# svrand — a proof of concept

SystemVerilog constrained randomization (`randomize()`, `std::randomize()`) for rand variables of
**any width**, by bit-blasting the constraints onto a SAT solver ([varisat](https://crates.io/crates/varisat)).

It is a PoC for the [xezim](https://github.com/aionhw/xezim) simulator. xezim's constraint solver holds
values in `i128` / `u64`, so constraints on a rand variable wider than 64 bits (a shift, a multi-bit
part-select, `x + 1 == K`) are not solved there
([aionhw/xezim#261](https://github.com/aionhw/xezim/issues/261)).

## How it works

The caller (a simulator) lowers one `randomize()` call into a `Problem` and calls `Problem::solve`.

- **Problem** (`src/ir.rs`): rand variables and arrays with their width and signedness, and constraint
  blocks with SystemVerilog's operators and items (`if`/`else`, `->`, `inside`, `dist`, `foreach`,
  `unique`, `soft`, `solve ... before`, function calls). The caller passes state operands as constants,
  leaves `rand_mode(0)` members and disabled blocks out, flattens rand sub-objects into the problem
  (`axi_cfg[0].request_start_delay.min_delay`), and gives each block its soft priority (§18.5.14.1).
- **Typing** (`src/types.rs`): the self-determined type of an expression (§11.6, §11.8.1).
- **Lowering** (`src/lower.rs`): expressions to circuits, with the context-determined widths and the
  sign extension of §11.6 / §11.8.2.
- **Bit-blasting** (`src/bb.rs`): Tseitin gates with constant folding and structural hashing; adders,
  comparators, barrel shifters, multipliers, restoring dividers; CNF into varisat.
- **Evaluator** (`src/eval.rs`): the same typing rules on concrete values, for indices, weights and
  call arguments during a solve, and for an independent check of every solution (`Problem::verify`).
- **Solving** (`src/solve.rs`, `src/domain.rs`), after xezim's interval CSP:
  - stages: the rand arguments of called functions first (§18.5.12), then the sizes of dynamic arrays
    (§18.5.8.1), then everything else;
  - interval domains from the items that bound one variable by constants; a variable whose items all
    are such bounds is drawn from its domain (and its `dist`) without the solver;
  - soft items tried all at once, and one by one from the highest rank only on a conflict (§18.5.14);
  - `x == f(others)` with a division, remainder or product of variables computed once the others are
    fixed;
  - variables fixed in `solve ... before` order (§18.5.10), smallest domain first, drawn from their
    domain or `dist` (§18.5.4); a run of variables is drawn together and checked once by assuming their
    bits, and split on a conflict.

```rust
use svrand::build::*;
use svrand::{BinOp::*, NoFuncs, Problem};

let mut p = Problem::new();
let x = p.var("x", 32, false);
let y = p.var("y", 65, false); // wider than 64 bits
p.constraint(0, vec![item(bin(Eq, bin(Shr, var(x), int(8)), int(0)))]);
let (sol, _stats) = p.solve(&mut rng, &mut NoFuncs)?;
assert!(sol.var(x).to_i64().unwrap() < 256);
```

## Running

```sh
cargo test --release                   # differential test of the circuits, unsat tests
cargo run --release --bin tvip -- all 50 1
```

`tvip` writes down the constraints of the [tvip-axi](https://github.com/taichi-ishitani/tvip-axi) VIP
with this API, solves each case N times, and checks every solution with the evaluator.
Modes: `item`, `delay`, `config`, `sample`, `slave`, `stdrand`, `all`; then N and a seed.

## Results

Release build; every solution passed `Problem::verify`.

| Case | Verified | Time / solve |
|---|---|---|
| `tvip_axi_master_item` (write; `data[]` 1024-bit, `strobe[]` 128-bit, up to 256 elements) | 100/100 | 21 ms (max 26 ms) |
| `tvip_axi_slave_item` (read / write) | 50/50 each | 1 ms |
| `tvip_delay_configuration` (function calls, soft, `solve ... before`) | 50/50 | 1 ms |
| `tvip_axi_configuration` (with its nine delay members) | 50/50 | 56 ms |
| `tvip_axi_sample_configuration` (two configurations, 18 delay members, flattened) | 50/50 | 170–250 ms |
| `std::randomize` in the slave driver | 500/500 each | < 1 ms |

Distributions follow the constraints, e.g. the delay `dist {0 := 6, [1:3] :/ 3, [6:10] :/ 1}` comes out
59.8 : 30.3 : 9.9, and the response `dist` 6 : 2 : 1 : 1 comes out 62.6 : 18.5 : 9.8 : 9.1.

Tests:

- `src/difftest.rs`: random expressions over every operator, widths 1..129, both signednesses; the
  circuit's output (inputs pinned by assumptions) equals the evaluator's, and is the only possible
  output. Five deliberate bugs in the circuits were all caught.
- `tests/unsat.rs`: unsatisfiable problems return `SolveError::Unsat` through every path (the solver,
  a domain-only variable, a `Fun`, a `dist`, the size stage, the call-argument stage, `unique`); soft
  conflicts never fail a solvable problem; and the call-argument ordering of §18.5.12 can fail a
  problem a joint solve would satisfy, as the LRM specifies.

## Findings

- **OxiZ** (a pure-Rust SMT solver) was tried first and dropped: version 0.3.3 returned `sat` models
  that violate the assertions, and wrong `unsat` answers after `check_with_assumptions`. See
  [`notes/oxiz-0.3.3`](notes/oxiz-0.3.3) for a minimal reproduction.
- **varisat** is unmaintained since 2022 but feature-complete; Cargo's resolver tests use it as the
  reference solver, with assumptions, the same way this PoC does. A SAT model is easy to check, and
  every solution is checked against the evaluator anyway.
- The speed comes from xezim's CSP ideas, not from the SAT solver: domains, drawing from them, batching,
  and keeping domain-only variables out of the solver took the master item from seconds to ~20 ms.

## Limitations

- The circuits and the evaluator share the typing rules, so an error in those rules is not caught by
  the differential test.
- Not yet checked against xezim's own randomization tests (the next step).
- Value selection is not uniform over the solutions (neither is xezim's): a variable is drawn from its
  own domain, then fixed.
- `tvip_axi_master_access_sequence` is not written down (its constraints match the item's).
