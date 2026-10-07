# OxiZ 0.3.3: a `sat` model that violates the assertions

Found while building the svrand PoC (2026-10-07). Not reported upstream yet.

- `oxiz_bad_model_min.smt2`: four assertions; OxiZ answers `sat ((mid1 #x00000080))`, but `mid1 = 128`
  violates `(bvsle mid1 #x0000000a)`. Any value in 2..=10 is a model. Stable over repeated runs.
- `smt2run.rs`: the runner used (`oxiz::solver::Context::execute_script`), with
  `oxiz = { version = "=0.3.3", default-features = false, features = ["std"] }`.

A second problem seen at the same time (no minimal repro): after a series of `check_with_assumptions`,
a plain `check` on the same solver answered `unsat`, while a fresh solver given the same assertions
answered `sat`.
