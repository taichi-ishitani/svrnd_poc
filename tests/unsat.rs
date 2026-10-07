//! §18.6.1: `randomize()` returns 0 when the constraints cannot all hold.
//! Each problem here has no solution; `solve` must say so through every
//! path — the solver, a variable decided by its domain alone, a `Fun`, a
//! `dist`, the array-size stage and the call-argument stage — and a soft
//! conflict must never make a solvable problem fail.

use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use svrand::build::*;
use svrand::{ArraySize, BinOp::*, Bits, FuncEval, FuncId, NoFuncs, Problem, SolveError};

fn rng() -> ChaCha8Rng {
    ChaCha8Rng::seed_from_u64(1)
}

fn unsat(p: &Problem, funcs: &mut dyn FuncEval) {
    for seed in 0..5 {
        let mut r = ChaCha8Rng::seed_from_u64(seed);
        match p.solve(&mut r, funcs) {
            Err(SolveError::Unsat) => {}
            Err(e) => panic!("expected Unsat, got {e:?}"),
            Ok((sol, _)) => panic!(
                "expected Unsat, got a solution (verify: {:?})",
                p.verify(&sol, funcs)
            ),
        }
    }
}

fn sat(p: &Problem, funcs: &mut dyn FuncEval) {
    let (sol, _) = p.solve(&mut rng(), funcs).expect("satisfiable");
    p.verify(&sol, funcs).expect("a valid solution");
}

/// Two variables, so the items reach the solver.
#[test]
fn contradiction_in_the_solver() {
    let mut p = Problem::new();
    let x = p.var("x", 32, true);
    let y = p.var("y", 32, true);
    p.constraint(
        0,
        vec![item(bin(Lt, var(x), var(y))), item(bin(Lt, var(y), var(x)))],
    );
    unsat(&p, &mut NoFuncs);
}

/// Bounds by constants only: decided by the domain, outside the solver.
#[test]
fn empty_domain() {
    let mut p = Problem::new();
    let x = p.var("x", 32, true);
    p.constraint(
        0,
        vec![
            item(bin(Lt, var(x), int(5))),
            item(bin(Gt, var(x), int(10))),
        ],
    );
    unsat(&p, &mut NoFuncs);
}

/// A wide variable: `(x >> 8) == 0` and `x[9]` set.
#[test]
fn wide_variable() {
    let mut p = Problem::new();
    let x = p.var("x", 1024, false);
    p.constraint(
        0,
        vec![
            item(bin(Eq, bin(Shr, var(x), int(8)), int(0))),
            item(bin(
                Eq,
                svrand::Expr::Slice {
                    base: Box::new(var(x)),
                    msb: 9,
                    lsb: 9,
                },
                c(1, false, 1),
            )),
        ],
    );
    unsat(&p, &mut NoFuncs);
}

/// The same, on the elements of a dynamic array (domain-only path).
#[test]
fn wide_array_elements() {
    let mut p = Problem::new();
    let a = p.array("a", 128, false, ArraySize::Dynamic { max: 8 });
    let i = p.loop_var();
    p.constraint(
        0,
        vec![
            item(bin(Eq, size(a), int(4))),
            foreach(
                a,
                i,
                vec![
                    item(bin(Eq, bin(Shr, elem(a, lp(i)), int(8)), int(0))),
                    item(bin(Gt, elem(a, lp(i)), int(300))),
                ],
            ),
        ],
    );
    unsat(&p, &mut NoFuncs);
}

/// `x == y / 8` (a `Fun`) against a bound on `x`.
#[test]
fn fun_against_a_bound() {
    let mut p = Problem::new();
    let x = p.var("x", 32, true);
    let y = p.var("y", 32, true);
    p.constraint(
        0,
        vec![
            item(bin(Eq, var(y), int(64))),
            item(bin(Eq, var(x), bin(Div, var(y), int(8)))),
            item(bin(Ne, var(x), int(8))),
        ],
    );
    unsat(&p, &mut NoFuncs);
}

/// Every `dist` item has weight 0: no value is allowed (§18.5.4).
#[test]
fn dist_with_zero_weights() {
    let mut p = Problem::new();
    let x = p.var("x", 32, true);
    p.constraint(
        0,
        vec![dist(
            var(x),
            vec![
                each(val(int(0)), int(0)),
                spread(range(int(1), int(9)), int(0)),
            ],
        )],
    );
    unsat(&p, &mut NoFuncs);
}

/// A `dist` whose items the other constraints all rule out.
#[test]
fn dist_ruled_out() {
    let mut p = Problem::new();
    let x = p.var("x", 32, true);
    let y = p.var("y", 32, true);
    p.constraint(
        0,
        vec![
            dist(
                var(x),
                vec![
                    each(val(int(0)), int(6)),
                    spread(range(int(1), int(3)), int(3)),
                ],
            ),
            item(bin(Gt, var(x), var(y))),
            item(bin(Ge, var(y), int(3))),
        ],
    );
    unsat(&p, &mut NoFuncs);
}

/// Conflicting sizes of a dynamic array (the size stage).
#[test]
fn array_size_conflict() {
    let mut p = Problem::new();
    let a = p.array("a", 8, false, ArraySize::Dynamic { max: 16 });
    let n = p.var("n", 32, true);
    p.constraint(
        0,
        vec![
            item(bin(Eq, size(a), var(n))),
            item(bin(Eq, var(n), int(5))),
            item(bin(Eq, size(a), int(6))),
        ],
    );
    unsat(&p, &mut NoFuncs);
}

/// A size beyond the array's bound.
#[test]
fn array_size_beyond_bound() {
    let mut p = Problem::new();
    let a = p.array("a", 8, false, ArraySize::Dynamic { max: 16 });
    p.constraint(0, vec![item(bin(Eq, size(a), int(17)))]);
    unsat(&p, &mut NoFuncs);
}

/// Elements that cannot meet their constraints once sized.
#[test]
fn elements_unsat_after_sizing() {
    let mut p = Problem::new();
    let a = p.array("a", 8, false, ArraySize::Dynamic { max: 16 });
    let i = p.loop_var();
    p.constraint(
        0,
        vec![
            item(bin(Eq, size(a), int(3))),
            foreach(a, i, vec![item(bin(Lt, elem(a, lp(i)), elem(a, int(0))))]),
        ],
    );
    unsat(&p, &mut NoFuncs);
}

struct Ident;
impl FuncEval for Ident {
    fn call(&mut self, _: FuncId, a: &[Bits]) -> Bits {
        a[0].clone()
    }
}

/// A function of a rand argument (§18.5.12): unsat once the call is
/// evaluated.
#[test]
fn call_argument_stage() {
    let mut p = Problem::new();
    let x = p.var("x", 32, true);
    let y = p.var("y", 32, true);
    p.constraint(
        0,
        vec![
            item(bin(Eq, var(x), int(3))),
            item(bin(Eq, var(y), call(FuncId(0), 32, true, vec![var(x)]))),
            item(bin(Gt, var(y), int(3))),
        ],
    );
    unsat(&p, &mut Ident);
}

/// `unique` over more values than the domain holds.
#[test]
fn unique_pigeonhole() {
    let mut p = Problem::new();
    let xs: Vec<_> = (0..3).map(|i| p.var(&format!("x{i}"), 32, true)).collect();
    let mut items: Vec<_> = xs
        .iter()
        .map(|&x| item(inside(var(x), vec![range(int(0), int(1))])))
        .collect();
    items.push(svrand::Item::Unique(xs.iter().map(|&x| var(x)).collect()));
    p.constraint(0, items);
    unsat(&p, &mut NoFuncs);
}

/// Soft items that conflict with a hard one, or with each other, are
/// dropped: the problem stays solvable (§18.5.14).
#[test]
fn soft_conflicts_never_fail() {
    let mut p = Problem::new();
    let x = p.var("x", 32, true);
    p.constraint(0, vec![item(bin(Gt, var(x), int(10)))]);
    p.constraint(1, vec![soft(item(bin(Eq, var(x), int(5))))]);
    p.constraint(
        2,
        vec![
            soft(item(bin(Eq, var(x), int(20)))),
            soft(item(bin(Eq, var(x), int(30)))),
        ],
    );
    sat(&p, &mut NoFuncs);
    let (sol, _) = p.solve(&mut rng(), &mut NoFuncs).unwrap();
    // The later soft item wins its conflict with the earlier one.
    assert_eq!(sol.var(x).to_i64(), Some(30));
}

/// §18.5.12: the argument is solved first, without the item that calls the
/// function, so a draw the call then rules out fails the whole call — the
/// ordering the LRM imposes, not a solver error. Reports how often.
#[test]
fn call_argument_ordering_can_fail() {
    let mut p = Problem::new();
    let x = p.var("x", 32, true);
    let y = p.var("y", 32, true);
    p.constraint(
        0,
        vec![
            item(inside(var(x), vec![range(int(0), int(10))])),
            item(bin(Eq, var(y), call(FuncId(0), 32, true, vec![var(x)]))),
            item(bin(Gt, var(y), int(8))),
        ],
    );
    let (mut ok, mut fail) = (0, 0);
    for seed in 0..200 {
        let mut r = ChaCha8Rng::seed_from_u64(seed);
        match p.solve(&mut r, &mut Ident) {
            Ok((sol, _)) => {
                p.verify(&sol, &mut Ident).unwrap();
                ok += 1;
            }
            Err(SolveError::Unsat) => fail += 1,
            Err(e) => panic!("{e:?}"),
        }
    }
    println!("call ordering: {ok} solved, {fail} failed of 200");
    assert!(ok > 0);
}
