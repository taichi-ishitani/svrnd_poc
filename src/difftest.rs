//! Differential test of the bit-blasted circuits against the evaluator:
//! random expressions over every operator, widths across the 64-bit
//! boundary, both signednesses. The variables are pinned by assumptions,
//! so the solver (not constant folding) computes the circuit's output.

use std::collections::HashMap;

use num_bigint::RandBigInt;
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;

use crate::NoFuncs;
use crate::bb::{Bb, Bv};
use crate::eval::{Env, Key};
use crate::ir::{BinOp, Expr, Problem, SetItem, UnOp, VarId};
use crate::lower::Enc;
use crate::value::Bits;

const WIDTHS: [u32; 15] = [1, 2, 3, 7, 8, 13, 31, 32, 33, 63, 64, 65, 100, 128, 129];

const BINOPS: [BinOp; 23] = [
    BinOp::Add,
    BinOp::Sub,
    BinOp::Mul,
    BinOp::Div,
    BinOp::Mod,
    BinOp::BitAnd,
    BinOp::BitOr,
    BinOp::BitXor,
    BinOp::BitXnor,
    BinOp::Shl,
    BinOp::Shr,
    BinOp::AShr,
    BinOp::Lt,
    BinOp::Le,
    BinOp::Gt,
    BinOp::Ge,
    BinOp::Eq,
    BinOp::Ne,
    BinOp::LogAnd,
    BinOp::LogOr,
    BinOp::Implies,
    BinOp::Equiv,
    BinOp::Add,
];

const UNOPS: [UnOp; 10] = [
    UnOp::Plus,
    UnOp::Neg,
    UnOp::BitNot,
    UnOp::LogNot,
    UnOp::RedAnd,
    UnOp::RedOr,
    UnOp::RedXor,
    UnOp::RedNand,
    UnOp::RedNor,
    UnOp::RedXnor,
];

struct Gen {
    rng: ChaCha8Rng,
    vars: Vec<VarId>,
}

impl Gen {
    fn konst(&mut self) -> Expr {
        let w = WIDTHS[self.rng.gen_range(0..WIDTHS.len())];
        let s = self.rng.r#gen();
        // Small values often, so comparisons and shifts are interesting.
        let v = if self.rng.gen_bool(0.5) {
            num_bigint::BigUint::from(self.rng.gen_range(0u32..20))
        } else {
            self.rng.gen_biguint(u64::from(w))
        };
        Expr::Const(Bits::new(w, s, v))
    }

    fn expr(&mut self, p: &Problem, depth: u32) -> Expr {
        if depth == 0 || self.rng.gen_bool(0.25) {
            return if self.rng.gen_bool(0.7) {
                Expr::Var(self.vars[self.rng.gen_range(0..self.vars.len())])
            } else {
                self.konst()
            };
        }
        let d = depth - 1;
        let b = |e: Expr| Box::new(e);
        match self.rng.gen_range(0..10) {
            0..=3 => {
                let op = BINOPS[self.rng.gen_range(0..BINOPS.len())];
                Expr::Binary(op, b(self.expr(p, d)), b(self.expr(p, d)))
            }
            4 => Expr::Unary(
                UNOPS[self.rng.gen_range(0..UNOPS.len())],
                b(self.expr(p, d)),
            ),
            5 => Expr::Cond(b(self.expr(p, d)), b(self.expr(p, d)), b(self.expr(p, d))),
            6 => {
                let n = self.rng.gen_range(1..4);
                Expr::Concat((0..n).map(|_| self.expr(p, d)).collect())
            }
            7 => {
                let base = self.expr(p, d);
                let w = p.ty(&base).w;
                if self.rng.gen_bool(0.5) {
                    let lsb = self.rng.gen_range(0..w);
                    let msb = self.rng.gen_range(lsb..w);
                    Expr::Slice {
                        base: b(base),
                        msb,
                        lsb,
                    }
                } else {
                    Expr::Bit {
                        base: b(base),
                        index: b(self.expr(p, d)),
                    }
                }
            }
            8 => {
                let w = WIDTHS[self.rng.gen_range(0..WIDTHS.len())];
                Expr::Cast {
                    width: w,
                    signed: self.rng.r#gen(),
                    expr: b(self.expr(p, d)),
                }
            }
            _ => {
                let x = self.expr(p, d);
                let set = (0..self.rng.gen_range(1..4))
                    .map(|_| {
                        if self.rng.gen_bool(0.5) {
                            SetItem::Value(self.expr(p, d))
                        } else {
                            SetItem::Range(self.expr(p, d), self.expr(p, d))
                        }
                    })
                    .collect();
                Expr::Inside(b(x), set)
            }
        }
    }
}

/// The literals that pin `bits` to `v`.
fn pins(bits: &[varisat::Lit], v: &num_bigint::BigUint) -> Vec<varisat::Lit> {
    bits.iter()
        .enumerate()
        .map(|(i, &l)| if v.bit(i as u64) { l } else { !l })
        .collect()
}

/// Run `cases` random expressions, `assigns` assignments each; returns the
/// first mismatch.
pub(crate) fn run(seed: u64, cases: usize, assigns: usize, depth: u32) -> Result<usize, String> {
    let mut p = Problem::new();
    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    let vars: Vec<VarId> = (0..4)
        .map(|i| {
            let w = WIDTHS[rng.gen_range(0..WIDTHS.len())];
            p.var(&format!("v{i}"), w, rng.r#gen())
        })
        .collect();
    let mut g = Gen {
        rng,
        vars: vars.clone(),
    };
    let mut checked = 0;
    for case in 0..cases {
        let e = g.expr(&p, depth);
        let ty = p.ty(&e);
        let mut funcs = NoFuncs;
        // One circuit per expression, shared by all assignments.
        let mut bb = Bb::new();
        let mut keys: HashMap<Key, Bv> = HashMap::new();
        let mut env = Env::new(&p, &mut funcs);
        let out = {
            let mut enc = Enc {
                p: &p,
                bb: &mut bb,
                env: &mut env,
                vars: &mut keys,
            };
            for v in &vars {
                enc.key_bits(Key::Var(v.0));
            }
            enc.bv(&e, ty).expect("lowerable")
        };
        for _ in 0..assigns {
            let mut assume = Vec::new();
            let mut fixed = HashMap::new();
            for v in &vars {
                let t = p.ty(&Expr::Var(*v));
                let x = if g.rng.gen_bool(0.3) {
                    num_bigint::BigUint::from(g.rng.gen_range(0u32..4))
                } else {
                    g.rng.gen_biguint(u64::from(t.w))
                };
                assume.extend(pins(&keys[&Key::Var(v.0)], &x));
                fixed.insert(Key::Var(v.0), Bits::new(t.w, t.s, x));
            }
            let mut funcs = NoFuncs;
            let mut ev = Env::new(&p, &mut funcs);
            ev.fixed = fixed.clone();
            let want = p.eval(&mut ev, &e, ty).expect("evaluable");
            if !bb.check(&assume) {
                return Err(format!(
                    "case {case}: circuit unsatisfiable under the assignment\n  {e:?}"
                ));
            }
            let got = bb.value_bv(&out);
            if got != want {
                return Err(format!(
                    "case {case}: circuit {got:#x}, evaluator {want:#x} (ctx {ty:?})\n  expr {e:?}\n  values {fixed:?}"
                ));
            }
            // The output is determined: no other value is possible.
            let differs = !bb.eq(&out, &bb.konst(&want, ty.w));
            let mut a2 = assume.clone();
            a2.push(differs);
            if bb.check(&a2) {
                return Err(format!(
                    "case {case}: output not determined by the inputs\n  {e:?}"
                ));
            }
            checked += 1;
        }
    }
    Ok(checked)
}

#[cfg(test)]
mod tests {
    #[test]
    fn circuits_match_the_evaluator() {
        for seed in 0..8 {
            match super::run(seed, 300, 4, 3) {
                Ok(n) => assert!(n > 0),
                Err(m) => panic!("seed {seed}: {m}"),
            }
        }
    }
}
