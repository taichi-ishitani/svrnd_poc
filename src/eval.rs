//! Concrete evaluation with the same typing rules the encoder uses: indices,
//! weights and call arguments during a solve, and an independent check of a
//! finished solution.

use std::collections::HashMap;

use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{One, Zero};

use crate::FuncEval;
use crate::ir::{BinOp, Expr, FuncId, Item, Problem, SetItem, UnOp};
use crate::types::{Ty, is_logical, is_relational, join};
use crate::value::{Bits, mask};

/// A solver variable: a scalar, an array element, or a dynamic array's size.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Key {
    Var(usize),
    Elem(usize, usize),
    Size(usize),
}

/// What is known while lowering or evaluating: values fixed so far, the
/// array sizes once they are settled, the indices of the enclosing
/// `foreach`es, and the caller's functions.
pub(crate) struct Env<'f> {
    pub fixed: HashMap<Key, Bits>,
    pub sizes: Vec<Option<usize>>,
    pub loops: HashMap<usize, i64>,
    pub funcs: &'f mut dyn FuncEval,
    calls: HashMap<(FuncId, Vec<Bits>), Bits>,
}

impl<'f> Env<'f> {
    pub fn new(p: &Problem, funcs: &'f mut dyn FuncEval) -> Self {
        let sizes = p
            .arrays
            .iter()
            .map(|a| match a.size {
                crate::ir::ArraySize::Fixed(n) => Some(n),
                crate::ir::ArraySize::Dynamic { .. } => None,
            })
            .collect();
        Env {
            fixed: HashMap::new(),
            sizes,
            loops: HashMap::new(),
            funcs,
            calls: HashMap::new(),
        }
    }

    pub fn call(&mut self, func: FuncId, args: Vec<Bits>) -> Bits {
        if let Some(v) = self.calls.get(&(func, args.clone())) {
            return v.clone();
        }
        let v = self.funcs.call(func, &args);
        self.calls.insert((func, args), v.clone());
        v
    }
}

/// Extend `v` (bits of a `from`-bit operand) to the context type: sign
/// extension only when the context is signed (§11.8.2).
pub(crate) fn ext(v: BigUint, from: u32, to: Ty) -> BigUint {
    if from >= to.w {
        return v & mask(to.w);
    }
    if to.s && v.bit(u64::from(from - 1)) {
        v | (mask(to.w) ^ mask(from))
    } else {
        v
    }
}

pub(crate) fn signed_of(v: &BigUint, w: u32) -> BigInt {
    let u = BigInt::from_biguint(Sign::Plus, v.clone());
    if v.bit(u64::from(w - 1)) {
        u - (BigInt::one() << w)
    } else {
        u
    }
}

fn wrap(v: BigInt, w: u32) -> BigUint {
    Bits::from_bigint(w, false, &v).bits().clone()
}

impl Problem {
    /// The value of `e` in the context type `ctx`; `None` when it depends on
    /// a variable that is not fixed yet.
    pub(crate) fn eval(&self, env: &mut Env, e: &Expr, ctx: Ty) -> Option<BigUint> {
        let own = self.ty(e);
        let leaf = |v: &Bits| ext(v.bits().clone(), v.width(), ctx);
        Some(match e {
            Expr::Const(b) => leaf(b),
            Expr::Var(v) => leaf(env.fixed.get(&Key::Var(v.0))?),
            Expr::Elem(a, i) => {
                let i = self.eval_index(env, i)?;
                leaf(env.fixed.get(&Key::Elem(a.0, i))?)
            }
            Expr::Size(a) => {
                let n = env.sizes[a.0]?;
                leaf(&Bits::from_u64(32, true, n as u64))
            }
            Expr::Loop(l) => leaf(&Bits::from_i64(32, true, *env.loops.get(&l.0)?)),
            Expr::Unary(op, a) => match op {
                UnOp::Plus => self.eval(env, a, ctx)?,
                UnOp::Neg => {
                    let v = self.eval(env, a, ctx)?;
                    wrap(-BigInt::from_biguint(Sign::Plus, v), ctx.w)
                }
                UnOp::BitNot => self.eval(env, a, ctx)? ^ mask(ctx.w),
                _ => {
                    let b = self.truth(env, e)?;
                    ext(BigUint::from(b as u8), 1, ctx)
                }
            },
            Expr::Binary(op, l, r) if is_relational(*op) || is_logical(*op) => {
                let b = self.truth(env, e)?;
                ext(BigUint::from(b as u8), 1, ctx)
            }
            Expr::Binary(op, l, r) => {
                let a = self.eval(env, l, ctx)?;
                match op {
                    BinOp::Shl | BinOp::Shr | BinOp::AShr => {
                        // §11.4.10: the amount is self-determined and unsigned.
                        let rt = self.ty(r);
                        let n = self.eval(env, r, Ty { w: rt.w, s: false })?;
                        let n: u64 = n.try_into().unwrap_or(u64::MAX);
                        let n = n.min(u64::from(ctx.w)) as usize;
                        match op {
                            BinOp::Shl => (a << n) & mask(ctx.w),
                            BinOp::Shr => a >> n,
                            _ if ctx.s => wrap(signed_of(&a, ctx.w) >> n, ctx.w),
                            _ => a >> n,
                        }
                    }
                    _ => {
                        let b = self.eval(env, r, ctx)?;
                        arith(*op, a, b, ctx)
                    }
                }
            }
            Expr::Cond(c, t, f) => {
                if self.truth(env, c)? {
                    self.eval(env, t, ctx)?
                } else {
                    self.eval(env, f, ctx)?
                }
            }
            Expr::Concat(es) => {
                let mut acc = BigUint::zero();
                for x in es {
                    let t = self.ty(x);
                    acc = (acc << t.w) | self.eval(env, x, t)?;
                }
                ext(acc, own.w, ctx)
            }
            Expr::Replicate(n, x) => {
                let t = self.ty(x);
                let v = self.eval(env, x, t)?;
                let mut acc = BigUint::zero();
                for _ in 0..*n {
                    acc = (acc << t.w) | &v;
                }
                ext(acc, own.w, ctx)
            }
            Expr::Slice { base, msb, lsb } => {
                let v = self.eval(env, base, self.ty(base))?;
                ext((v >> *lsb) & mask(msb - lsb + 1), own.w, ctx)
            }
            Expr::Bit { base, index } => {
                // The index reads as unsigned (a bit offset); an offset past
                // the operand selects 0 (two-state).
                let bt = self.ty(base);
                let v = self.eval(env, base, bt)?;
                let it = self.ty(index);
                let i = self.eval(env, index, Ty { w: it.w, s: false })?;
                let b = u64::try_from(&i).is_ok_and(|i| i < u64::from(bt.w) && v.bit(i));
                ext(BigUint::from(b as u8), 1, ctx)
            }
            Expr::Cast { width, expr, .. } => {
                let it = self.ty(expr);
                let v = self.eval(
                    env,
                    expr,
                    Ty {
                        w: (*width).max(it.w),
                        s: it.s,
                    },
                )?;
                ext(v & mask(*width), *width, ctx)
            }
            Expr::Inside(..) => {
                let b = self.truth(env, e)?;
                ext(BigUint::from(b as u8), 1, ctx)
            }
            Expr::Call { func, args, .. } => {
                let v = self.eval_call(env, *func, args)?;
                leaf(&v)
            }
        })
    }

    pub(crate) fn eval_call(&self, env: &mut Env, func: FuncId, args: &[Expr]) -> Option<Bits> {
        let mut vals = Vec::with_capacity(args.len());
        for a in args {
            let t = self.ty(a);
            vals.push(Bits::new(t.w, t.s, self.eval(env, a, t)?));
        }
        Some(env.call(func, vals))
    }

    /// The value of a self-determined operand as a signed integer.
    pub(crate) fn eval_int(&self, env: &mut Env, e: &Expr) -> Option<BigInt> {
        let t = self.ty(e);
        let v = self.eval(env, e, t)?;
        Some(if t.s {
            signed_of(&v, t.w)
        } else {
            BigInt::from_biguint(Sign::Plus, v)
        })
    }

    pub(crate) fn eval_index(&self, env: &mut Env, e: &Expr) -> Option<usize> {
        usize::try_from(self.eval_int(env, e)?).ok()
    }

    /// The truth of `e` as a condition (non-zero).
    pub(crate) fn truth(&self, env: &mut Env, e: &Expr) -> Option<bool> {
        Some(match e {
            Expr::Binary(op, l, r) if is_relational(*op) => {
                let c = join(self.ty(l), self.ty(r));
                let a = self.eval(env, l, c)?;
                let b = self.eval(env, r, c)?;
                compare(*op, &a, &b, c)
            }
            Expr::Binary(op, l, r) if is_logical(*op) => {
                let a = self.truth(env, l)?;
                match op {
                    BinOp::LogAnd => a && self.truth(env, r)?,
                    BinOp::LogOr => a || self.truth(env, r)?,
                    BinOp::Implies => !a || self.truth(env, r)?,
                    _ => a == self.truth(env, r)?,
                }
            }
            Expr::Unary(UnOp::LogNot, a) => !self.truth(env, a)?,
            Expr::Unary(
                op @ (UnOp::RedAnd
                | UnOp::RedOr
                | UnOp::RedXor
                | UnOp::RedNand
                | UnOp::RedNor
                | UnOp::RedXnor),
                a,
            ) => {
                let t = self.ty(a);
                let v = self.eval(env, a, t)?;
                match op {
                    UnOp::RedAnd => v == mask(t.w),
                    UnOp::RedOr => !v.is_zero(),
                    UnOp::RedXor => v.count_ones() % 2 == 1,
                    UnOp::RedNand => v != mask(t.w),
                    UnOp::RedNor => v.is_zero(),
                    _ => v.count_ones() % 2 == 0,
                }
            }
            Expr::Inside(x, set) => {
                for s in set {
                    if self.in_set(env, x, s)? {
                        return Some(true);
                    }
                }
                false
            }
            _ => {
                let t = self.ty(e);
                !self.eval(env, e, t)?.is_zero()
            }
        })
    }

    /// §11.4.13: `x` matches a value by `==`, a range by `>=` and `<=`.
    pub(crate) fn in_set(&self, env: &mut Env, x: &Expr, s: &SetItem) -> Option<bool> {
        let rel = |me: &Self, env: &mut Env, op, a: &Expr, b: &Expr| {
            me.truth(
                env,
                &Expr::Binary(op, Box::new(a.clone()), Box::new(b.clone())),
            )
        };
        Some(match s {
            SetItem::Value(v) => rel(self, env, BinOp::Eq, x, v)?,
            SetItem::Range(lo, hi) => {
                rel(self, env, BinOp::Ge, x, lo)? && rel(self, env, BinOp::Le, x, hi)?
            }
        })
    }

    /// Whether a hard item holds (soft items are ignored).
    pub(crate) fn item_holds(&self, env: &mut Env, it: &Item) -> Option<bool> {
        Some(match it {
            Item::Expr(e) => self.truth(env, e)?,
            Item::Implies(c, body) => !self.truth(env, c)? || self.items_hold(env, body)?,
            Item::IfElse(c, t, f) => {
                if self.truth(env, c)? {
                    self.items_hold(env, t)?
                } else {
                    self.items_hold(env, f)?
                }
            }
            Item::Dist(x, items) => {
                let mut any = false;
                for d in items {
                    if self.in_set(env, x, &d.item)? && self.dist_weight_nonzero(env, d)? {
                        any = true;
                        break;
                    }
                }
                any
            }
            Item::Foreach(a, l, body) => {
                let n = env.sizes[a.0]?;
                for i in 0..n {
                    env.loops.insert(l.0, i as i64);
                    if !self.items_hold(env, body)? {
                        env.loops.remove(&l.0);
                        return Some(false);
                    }
                }
                env.loops.remove(&l.0);
                true
            }
            Item::Unique(es) => {
                let mut c = self.ty(&es[0]);
                for e in es {
                    c = join(c, self.ty(e));
                }
                let mut seen = std::collections::HashSet::new();
                for e in es {
                    if !seen.insert(self.eval(env, e, c)?) {
                        return Some(false);
                    }
                }
                true
            }
            Item::Soft(_) => true,
        })
    }

    pub(crate) fn items_hold(&self, env: &mut Env, items: &[Item]) -> Option<bool> {
        for it in items {
            if !self.item_holds(env, it)? {
                return Some(false);
            }
        }
        Some(true)
    }

    pub(crate) fn dist_weight_nonzero(
        &self,
        env: &mut Env,
        d: &crate::ir::DistItem,
    ) -> Option<bool> {
        Some(match &d.weight {
            None => true,
            Some(crate::ir::Weight::Each(w) | crate::ir::Weight::Spread(w)) => {
                self.eval_int(env, w)? > BigInt::zero()
            }
        })
    }
}

fn compare(op: BinOp, a: &BigUint, b: &BigUint, c: Ty) -> bool {
    let ord = if c.s {
        signed_of(a, c.w).cmp(&signed_of(b, c.w))
    } else {
        a.cmp(b)
    };
    match op {
        BinOp::Lt => ord.is_lt(),
        BinOp::Le => ord.is_le(),
        BinOp::Gt => ord.is_gt(),
        BinOp::Ge => ord.is_ge(),
        BinOp::Eq => ord.is_eq(),
        _ => ord.is_ne(),
    }
}

/// The arithmetic and bitwise operators. Division by zero follows the
/// SMT-LIB bit-vector semantics the encoder uses (SystemVerilog yields X).
fn arith(op: BinOp, a: BigUint, b: BigUint, c: Ty) -> BigUint {
    let m = mask(c.w);
    match op {
        BinOp::Add => (a + b) & m,
        BinOp::Sub => ((a + (BigUint::one() << c.w)) - b) & m,
        BinOp::Mul => (a * b) & m,
        BinOp::BitAnd => a & b,
        BinOp::BitOr => a | b,
        BinOp::BitXor => a ^ b,
        BinOp::BitXnor => (a ^ b) ^ m,
        BinOp::Div | BinOp::Mod if c.s => {
            let (x, y) = (signed_of(&a, c.w), signed_of(&b, c.w));
            if y.is_zero() {
                return if op == BinOp::Mod {
                    a
                } else if x >= BigInt::zero() {
                    m
                } else {
                    BigUint::one()
                };
            }
            // Truncating division; the remainder takes the dividend's sign.
            wrap(if op == BinOp::Div { &x / &y } else { &x % &y }, c.w)
        }
        BinOp::Div => {
            if b.is_zero() {
                m
            } else {
                a / b
            }
        }
        BinOp::Mod => {
            if b.is_zero() {
                a
            } else {
                a % b
            }
        }
        _ => unreachable!("{op:?} is not arithmetic"),
    }
}
