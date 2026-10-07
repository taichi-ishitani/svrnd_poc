//! Lowering to bit-blasted circuits (`bb`) with the §11.6 / §11.8 rules.
//!
//! An item that cannot be lowered yet (a call whose rand arguments are not
//! fixed, an element of an array whose size is not settled) yields `None` and
//! is deferred to a later stage.

use std::collections::HashMap;

use num_bigint::{BigInt, BigUint};
use num_traits::ToPrimitive;
use varisat::Lit;

use crate::bb::{Bb, Bv};
use crate::eval::{Env, Key};
use crate::ir::{BinOp, DistItem, Expr, Item, Problem, SetItem, UnOp, Weight};
use crate::types::{Ty, is_logical, is_relational, join};
use crate::value::{Bits, mask};

/// A `dist` whose items are constants once lowered: the variable it draws,
/// the guard it sits under, and `(lo, hi, total weight)` per item.
pub(crate) struct DistSpec {
    pub key: Key,
    pub guard: Lit,
    pub items: Vec<(BigInt, BigInt, f64)>,
}

/// A soft item: its rank, its literal, and the domain it gives a variable
/// when it is an unconditional bound.
pub(crate) struct Soft {
    pub rank: (u32, u32),
    pub lit: Lit,
    pub bound: Option<(Key, crate::domain::Dom)>,
}

pub(crate) struct Enc<'a, 'f> {
    pub p: &'a Problem,
    pub bb: &'a mut Bb,
    pub env: &'a mut Env<'f>,
    pub vars: &'a mut HashMap<Key, Bv>,
}

impl Enc<'_, '_> {
    pub fn key_ty(&self, k: Key) -> Ty {
        self.p.key_ty(k)
    }

    /// The bits of `k`, created on first use.
    pub fn key_bits(&mut self, k: Key) -> Bv {
        if let Some(v) = self.vars.get(&k) {
            return v.clone();
        }
        let v = self.bb.fresh_bv(self.key_ty(k).w);
        self.vars.insert(k, v.clone());
        v
    }

    pub fn konst(&self, v: &BigUint, w: u32) -> Bv {
        self.bb.konst(&(v & mask(w)), w)
    }

    /// A leaf: its fixed value when known, else its bits.
    fn leaf(&mut self, k: Key, ctx: Ty) -> Bv {
        let own = self.key_ty(k);
        let v = match self.env.fixed.get(&k).cloned() {
            Some(b) => self.konst(b.bits(), own.w),
            None => self.key_bits(k),
        };
        self.bb.ext(&v, ctx.w, ctx.s)
    }

    fn bool_bv(&mut self, b: Lit, ctx: Ty) -> Bv {
        // A 1-bit unsigned result: zero-extended whatever the context.
        self.bb.ext(&[b], ctx.w, false)
    }

    /// `e` as a `ctx.w`-bit vector.
    pub fn bv(&mut self, e: &Expr, ctx: Ty) -> Option<Bv> {
        let p = self.p;
        Some(match e {
            Expr::Const(b) => {
                let v = crate::eval::ext(b.bits().clone(), b.width(), ctx);
                self.konst(&v, ctx.w)
            }
            Expr::Var(v) => self.leaf(Key::Var(v.0), ctx),
            Expr::Elem(a, i) => {
                let i = p.eval_index(self.env, i)?;
                if i >= self.env.sizes[a.0]? {
                    return None;
                }
                self.leaf(Key::Elem(a.0, i), ctx)
            }
            Expr::Size(a) => match self.env.sizes[a.0] {
                Some(n) => {
                    let v = crate::eval::ext(BigUint::from(n), 32, ctx);
                    self.konst(&v, ctx.w)
                }
                None => self.leaf(Key::Size(a.0), ctx),
            },
            Expr::Loop(l) => {
                let v = *self.env.loops.get(&l.0)?;
                let b = Bits::from_i64(32, true, v);
                let v = crate::eval::ext(b.bits().clone(), 32, ctx);
                self.konst(&v, ctx.w)
            }
            Expr::Unary(UnOp::Plus, a) => self.bv(a, ctx)?,
            Expr::Unary(UnOp::Neg, a) => {
                let t = self.bv(a, ctx)?;
                self.bb.neg(&t)
            }
            Expr::Unary(UnOp::BitNot, a) => {
                let t = self.bv(a, ctx)?;
                self.bb.not_bv(&t)
            }
            Expr::Unary(..) | Expr::Inside(..) => {
                let b = self.boolean(e)?;
                self.bool_bv(b, ctx)
            }
            Expr::Binary(op, ..) if is_relational(*op) || is_logical(*op) => {
                let b = self.boolean(e)?;
                self.bool_bv(b, ctx)
            }
            Expr::Binary(op @ (BinOp::Shl | BinOp::Shr | BinOp::AShr), l, r) => {
                // The amount is self-determined and unsigned (§11.4.10).
                let rt = p.ty(r);
                let a = self.bv(l, ctx)?;
                let n = self.bv(r, Ty { w: rt.w, s: false })?;
                let kind = match op {
                    BinOp::Shl => 0,
                    BinOp::AShr if ctx.s => 2,
                    _ => 1,
                };
                self.bb.shift(&a, &n, kind)
            }
            Expr::Binary(op, l, r) => {
                let a = self.bv(l, ctx)?;
                let b = self.bv(r, ctx)?;
                let bb = &mut *self.bb;
                match op {
                    BinOp::Add => bb.add(&a, &b),
                    BinOp::Sub => bb.sub(&a, &b),
                    BinOp::Mul => bb.mul(&a, &b),
                    BinOp::Div if ctx.s => bb.sdivrem(&a, &b).0,
                    BinOp::Div => bb.udivrem(&a, &b).0,
                    BinOp::Mod if ctx.s => bb.sdivrem(&a, &b).1,
                    BinOp::Mod => bb.udivrem(&a, &b).1,
                    BinOp::BitAnd => bb.zip(&a, &b, Bb::and),
                    BinOp::BitOr => bb.zip(&a, &b, Bb::or),
                    BinOp::BitXor => bb.zip(&a, &b, Bb::xor),
                    BinOp::BitXnor => {
                        let x = bb.zip(&a, &b, Bb::xor);
                        bb.not_bv(&x)
                    }
                    _ => unreachable!(),
                }
            }
            Expr::Cond(c, t, f) => {
                let c = self.boolean(c)?;
                let t = self.bv(t, ctx)?;
                let f = self.bv(f, ctx)?;
                self.bb.ite_bv(c, &t, &f)
            }
            Expr::Concat(es) => {
                // The first operand is the most significant.
                let mut v: Bv = Vec::new();
                for x in es.iter().rev() {
                    let t = p.ty(x);
                    v.extend(self.bv(x, t)?);
                }
                self.bb.ext(&v, ctx.w, false)
            }
            Expr::Replicate(n, x) => {
                let t = p.ty(x);
                let one = self.bv(x, t)?;
                let v: Bv = (0..*n).flat_map(|_| one.iter().copied()).collect();
                self.bb.ext(&v, ctx.w, false)
            }
            Expr::Slice { base, msb, lsb } => {
                let v = self.bv(base, p.ty(base))?;
                let s = v[*lsb as usize..=*msb as usize].to_vec();
                self.bb.ext(&s, ctx.w, false)
            }
            Expr::Bit { base, index } => {
                let bt = p.ty(base);
                let it = p.ty(index);
                let v = self.bv(base, bt)?;
                let i = self.bv(index, Ty { w: it.w, s: false })?;
                let sh = self.bb.shift(&v, &i, 1);
                self.bool_bv(sh[0], ctx)
            }
            Expr::Cast { width, expr, .. } => {
                let it = p.ty(expr);
                let v = self.bv(
                    expr,
                    Ty {
                        w: (*width).max(it.w),
                        s: it.s,
                    },
                )?;
                let v = v[..*width as usize].to_vec();
                self.bb.ext(&v, ctx.w, ctx.s)
            }
            Expr::Call { func, args, .. } => {
                let v = p.eval_call(self.env, *func, args)?;
                let x = crate::eval::ext(v.bits().clone(), v.width(), ctx);
                self.konst(&x, ctx.w)
            }
        })
    }

    /// `e` as a condition (non-zero).
    pub fn boolean(&mut self, e: &Expr) -> Option<Lit> {
        let p = self.p;
        Some(match e {
            Expr::Binary(op, l, r) if is_relational(*op) => {
                let c = join(p.ty(l), p.ty(r));
                let a = self.bv(l, c)?;
                let b = self.bv(r, c)?;
                let bb = &mut *self.bb;
                match (op, c.s) {
                    (BinOp::Lt, true) => bb.slt(&a, &b),
                    (BinOp::Lt, false) => bb.ult(&a, &b),
                    (BinOp::Le, true) => bb.sle(&a, &b),
                    (BinOp::Le, false) => bb.ule(&a, &b),
                    (BinOp::Gt, true) => bb.slt(&b, &a),
                    (BinOp::Gt, false) => bb.ult(&b, &a),
                    (BinOp::Ge, true) => bb.sle(&b, &a),
                    (BinOp::Ge, false) => bb.ule(&b, &a),
                    (BinOp::Eq, _) => bb.eq(&a, &b),
                    _ => !bb.eq(&a, &b),
                }
            }
            Expr::Binary(op, l, r) if is_logical(*op) => {
                let a = self.boolean(l)?;
                let b = self.boolean(r)?;
                match op {
                    BinOp::LogAnd => self.bb.and(a, b),
                    BinOp::LogOr => self.bb.or(a, b),
                    BinOp::Implies => self.bb.implies(a, b),
                    _ => !self.bb.xor(a, b),
                }
            }
            Expr::Unary(UnOp::LogNot, a) => !self.boolean(a)?,
            Expr::Unary(
                op @ (UnOp::RedAnd
                | UnOp::RedOr
                | UnOp::RedXor
                | UnOp::RedNand
                | UnOp::RedNor
                | UnOp::RedXnor),
                a,
            ) => {
                let t = p.ty(a);
                let v = self.bv(a, t)?;
                let r = match op {
                    UnOp::RedAnd | UnOp::RedNand => self.bb.and_all(v),
                    UnOp::RedOr | UnOp::RedNor => self.bb.or_all(v),
                    _ => {
                        let mut x = self.bb.fls();
                        for l in v {
                            x = self.bb.xor(x, l);
                        }
                        x
                    }
                };
                if matches!(op, UnOp::RedNand | UnOp::RedNor | UnOp::RedXnor) {
                    !r
                } else {
                    r
                }
            }
            Expr::Inside(x, set) => {
                let mut ors = Vec::with_capacity(set.len());
                for s in set {
                    ors.push(self.in_set(x, s)?);
                }
                self.bb.or_all(ors)
            }
            _ => {
                let t = p.ty(e);
                let v = self.bv(e, t)?;
                self.bb.or_all(v)
            }
        })
    }

    pub fn in_set(&mut self, x: &Expr, s: &SetItem) -> Option<Lit> {
        let rel = |me: &mut Self, op, a: &Expr, b: &Expr| {
            me.boolean(&Expr::Binary(op, Box::new(a.clone()), Box::new(b.clone())))
        };
        Some(match s {
            SetItem::Value(v) => rel(self, BinOp::Eq, x, v)?,
            SetItem::Range(lo, hi) => {
                let a = rel(self, BinOp::Ge, x, lo)?;
                let b = rel(self, BinOp::Le, x, hi)?;
                self.bb.and(a, b)
            }
        })
    }

    /// Lower the hard part of `items` under `guard`; soft items go to `soft`
    /// as `guard -> item` with their rank, `dist`s with constant items to
    /// `dists`.
    pub fn items(
        &mut self,
        items: &[Item],
        guard: Lit,
        rank: &mut (u32, u32),
        soft: &mut Vec<Soft>,
        dists: &mut Vec<DistSpec>,
    ) -> Option<Lit> {
        let mut hard = Vec::with_capacity(items.len());
        for it in items {
            hard.push(self.item(it, guard, rank, soft, dists)?);
        }
        Some(self.bb.and_all(hard))
    }

    fn item(
        &mut self,
        it: &Item,
        guard: Lit,
        rank: &mut (u32, u32),
        soft: &mut Vec<Soft>,
        dists: &mut Vec<DistSpec>,
    ) -> Option<Lit> {
        let p = self.p;
        Some(match it {
            Item::Expr(e) => self.boolean(e)?,
            Item::Implies(c, body) => {
                let c = self.boolean(c)?;
                let g = self.bb.and(guard, c);
                let b = self.items(body, g, rank, soft, dists)?;
                self.bb.implies(c, b)
            }
            Item::IfElse(c, t, f) => {
                let c = self.boolean(c)?;
                let gt = self.bb.and(guard, c);
                let gf = self.bb.and(guard, !c);
                let t = self.items(t, gt, rank, soft, dists)?;
                let f = self.items(f, gf, rank, soft, dists)?;
                self.bb.ite(c, t, f)
            }
            Item::Dist(x, ds) => {
                let mut ors = Vec::with_capacity(ds.len());
                let mut spec = Vec::new();
                for d in ds {
                    if !p.dist_weight_nonzero(self.env, d)? {
                        continue;
                    }
                    ors.push(self.in_set(x, &d.item)?);
                    spec.push(self.dist_item(d));
                }
                if let (Some(k), Some(items)) = (p.key_of(self.env, x), spec.into_iter().collect())
                {
                    dists.push(DistSpec {
                        key: k,
                        guard,
                        items,
                    });
                }
                self.bb.or_all(ors)
            }
            Item::Foreach(a, l, body) => {
                let n = self.env.sizes[a.0]?;
                let mut all = Vec::with_capacity(n);
                for i in 0..n {
                    self.env.loops.insert(l.0, i as i64);
                    let t = self.items(body, guard, rank, soft, dists);
                    self.env.loops.remove(&l.0);
                    all.push(t?);
                }
                self.bb.and_all(all)
            }
            Item::Unique(es) => {
                let mut c = p.ty(&es[0]);
                for e in es {
                    c = join(c, p.ty(e));
                }
                let mut ts = Vec::with_capacity(es.len());
                for e in es {
                    ts.push(self.bv(e, c)?);
                }
                let mut ne = Vec::new();
                for i in 0..ts.len() {
                    for j in i + 1..ts.len() {
                        ne.push(!self.bb.eq(&ts[i], &ts[j]));
                    }
                }
                self.bb.and_all(ne)
            }
            Item::Soft(inner) => {
                rank.1 += 1;
                let mut nested = Vec::new();
                let t = self.item(inner, guard, rank, &mut nested, dists)?;
                let t = self.bb.implies(guard, t);
                // An unconditional `soft x == K` narrows `x` once kept.
                let bound = match (&**inner, guard == self.bb.tru()) {
                    (Item::Expr(e), true) => p.dom_expr(self.env, e),
                    _ => None,
                };
                soft.push(Soft {
                    rank: *rank,
                    lit: t,
                    bound,
                });
                self.bb.tru()
            }
        })
    }

    /// `(lo, hi, weight of the whole item)`; `None` when a bound or the
    /// weight depends on a variable.
    fn dist_item(&mut self, d: &DistItem) -> Option<(BigInt, BigInt, f64)> {
        let p = self.p;
        let (lo, hi) = match &d.item {
            SetItem::Value(v) => {
                let v = p.eval_int(self.env, v)?;
                (v.clone(), v)
            }
            SetItem::Range(lo, hi) => (p.eval_int(self.env, lo)?, p.eval_int(self.env, hi)?),
        };
        if hi < lo {
            return None;
        }
        let n = (&hi - &lo + BigInt::from(1)).to_f64().unwrap_or(f64::MAX);
        let w = match &d.weight {
            None => n,
            Some(Weight::Each(w)) => p.eval_int(self.env, w)?.to_f64()? * n,
            Some(Weight::Spread(w)) => p.eval_int(self.env, w)?.to_f64()?,
        };
        Some((lo, hi, w))
    }
}
