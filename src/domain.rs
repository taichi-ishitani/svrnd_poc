//! Interval domains of single variables, taken from the hard items that
//! bound one variable by constants (`x inside {…}`, `x < K`, `K <= x`, …).
//!
//! As in xezim's CSP, a variable draws its value from its domain, so a draw
//! rarely contradicts the constraints. Here the domain is only a hint for
//! the draw: the solver still enforces every constraint.

use std::collections::HashMap;

use num_bigint::{BigInt, BigUint, RandBigInt, Sign};
use num_traits::{One, Zero};
use rand::RngCore;

use crate::eval::{Env, Key, signed_of};
use crate::ir::{BinOp, Expr, Item, Problem, SetItem};
use crate::types::{Ty, join};

/// Sorted, disjoint, inclusive intervals of a variable's own values
/// (signed if the variable is).
pub(crate) type Dom = Vec<(BigInt, BigInt)>;

pub(crate) fn full(t: Ty) -> Dom {
    if t.s {
        let h = BigInt::one() << (t.w - 1);
        vec![(-h.clone(), h - 1)]
    } else {
        vec![(BigInt::zero(), (BigInt::one() << t.w) - 1)]
    }
}

fn norm(mut v: Dom) -> Dom {
    v.retain(|(a, b)| a <= b);
    v.sort();
    let mut out: Dom = Vec::with_capacity(v.len());
    for (a, b) in v {
        match out.last_mut() {
            Some((_, hi)) if a <= &*hi + 1 => {
                if b > *hi {
                    *hi = b;
                }
            }
            _ => out.push((a, b)),
        }
    }
    out
}

pub(crate) fn meet(a: &Dom, b: &Dom) -> Dom {
    let mut out = Vec::new();
    for (al, ah) in a {
        for (bl, bh) in b {
            let lo = al.max(bl).clone();
            let hi = ah.min(bh).clone();
            if lo <= hi {
                out.push((lo, hi));
            }
        }
    }
    norm(out)
}

fn union(a: Dom, b: Dom) -> Dom {
    norm(a.into_iter().chain(b).collect())
}

pub(crate) fn size(d: &Dom) -> BigUint {
    d.iter()
        .map(|(a, b)| (b - a + BigInt::one()).to_biguint().unwrap())
        .sum()
}

/// A uniform draw from a non-empty domain.
pub(crate) fn draw(d: &Dom, rng: &mut dyn RngCore) -> BigInt {
    let mut k = rng.gen_biguint_below(&size(d));
    for (a, b) in d {
        let n = (b - a + BigInt::one()).to_biguint().unwrap();
        if k < n {
            return a + BigInt::from_biguint(Sign::Plus, k);
        }
        k -= n;
    }
    unreachable!()
}

impl Problem {
    /// The domain of every variable the top-level hard items bound by
    /// constants; items under a condition or soft do not narrow.
    pub(crate) fn domains(&self, env: &mut Env) -> HashMap<Key, Dom> {
        let mut out = HashMap::new();
        for b in &self.blocks {
            self.dom_items(env, &b.items, &mut out);
        }
        out
    }

    fn dom_items(&self, env: &mut Env, items: &[Item], out: &mut HashMap<Key, Dom>) {
        for it in items {
            match it {
                Item::Expr(e) => {
                    if let Some((k, d)) = self.dom_expr(env, e) {
                        let cur = out.remove(&k).unwrap_or_else(|| full(self.key_ty(k)));
                        out.insert(k, meet(&cur, &d));
                    }
                }
                Item::Foreach(a, l, body) => {
                    let Some(n) = env.sizes[a.0] else { continue };
                    for i in 0..n {
                        env.loops.insert(l.0, i as i64);
                        self.dom_items(env, body, out);
                    }
                    env.loops.remove(&l.0);
                }
                _ => {}
            }
        }
    }

    pub(crate) fn key_ty(&self, k: Key) -> Ty {
        match k {
            Key::Var(v) => Ty {
                w: self.vars[v].width,
                s: self.vars[v].signed,
            },
            Key::Elem(a, _) => Ty {
                w: self.arrays[a].width,
                s: self.arrays[a].signed,
            },
            Key::Size(_) => crate::types::INT,
        }
    }

    /// The variable a bare operand names (`x`, `arr[3]`).
    pub(crate) fn key_of(&self, env: &mut Env, e: &Expr) -> Option<Key> {
        match e {
            Expr::Var(v) => Some(Key::Var(v.0)),
            Expr::Elem(a, i) => Some(Key::Elem(a.0, self.eval_index(env, i)?)),
            _ => None,
        }
    }

    pub(crate) fn dom_expr(&self, env: &mut Env, e: &Expr) -> Option<(Key, Dom)> {
        if let Some(d) = self.dom_shr(env, e) {
            return Some(d);
        }
        // `a || b`, `a && b` of bounds on one variable.
        if let Expr::Binary(op @ (BinOp::LogOr | BinOp::LogAnd), l, r) = e {
            let (ka, da) = self.dom_expr(env, l)?;
            let (kb, db) = self.dom_expr(env, r)?;
            if ka != kb {
                return None;
            }
            let d = if *op == BinOp::LogOr {
                union(da, db)
            } else {
                meet(&da, &db)
            };
            return Some((ka, d));
        }
        match e {
            Expr::Binary(op, l, r) => {
                let op = *op;
                if let Some(k) = self.key_of(env, l) {
                    Some((k, self.dom_rel(env, k, l, op, r)?))
                } else {
                    let k = self.key_of(env, r)?;
                    let flip = match op {
                        BinOp::Lt => BinOp::Gt,
                        BinOp::Le => BinOp::Ge,
                        BinOp::Gt => BinOp::Lt,
                        BinOp::Ge => BinOp::Le,
                        o => o,
                    };
                    Some((k, self.dom_rel(env, k, r, flip, l)?))
                }
            }
            Expr::Inside(x, set) => {
                let k = self.key_of(env, x)?;
                let mut d: Dom = Vec::new();
                for s in set {
                    let part = match s {
                        SetItem::Value(v) => self.dom_rel(env, k, x, BinOp::Eq, v)?,
                        SetItem::Range(lo, hi) => meet(
                            &self.dom_rel(env, k, x, BinOp::Ge, lo)?,
                            &self.dom_rel(env, k, x, BinOp::Le, hi)?,
                        ),
                    };
                    d = union(d, part);
                }
                Some((k, d))
            }
            _ => None,
        }
    }

    /// `(x >> k) REL c` (either way round), `x` an unsigned variable and
    /// `k`, `c` constants: `x >> k` is `floor(x / 2**k)`, so the relation is
    /// one interval of `x` (xezim's `csp_shr_rel`).
    fn dom_shr(&self, env: &mut Env, e: &Expr) -> Option<(Key, Dom)> {
        let Expr::Binary(op, l, r) = e else {
            return None;
        };
        let (sh, c, op) = match (&**l, &**r) {
            (Expr::Binary(BinOp::Shr, ..), _) => (&**l, &**r, *op),
            (_, Expr::Binary(BinOp::Shr, ..)) => (
                &**r,
                &**l,
                match op {
                    BinOp::Lt => BinOp::Gt,
                    BinOp::Le => BinOp::Ge,
                    BinOp::Gt => BinOp::Lt,
                    BinOp::Ge => BinOp::Le,
                    o => *o,
                },
            ),
            _ => return None,
        };
        let Expr::Binary(_, x, amt) = sh else {
            return None;
        };
        let k = self.key_of(env, x)?;
        let kt = self.key_ty(k);
        if kt.s {
            return None;
        }
        let ct = join(kt, self.ty(c));
        if ct.s {
            return None;
        }
        let n: u32 = self.eval_int(env, amt)?.try_into().ok()?;
        let cv = BigInt::from_biguint(Sign::Plus, self.eval(env, c, ct)?);
        let one = BigInt::one();
        let lo = |v: &BigInt| v << n;
        let hi = |v: &BigInt| ((v + &one) << n) - &one;
        let top: BigInt = (BigInt::one() << kt.w) - BigInt::one();
        let zero = BigInt::zero();
        let d: Dom = match op {
            BinOp::Eq => vec![(lo(&cv), hi(&cv))],
            BinOp::Lt => vec![(zero, lo(&cv) - &one)],
            BinOp::Le => vec![(zero, hi(&cv))],
            BinOp::Gt => vec![(hi(&cv) + &one, top.clone())],
            BinOp::Ge => vec![(lo(&cv), top.clone())],
            _ => return None,
        };
        Some((k, meet(&d, &full(kt))))
    }

    /// The values of `k` (operand `x`) for which `x OP c` holds, `c` a
    /// constant: the bound is taken in the comparison's context type and
    /// mapped back to the variable's own values.
    fn dom_rel(&self, env: &mut Env, k: Key, x: &Expr, op: BinOp, c: &Expr) -> Option<Dom> {
        let kt = self.key_ty(k);
        let ct = join(self.ty(x), self.ty(c));
        let cv = self.eval(env, c, ct)?;
        let cv = if ct.s {
            signed_of(&cv, ct.w)
        } else {
            BigInt::from_biguint(Sign::Plus, cv)
        };
        let (lo, hi) = full(ct).pop()?;
        let one = BigInt::one();
        let ctx_set: Dom = match op {
            BinOp::Lt => vec![(lo, cv - one)],
            BinOp::Le => vec![(lo, cv)],
            BinOp::Gt => vec![(cv + one, hi)],
            BinOp::Ge => vec![(cv, hi)],
            BinOp::Eq => vec![(cv.clone(), cv)],
            _ => return None,
        };
        // The context value of `x` is `x` itself, except a signed variable in
        // an unsigned context, whose negative values read as `x + 2**w`.
        let own = full(kt);
        let mut d = meet(&own, &ctx_set);
        if kt.s && !ct.s {
            let m = BigInt::one() << kt.w;
            let neg: Dom = meet(&ctx_set, &vec![(&m >> 1usize, &m - 1)])
                .into_iter()
                .map(|(a, b)| (a - &m, b - &m))
                .collect();
            d = union(meet(&d, &vec![(BigInt::zero(), (&m >> 1usize) - 1)]), neg);
        }
        Some(norm(d))
    }
}

/// Which items a domain captures exactly, and the variables that occur in
/// any other item.
pub(crate) struct Analysis {
    pub doms: HashMap<Key, Dom>,
    /// `dist` items (constant bounds and weights) of a captured `dist`.
    pub dists: HashMap<Key, Vec<(BigInt, BigInt, f64)>>,
    /// Variables of items no domain captures.
    pub coupled: std::collections::HashSet<Key>,
    /// Per block, per item: captured entirely.
    pub captured: Vec<Vec<bool>>,
}

impl Problem {
    /// As in xezim's CSP, a variable whose every item is a bound by
    /// constants is decided by its domain alone: such an item is captured,
    /// and the solver never needs it. Requires every array size.
    pub(crate) fn analyze(&self, env: &mut Env) -> Analysis {
        let mut a = Analysis {
            doms: HashMap::new(),
            dists: HashMap::new(),
            coupled: Default::default(),
            captured: Vec::new(),
        };
        for b in &self.blocks {
            let mut row = Vec::with_capacity(b.items.len());
            for it in &b.items {
                row.push(self.cap_item(env, it, &mut a));
            }
            a.captured.push(row);
        }
        // A captured item stays out of the solver only when none of its
        // variables is decided there.
        for (bi, b) in self.blocks.iter().enumerate() {
            for (ii, it) in b.items.iter().enumerate() {
                if a.captured[bi][ii] {
                    let mut ks = Vec::new();
                    self.item_keys(env, it, &mut ks);
                    if ks.iter().any(|k| a.coupled.contains(k)) {
                        a.captured[bi][ii] = false;
                    }
                }
            }
        }
        a
    }

    fn cap_items(&self, env: &mut Env, items: &[Item], a: &mut Analysis) -> bool {
        let mut all = true;
        for it in items {
            all &= self.cap_item(env, it, a);
        }
        all
    }

    fn cap_item(&self, env: &mut Env, it: &Item, a: &mut Analysis) -> bool {
        let captured = match it {
            Item::Expr(e) => match self.dom_expr(env, e) {
                Some((k, d)) if self.only_key(env, e, k) => {
                    let cur = a.doms.remove(&k).unwrap_or_else(|| full(self.key_ty(k)));
                    a.doms.insert(k, meet(&cur, &d));
                    true
                }
                _ => false,
            },
            Item::Dist(x, ds) => match (self.key_of(env, x), self.dist_items(env, ds)) {
                (Some(k), Some(items)) if self.only_key(env, x, k) => {
                    let d = norm(
                        items
                            .iter()
                            .map(|(lo, hi, _)| (lo.clone(), hi.clone()))
                            .collect(),
                    );
                    let cur = a.doms.remove(&k).unwrap_or_else(|| full(self.key_ty(k)));
                    a.doms.insert(k, meet(&cur, &d));
                    a.dists.insert(k, items);
                    true
                }
                _ => false,
            },
            Item::IfElse(c, t, f) if !self.has_var(env, c) => match self.truth(env, c) {
                Some(true) => return self.cap_items(env, t, a),
                Some(false) => return self.cap_items(env, f, a),
                None => false,
            },
            Item::Implies(c, b) if !self.has_var(env, c) => match self.truth(env, c) {
                Some(true) => return self.cap_items(env, b, a),
                Some(false) => return true,
                None => false,
            },
            Item::Foreach(arr, l, body) => {
                let Some(n) = env.sizes[arr.0] else {
                    return false;
                };
                let mut all = true;
                for i in 0..n {
                    env.loops.insert(l.0, i as i64);
                    all &= self.cap_items(env, body, a);
                }
                env.loops.remove(&l.0);
                return all;
            }
            _ => false,
        };
        if !captured {
            let mut ks = Vec::new();
            self.item_keys(env, it, &mut ks);
            a.coupled.extend(ks);
        }
        captured
    }

    /// Whether `e` reads `k` and no other variable.
    fn only_key(&self, env: &mut Env, e: &Expr, k: Key) -> bool {
        let mut ks = Vec::new();
        self.expr_keys(env, e, &mut ks) && ks == [k]
    }

    fn has_var(&self, env: &mut Env, e: &Expr) -> bool {
        let mut ks = Vec::new();
        !self.expr_keys(env, e, &mut ks) || !ks.is_empty()
    }

    /// Every variable an item reads (element indices evaluated; an
    /// unevaluable index reads the whole array). Calls are evaluated by the
    /// caller, so their arguments are read.
    pub(crate) fn item_keys(&self, env: &mut Env, it: &Item, out: &mut Vec<Key>) {
        match it {
            Item::Expr(e) => self.all_keys(env, e, out),
            Item::Implies(c, b) => {
                self.all_keys(env, c, out);
                b.iter().for_each(|i| self.item_keys(env, i, out));
            }
            Item::IfElse(c, t, f) => {
                self.all_keys(env, c, out);
                t.iter().chain(f).for_each(|i| self.item_keys(env, i, out));
            }
            Item::Dist(x, ds) => {
                self.all_keys(env, x, out);
                for d in ds {
                    match &d.item {
                        SetItem::Value(v) => self.all_keys(env, v, out),
                        SetItem::Range(l, h) => {
                            self.all_keys(env, l, out);
                            self.all_keys(env, h, out);
                        }
                    }
                }
            }
            Item::Foreach(arr, l, body) => {
                let n = env.sizes[arr.0].unwrap_or(0);
                for i in 0..n {
                    env.loops.insert(l.0, i as i64);
                    body.iter().for_each(|b| self.item_keys(env, b, out));
                }
                env.loops.remove(&l.0);
            }
            Item::Unique(es) => es.iter().for_each(|e| self.all_keys(env, e, out)),
            Item::Soft(i) => self.item_keys(env, i, out),
        }
    }

    fn all_keys(&self, env: &mut Env, e: &Expr, out: &mut Vec<Key>) {
        let mut add = |k: Key| {
            if !out.contains(&k) {
                out.push(k);
            }
        };
        match e {
            Expr::Var(_) | Expr::Elem(..) => match self.key_of(env, e) {
                Some(k) => add(k),
                None => {
                    if let Expr::Elem(arr, _) = e {
                        let n = env.sizes[arr.0].unwrap_or(0);
                        (0..n).for_each(|i| add(Key::Elem(arr.0, i)));
                    }
                }
            },
            Expr::Size(arr) => add(Key::Size(arr.0)),
            Expr::Unary(_, x) | Expr::Replicate(_, x) => self.all_keys(env, x, out),
            Expr::Binary(_, x, y) => {
                self.all_keys(env, x, out);
                self.all_keys(env, y, out);
            }
            Expr::Cond(x, y, z) => {
                self.all_keys(env, x, out);
                self.all_keys(env, y, out);
                self.all_keys(env, z, out);
            }
            Expr::Concat(es) => es.iter().for_each(|x| self.all_keys(env, x, out)),
            Expr::Slice { base, .. } => self.all_keys(env, base, out),
            Expr::Bit { base, index } => {
                self.all_keys(env, base, out);
                self.all_keys(env, index, out);
            }
            Expr::Cast { expr, .. } => self.all_keys(env, expr, out),
            Expr::Inside(x, set) => {
                self.all_keys(env, x, out);
                for s in set {
                    match s {
                        SetItem::Value(v) => self.all_keys(env, v, out),
                        SetItem::Range(l, h) => {
                            self.all_keys(env, l, out);
                            self.all_keys(env, h, out);
                        }
                    }
                }
            }
            Expr::Call { args, .. } => args.iter().for_each(|x| self.all_keys(env, x, out)),
            Expr::Const(_) | Expr::Loop(_) => {}
        }
    }

    /// The variables `e` reads; false when an element index is not constant.
    pub(crate) fn expr_keys(&self, env: &mut Env, e: &Expr, out: &mut Vec<Key>) -> bool {
        let add = |k: Key, out: &mut Vec<Key>| {
            if !out.contains(&k) {
                out.push(k);
            }
        };
        match e {
            Expr::Var(_) | Expr::Elem(..) => match self.key_of(env, e) {
                Some(k) => {
                    add(k, out);
                    true
                }
                None => false,
            },
            Expr::Size(a) if env.sizes[a.0].is_none() => {
                add(Key::Size(a.0), out);
                true
            }
            Expr::Unary(_, a) | Expr::Replicate(_, a) => self.expr_keys(env, a, out),
            Expr::Binary(_, a, b) => self.expr_keys(env, a, out) && self.expr_keys(env, b, out),
            Expr::Cond(a, b, c) => {
                self.expr_keys(env, a, out)
                    && self.expr_keys(env, b, out)
                    && self.expr_keys(env, c, out)
            }
            Expr::Concat(es) => es.iter().all(|x| self.expr_keys(env, x, out)),
            Expr::Slice { base, .. } => self.expr_keys(env, base, out),
            Expr::Cast { expr, .. } => self.expr_keys(env, expr, out),
            Expr::Inside(x, set) => {
                self.expr_keys(env, x, out)
                    && set.iter().all(|s| match s {
                        SetItem::Value(v) => self.expr_keys(env, v, out),
                        SetItem::Range(l, h) => {
                            self.expr_keys(env, l, out) && self.expr_keys(env, h, out)
                        }
                    })
            }
            Expr::Bit { .. } | Expr::Call { .. } => false,
            _ => true,
        }
    }

    /// `(lo, hi, weight of the whole item)` of every item of a `dist` with a
    /// non-zero weight; `None` when a bound or weight depends on a variable.
    pub(crate) fn dist_items(
        &self,
        env: &mut Env,
        ds: &[crate::ir::DistItem],
    ) -> Option<Vec<(BigInt, BigInt, f64)>> {
        use num_traits::ToPrimitive;
        let mut out = Vec::new();
        for d in ds {
            if !self.dist_weight_nonzero(env, d)? {
                continue;
            }
            let (lo, hi) = match &d.item {
                SetItem::Value(v) => {
                    let v = self.eval_int(env, v)?;
                    (v.clone(), v)
                }
                SetItem::Range(lo, hi) => (self.eval_int(env, lo)?, self.eval_int(env, hi)?),
            };
            if hi < lo {
                continue;
            }
            let n = (&hi - &lo + BigInt::one()).to_f64().unwrap_or(f64::MAX);
            let w = match &d.weight {
                None => n,
                Some(crate::ir::Weight::Each(w)) => self.eval_int(env, w)?.to_f64()? * n,
                Some(crate::ir::Weight::Spread(w)) => self.eval_int(env, w)?.to_f64()?,
            };
            out.push((lo, hi, w));
        }
        Some(out)
    }
}
