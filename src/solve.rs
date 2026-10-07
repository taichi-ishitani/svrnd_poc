//! One `randomize()`: staged solving and value selection.
//!
//! Stages (each a fresh solver over the items that can be lowered by then):
//! 1. the rand arguments of functions called from constraints (§18.5.12);
//! 2. the sizes of rand dynamic arrays (§18.5.8.1);
//! 3. everything else.
//!
//! Within a stage, after xezim's CSP:
//! - the hard items are asserted; the soft items are tried all at once, and
//!   one by one from the highest rank only on a conflict (§18.5.14);
//! - `x == f(others)` with a division, remainder or product of variables
//!   is computed once the others are fixed (xezim's `Fun`);
//! - variables are fixed in `solve ... before` order (§18.5.10), smallest
//!   domain first, each drawn from its domain or its `dist` (§18.5.4); runs
//!   of plain variables are drawn together and split on a conflict.
//!
//! A value is fixed only after the solver accepted it, by assuming the
//! variable's bits.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::time::{Duration, Instant};

use num_bigint::{BigInt, BigUint, RandBigInt, Sign};
use rand::{Rng, RngCore};
use varisat::Lit;

use crate::FuncEval;
use crate::bb::{Bb, Bv};
use crate::domain::{self, Dom};
use crate::eval::{Env, Key};
use crate::ir::{ArraySize, Expr, Item, Problem, Solution, VarRef};
use crate::lower::{DistSpec, Enc, Soft};
use crate::value::{Bits, mask};

/// `key == expr`, decided by evaluating `expr` once `deps` are fixed.
struct Fun {
    key: Key,
    expr: Expr,
    ctx: crate::types::Ty,
    deps: Vec<Key>,
}

/// Division, remainder, or a product of two non-constants.
fn nonlinear(e: &Expr) -> bool {
    fn has_var(e: &Expr) -> bool {
        match e {
            Expr::Var(_) | Expr::Elem(..) | Expr::Size(_) => true,
            Expr::Const(_) | Expr::Loop(_) => false,
            Expr::Unary(_, a) | Expr::Replicate(_, a) => has_var(a),
            Expr::Binary(_, a, b) => has_var(a) || has_var(b),
            Expr::Cond(a, b, c) => has_var(a) || has_var(b) || has_var(c),
            Expr::Concat(es) => es.iter().any(has_var),
            Expr::Slice { base, .. } => has_var(base),
            Expr::Cast { expr, .. } => has_var(expr),
            _ => true,
        }
    }
    match e {
        Expr::Binary(op, a, b) => {
            use crate::ir::BinOp::*;
            matches!(op, Div | Mod) && has_var(a)
                || *op == Mul && has_var(a) && has_var(b)
                || nonlinear(a)
                || nonlinear(b)
        }
        Expr::Unary(_, a) | Expr::Replicate(_, a) => nonlinear(a),
        Expr::Cond(a, b, c) => nonlinear(a) || nonlinear(b) || nonlinear(c),
        Expr::Concat(es) => es.iter().any(nonlinear),
        Expr::Slice { base, .. } => nonlinear(base),
        Expr::Cast { expr, .. } => nonlinear(expr),
        _ => false,
    }
}

/// The literals that pin `bits` to `v`.
fn pins(bits: &[Lit], v: &BigUint) -> Vec<Lit> {
    bits.iter()
        .enumerate()
        .map(|(i, &l)| if v.bit(i as u64) { l } else { !l })
        .collect()
}

#[derive(Debug)]
pub enum SolveError {
    /// The constraints cannot all hold (§18.6.1: `randomize()` returns 0).
    Unsat,
    /// A `Fun` input was not fixed in time.
    Unknown,
}

/// Counters of one solve.
#[derive(Clone, Debug, Default)]
pub struct Stats {
    pub checks: u32,
    pub solver_time: Duration,
    /// SAT variables of the largest stage.
    pub sat_vars: usize,
}

struct Ctx<'r> {
    rng: &'r mut dyn RngCore,
    stats: Stats,
}

impl Ctx<'_> {
    fn check(&mut self, bb: &mut Bb, assume: &[Lit]) -> bool {
        let t = Instant::now();
        let r = bb.check(assume);
        self.stats.checks += 1;
        self.stats.solver_time += t.elapsed();
        r
    }
}

impl Problem {
    /// Solve once. `rng` is the object's random stream (§18.13); `funcs`
    /// evaluates the functions constraints call.
    pub fn solve(
        &self,
        rng: &mut dyn RngCore,
        funcs: &mut dyn FuncEval,
    ) -> Result<(Solution, Stats), SolveError> {
        let mut env = Env::new(self, funcs);
        let mut cx = Ctx {
            rng,
            stats: Stats::default(),
        };

        let call_args = self.call_arg_vars();
        if !call_args.is_empty() {
            let pick: HashSet<Key> = call_args.iter().map(|&v| Key::Var(v)).collect();
            self.stage(&mut env, &mut cx, &|k| pick.contains(&k))?;
        }
        if self
            .arrays
            .iter()
            .any(|a| matches!(a.size, ArraySize::Dynamic { .. }))
        {
            self.stage(&mut env, &mut cx, &|k| matches!(k, Key::Size(_)))?;
            for i in 0..self.arrays.len() {
                if env.sizes[i].is_none() {
                    let n = env
                        .fixed
                        .get(&Key::Size(i))
                        .and_then(|b| b.to_i64())
                        .unwrap_or(0);
                    env.sizes[i] = Some(n.max(0) as usize);
                }
            }
        }
        self.stage(&mut env, &mut cx, &|k| !matches!(k, Key::Size(_)))?;

        let mut sol = Solution {
            vars: vec![None; self.vars.len()],
            arrays: Vec::with_capacity(self.arrays.len()),
        };
        for (i, slot) in sol.vars.iter_mut().enumerate() {
            *slot = env.fixed.get(&Key::Var(i)).cloned();
        }
        for i in 0..self.arrays.len() {
            let n = env.sizes[i].unwrap_or(0);
            sol.arrays.push(
                (0..n)
                    .map(|j| env.fixed[&Key::Elem(i, j)].clone())
                    .collect(),
            );
        }
        Ok((sol, cx.stats))
    }

    /// Check a solution against every hard item, independently of the solver.
    pub fn verify(&self, sol: &Solution, funcs: &mut dyn FuncEval) -> Result<(), String> {
        let mut env = Env::new(self, funcs);
        for (i, v) in sol.vars.iter().enumerate() {
            if let Some(b) = v {
                env.fixed.insert(Key::Var(i), b.clone());
            }
        }
        for (i, a) in sol.arrays.iter().enumerate() {
            env.sizes[i] = Some(a.len());
            for (j, b) in a.iter().enumerate() {
                env.fixed.insert(Key::Elem(i, j), b.clone());
            }
        }
        for (bi, b) in self.blocks.iter().enumerate() {
            for (ii, it) in b.items.iter().enumerate() {
                match self.item_holds(&mut env, it) {
                    Some(true) => {}
                    Some(false) => return Err(format!("block {bi} item {ii} does not hold")),
                    None => return Err(format!("block {bi} item {ii} could not be evaluated")),
                }
            }
        }
        Ok(())
    }

    fn call_arg_vars(&self) -> Vec<usize> {
        fn expr(e: &Expr, in_call: bool, out: &mut Vec<usize>) {
            match e {
                Expr::Var(v) if in_call => {
                    if !out.contains(&v.0) {
                        out.push(v.0);
                    }
                }
                Expr::Call { args, .. } => args.iter().for_each(|a| expr(a, true, out)),
                Expr::Elem(_, i) => expr(i, in_call, out),
                Expr::Unary(_, a) | Expr::Replicate(_, a) => expr(a, in_call, out),
                Expr::Binary(_, a, b) => {
                    expr(a, in_call, out);
                    expr(b, in_call, out);
                }
                Expr::Cond(a, b, c) => {
                    expr(a, in_call, out);
                    expr(b, in_call, out);
                    expr(c, in_call, out);
                }
                Expr::Concat(es) => es.iter().for_each(|e| expr(e, in_call, out)),
                Expr::Slice { base, .. } => expr(base, in_call, out),
                Expr::Bit { base, index } => {
                    expr(base, in_call, out);
                    expr(index, in_call, out);
                }
                Expr::Cast { expr: e, .. } => expr(e, in_call, out),
                Expr::Inside(x, set) => {
                    expr(x, in_call, out);
                    for s in set {
                        match s {
                            crate::ir::SetItem::Value(v) => expr(v, in_call, out),
                            crate::ir::SetItem::Range(a, b) => {
                                expr(a, in_call, out);
                                expr(b, in_call, out);
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        fn item(it: &Item, out: &mut Vec<usize>) {
            match it {
                Item::Expr(e) => expr(e, false, out),
                Item::Implies(c, b) => {
                    expr(c, false, out);
                    b.iter().for_each(|i| item(i, out));
                }
                Item::IfElse(c, t, f) => {
                    expr(c, false, out);
                    t.iter().chain(f).for_each(|i| item(i, out));
                }
                Item::Dist(x, _) => expr(x, false, out),
                Item::Foreach(_, _, b) => b.iter().for_each(|i| item(i, out)),
                Item::Unique(es) => es.iter().for_each(|e| expr(e, false, out)),
                Item::Soft(i) => item(i, out),
            }
        }
        let mut out = Vec::new();
        for b in &self.blocks {
            b.items.iter().for_each(|i| item(i, &mut out));
        }
        out
    }

    /// Solve the items that can be lowered now and fix the keys `pick`
    /// selects.
    fn stage(
        &self,
        env: &mut Env,
        cx: &mut Ctx,
        pick: &dyn Fn(Key) -> bool,
    ) -> Result<(), SolveError> {
        // Once every size is known, variables bounded only by constants are
        // decided by their domains, outside the solver.
        let analysis = if env.sizes.iter().all(Option::is_some) {
            Some(self.analyze(env))
        } else {
            None
        };
        let mut bb = Bb::new();
        let mut vars: HashMap<Key, Bv> = HashMap::new();
        let mut soft: Vec<Soft> = Vec::new();
        let mut dists: Vec<DistSpec> = Vec::new();
        let mut funs: Vec<Fun> = Vec::new();
        {
            let mut enc = Enc {
                p: self,
                bb: &mut bb,
                env,
                vars: &mut vars,
            };
            let top = enc.bb.tru();
            for (bi, b) in self.blocks.iter().enumerate() {
                let mut rank = (b.priority, 0u32);
                for (ii, it) in b.items.iter().enumerate() {
                    if analysis.as_ref().is_some_and(|a| a.captured[bi][ii]) {
                        continue;
                    }
                    if let Some(f) = self.fun_item(enc.env, it, pick) {
                        funs.push(f);
                        continue;
                    }
                    let mut s_soft = Vec::new();
                    let mut s_dist = Vec::new();
                    // An item that cannot be lowered yet waits for a later
                    // stage; its soft and dist parts with it.
                    if let Some(l) = enc.items(
                        std::slice::from_ref(it),
                        top,
                        &mut rank,
                        &mut s_soft,
                        &mut s_dist,
                    ) {
                        enc.bb.assert(l);
                        soft.extend(s_soft);
                        dists.extend(s_dist);
                    }
                }
            }
            // Every variable this stage fixes gets bits, mentioned or not —
            // but one decided by its domain alone never reaches the solver.
            for k in self.stage_keys(enc.env, pick) {
                let alone = analysis.as_ref().is_some_and(|a| !a.coupled.contains(&k))
                    && !funs.iter().any(|f| f.key == k);
                if alone {
                    let a = analysis.as_ref().unwrap();
                    if a.doms.get(&k).is_some_and(|d| d.is_empty()) {
                        return Err(SolveError::Unsat);
                    }
                    let v = self.alone_value(cx, k, a);
                    enc.env.fixed.insert(k, v);
                } else {
                    enc.key_bits(k);
                }
            }
            // A dynamic array's size is a non-negative `int` up to its bound.
            let sizes: Vec<(usize, Bv)> = enc
                .vars
                .iter()
                .filter_map(|(k, v)| match k {
                    Key::Size(a) => Some((*a, v.clone())),
                    _ => None,
                })
                .collect();
            for (a, v) in sizes {
                let max = match self.arrays[a].size {
                    ArraySize::Dynamic { max } => max,
                    ArraySize::Fixed(n) => n,
                };
                let hi = enc.konst(&BigUint::from(max), 32);
                let zero = enc.konst(&BigUint::default(), 32);
                let ge = enc.bb.sle(&zero, &v);
                let le = enc.bb.sle(&v, &hi);
                enc.bb.assert(ge);
                enc.bb.assert(le);
            }
        }
        if !cx.check(&mut bb, &[]) {
            return Err(SolveError::Unsat);
        }
        // §18.5.14: all soft items at once first; on a conflict, a later
        // (higher-ranked) one wins.
        let all: Vec<Lit> = soft.iter().map(|x| x.lit).collect();
        let mut kept: Vec<&Soft> = Vec::new();
        if !all.is_empty() && cx.check(&mut bb, &all) {
            for x in &soft {
                bb.assert(x.lit);
                kept.push(x);
            }
        } else {
            soft.sort_by_key(|x| std::cmp::Reverse(x.rank));
            for x in &soft {
                if cx.check(&mut bb, &[x.lit]) {
                    bb.assert(x.lit);
                    kept.push(x);
                }
            }
        }

        let mut doms = match &analysis {
            Some(a) => a.doms.clone(),
            None => self.domains(env),
        };
        // A kept soft bound narrows like a hard one (xezim propagates it).
        for x in kept {
            if let Some((k, d)) = &x.bound {
                let cur = doms
                    .remove(k)
                    .unwrap_or_else(|| domain::full(self.key_ty(*k)));
                doms.insert(*k, domain::meet(&cur, d));
            }
        }
        let keys: Vec<Key> = vars
            .keys()
            .copied()
            .chain(funs.iter().map(|f| f.key))
            .filter(|&k| pick(k) && !env.fixed.contains_key(&k))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        let order = self.order(cx, keys, &doms, &funs);
        cx.stats.sat_vars = cx.stats.sat_vars.max(bb.nvars);
        let mut enc = Enc {
            p: self,
            bb: &mut bb,
            env,
            vars: &mut vars,
        };
        let mut i = 0;
        while i < order.len() {
            let k = order[i];
            if let Some(f) = funs.iter().find(|f| f.key == k) {
                let v = self.pick_fun(&mut enc, cx, f)?;
                enc.env.fixed.insert(k, v);
                i += 1;
                continue;
            }
            // A run of variables none of which waits on another of the run:
            // draw them all (by their `dist` when one is in force) and check
            // once; split on a conflict.
            let mut j = i;
            while j < order.len()
                && j - i < 1024
                && !funs.iter().any(|f| f.key == order[j])
                && !order[i..j].iter().any(|o| self.waits(&order[j], o, &funs))
            {
                j += 1;
            }
            let batch: Vec<Key> = order[i..j].to_vec();
            self.pick_batch(&mut enc, cx, &batch, &dists, &doms)?;
            i = j;
        }
        Ok(())
    }

    /// The keys a stage fixes: every scalar, every element of a sized array,
    /// every dynamic array's size — narrowed by `pick`.
    fn stage_keys(&self, env: &Env, pick: &dyn Fn(Key) -> bool) -> Vec<Key> {
        let mut ks: Vec<Key> = (0..self.vars.len()).map(Key::Var).collect();
        for (a, d) in self.arrays.iter().enumerate() {
            match env.sizes[a] {
                Some(n) => ks.extend((0..n).map(|i| Key::Elem(a, i))),
                None if matches!(d.size, ArraySize::Dynamic { .. }) => ks.push(Key::Size(a)),
                None => {}
            }
        }
        ks.into_iter()
            .filter(|&k| pick(k) && !env.fixed.contains_key(&k))
            .collect()
    }

    /// §18.5.10: a variable named before another, and the inputs of a
    /// `Fun`, are fixed first; otherwise the smallest domain goes first
    /// (as in xezim's CSP), ties broken at random.
    fn order(
        &self,
        cx: &mut Ctx,
        keys: Vec<Key>,
        doms: &HashMap<Key, Dom>,
        funs: &[Fun],
    ) -> Vec<Key> {
        let dsize = |k: &Key| match doms.get(k) {
            Some(d) => domain::size(d),
            None => BigUint::from(1u8) << self.key_ty(*k).w,
        };
        let mut pending = keys;
        for i in (1..pending.len()).rev() {
            let j = cx.rng.gen_range(0..=i);
            pending.swap(i, j);
        }
        let mut out = Vec::with_capacity(pending.len());
        while !pending.is_empty() {
            let pos = (0..pending.len())
                .filter(|&i| {
                    !pending
                        .iter()
                        .any(|o| o != &pending[i] && self.waits(&pending[i], o, funs))
                })
                .min_by_key(|&i| dsize(&pending[i]))
                .unwrap_or(0);
            out.push(pending.remove(pos));
        }
        out
    }

    /// Whether `k` must be fixed after `o` (`solve o before k`, or `o` is an
    /// input of `k`'s `Fun`).
    fn waits(&self, k: &Key, o: &Key, funs: &[Fun]) -> bool {
        let refs = |r: &VarRef, k: &Key| match (r, k) {
            (VarRef::Var(v), Key::Var(x)) => v.0 == *x,
            (VarRef::Array(a), Key::Elem(x, _) | Key::Size(x)) => a.0 == *x,
            _ => false,
        };
        self.before
            .iter()
            .any(|(bs, as_)| as_.iter().any(|a| refs(a, k)) && bs.iter().any(|b| refs(b, o)))
            || funs.iter().any(|f| f.key == *k && f.deps.contains(o))
    }

    fn draw(&self, cx: &mut Ctx, k: Key, dom: Option<&Dom>) -> BigUint {
        let ty = self.key_ty(k);
        match dom.filter(|d| !d.is_empty()) {
            Some(d) => Bits::from_bigint(ty.w, ty.s, &domain::draw(d, cx.rng))
                .bits()
                .clone(),
            None => cx.rng.gen_biguint(u64::from(ty.w)),
        }
    }

    /// The value of a variable decided by its domain alone: by its `dist`
    /// when it has one, else uniformly over the domain.
    fn alone_value(&self, cx: &mut Ctx, k: Key, a: &crate::domain::Analysis) -> Bits {
        let ty = self.key_ty(k);
        let dom = a.doms.get(&k);
        let v = a
            .dists
            .get(&k)
            .and_then(|items| {
                let d = DistSpec {
                    key: k,
                    guard: varisat::Lit::from_index(0, true),
                    items: items.clone(),
                };
                self.dist_draw(cx, k, &d, dom)
            })
            .unwrap_or_else(|| self.draw(cx, k, dom));
        Bits::new(ty.w, ty.s, v)
    }

    /// §18.5.4: a value drawn by a `dist` — an item in proportion to its
    /// weight among the items the domain still meets, then a value of that
    /// part (xezim's `csp_pick_val`).
    fn dist_draw(&self, cx: &mut Ctx, k: Key, d: &DistSpec, dom: Option<&Dom>) -> Option<BigUint> {
        let ty = self.key_ty(k);
        let mut live: Vec<(Dom, f64)> = Vec::new();
        for (lo, hi, w) in &d.items {
            let part = vec![(lo.clone(), hi.clone())];
            let part = match dom {
                Some(dm) => domain::meet(&part, dm),
                None => part,
            };
            if !part.is_empty() && *w > 0.0 {
                live.push((part, *w));
            }
        }
        let total: f64 = live.iter().map(|x| x.1).sum();
        if live.is_empty() || total <= 0.0 {
            return None;
        }
        let mut x = cx.rng.gen_range(0.0..total);
        let mut pick = live.len() - 1;
        for (i, (_, w)) in live.iter().enumerate() {
            if x < *w {
                pick = i;
                break;
            }
            x -= w;
        }
        let v = domain::draw(&live[pick].0, cx.rng);
        Some(Bits::from_bigint(ty.w, ty.s, &v).bits().clone())
    }

    /// Fix `batch` together: one check with every variable at its draw; on a
    /// conflict, halves (the first fixed before the second is retried), and a
    /// single variable falls back to `pick_value`.
    fn pick_batch(
        &self,
        enc: &mut Enc,
        cx: &mut Ctx,
        batch: &[Key],
        dists: &[DistSpec],
        doms: &HashMap<Key, Dom>,
    ) -> Result<(), SolveError> {
        if batch.is_empty() {
            return Ok(());
        }
        if batch.len() == 1 {
            let k = batch[0];
            let v = self.pick_value(enc, cx, k, dists, doms.get(&k))?;
            enc.env.fixed.insert(k, v);
            return Ok(());
        }
        // The guards of the dists are read from a model of the variables
        // fixed so far.
        if batch.iter().any(|k| dists.iter().any(|d| d.key == *k)) && !cx.check(enc.bb, &[]) {
            return Err(SolveError::Unsat);
        }
        let mut assume = Vec::new();
        let mut vals = Vec::with_capacity(batch.len());
        for &k in batch {
            let dom = doms.get(&k);
            let by_dist = dists
                .iter()
                .find(|d| d.key == k && enc.bb.value(d.guard))
                .and_then(|d| self.dist_draw(cx, k, d, dom));
            let r = match by_dist {
                Some(r) => r,
                None => self.draw(cx, k, dom),
            };
            let bits = enc.key_bits(k);
            assume.extend(pins(&bits, &r));
            vals.push(r);
        }
        if cx.check(enc.bb, &assume) {
            for l in assume {
                enc.bb.assert(l);
            }
            for (&k, v) in batch.iter().zip(vals) {
                let ty = self.key_ty(k);
                enc.env.fixed.insert(k, Bits::new(ty.w, ty.s, v));
            }
            return Ok(());
        }
        let mid = batch.len() / 2;
        self.pick_batch(enc, cx, &batch[..mid], dists, doms)?;
        self.pick_batch(enc, cx, &batch[mid..], dists, doms)
    }

    /// A top-level `k == e` (either way round) whose `e` divides, takes a
    /// remainder or multiplies two non-constants, and does not read `k`;
    /// only when `k` is fixed in this stage and `e`'s variables are fixed by
    /// now or in this stage.
    fn fun_item(&self, env: &mut Env, it: &Item, pick: &dyn Fn(Key) -> bool) -> Option<Fun> {
        let Item::Expr(Expr::Binary(crate::ir::BinOp::Eq, l, r)) = it else {
            return None;
        };
        for (x, e) in [(l, r), (r, l)] {
            let Some(k) = self.key_of(env, x) else {
                continue;
            };
            if !pick(k) || env.fixed.contains_key(&k) || !nonlinear(e) {
                continue;
            }
            let mut deps = Vec::new();
            if !self.expr_keys(env, e, &mut deps) || deps.contains(&k) {
                continue;
            }
            if deps.iter().all(|d| env.fixed.contains_key(d) || pick(*d)) {
                let ctx = crate::types::join(self.ty(x), self.ty(e));
                return Some(Fun {
                    key: k,
                    expr: (**e).clone(),
                    ctx,
                    deps,
                });
            }
        }
        None
    }

    /// The value of a `Fun` variable: its expression, once its inputs are
    /// fixed.
    fn pick_fun(&self, enc: &mut Enc, cx: &mut Ctx, f: &Fun) -> Result<Bits, SolveError> {
        let ty = self.key_ty(f.key);
        let v = self
            .eval(enc.env, &f.expr, f.ctx)
            .ok_or(SolveError::Unknown)?;
        let x = &v & mask(ty.w);
        // `k == e` at the context width: the extension of `x` must be `e`.
        if crate::eval::ext(x.clone(), ty.w, f.ctx) != v {
            return Err(SolveError::Unsat);
        }
        let bits = enc.key_bits(f.key);
        let p = pins(&bits, &x);
        if !cx.check(enc.bb, &p) {
            return Err(SolveError::Unsat);
        }
        for l in p {
            enc.bb.assert(l);
        }
        Ok(Bits::new(ty.w, ty.s, x))
    }

    fn pick_value(
        &self,
        enc: &mut Enc,
        cx: &mut Ctx,
        k: Key,
        dists: &[DistSpec],
        dom: Option<&Dom>,
    ) -> Result<Bits, SolveError> {
        let ty = self.key_ty(k);
        let bits = enc.key_bits(k);
        let fix = |enc: &mut Enc, v: &BigUint| {
            for l in pins(&bits, v) {
                enc.bb.assert(l);
            }
            Bits::new(ty.w, ty.s, v.clone())
        };
        let try_eq = |enc: &mut Enc, cx: &mut Ctx, v: &BigUint| cx.check(enc.bb, &pins(&bits, v));

        // §18.5.4: an active `dist` picks an item by weight, then a value of
        // the item; an item the other constraints rule out is dropped.
        let mine: Vec<&DistSpec> = dists.iter().filter(|d| d.key == k).collect();
        if !mine.is_empty() && !cx.check(enc.bb, &[]) {
            return Err(SolveError::Unsat);
        }
        for d in mine {
            if !enc.bb.value(d.guard) {
                continue;
            }
            let mut items: Vec<&(BigInt, BigInt, f64)> = d.items.iter().collect();
            while !items.is_empty() {
                let total: f64 = items.iter().map(|i| i.2).sum();
                let mut x = cx.rng.gen_range(0.0..total.max(f64::MIN_POSITIVE));
                let mut idx = items.len() - 1;
                for (i, it) in items.iter().enumerate() {
                    if x < it.2 {
                        idx = i;
                        break;
                    }
                    x -= it.2;
                }
                let (lo, hi, _) = items[idx];
                let span = (hi - lo + 1u32).to_biguint().unwrap();
                let pick = BigInt::from_biguint(Sign::Plus, cx.rng.gen_biguint_below(&span)) + lo;
                let v = Bits::from_bigint(ty.w, ty.s, &pick).bits().clone();
                if try_eq(enc, cx, &v) {
                    return Ok(fix(enc, &v));
                }
                items.remove(idx);
            }
        }

        // A target from the variable's domain (xezim draws from it too); a
        // few tries, then keep the high bits of a solution and draw ever fewer
        // low bits; at last, the solution's value.
        let tries = if dom.is_some_and(|d| !d.is_empty()) {
            3
        } else {
            1
        };
        let mut r = BigUint::default();
        for _ in 0..tries {
            r = self.draw(cx, k, dom);
            if try_eq(enc, cx, &r) {
                return Ok(fix(enc, &r));
            }
        }
        if !cx.check(enc.bb, &[]) {
            return Err(SolveError::Unsat);
        }
        let m = enc.bb.value_bv(&bits);
        let mut j = ty.w / 2;
        while j > 0 {
            let low = mask(j);
            let cand = (&m & (mask(ty.w) ^ &low)) | (&r & &low);
            if try_eq(enc, cx, &cand) {
                return Ok(fix(enc, &cand));
            }
            j /= 2;
        }
        // The model of the last satisfiable check without assumptions.
        if !cx.check(enc.bb, &[]) {
            return Err(SolveError::Unsat);
        }
        let m = enc.bb.value_bv(&bits);
        Ok(fix(enc, &m))
    }
}
