//! Bit-blasting onto varisat: bit-vectors as literal vectors (LSB first),
//! gates by the Tseitin encoding with constant folding and structural
//! hashing, and the circuits of the SystemVerilog operators.

use std::collections::HashMap;

use num_bigint::BigUint;
use varisat::{ExtendFormula, Lit, Solver};

/// A bit-vector: `v[0]` is the least significant bit.
pub(crate) type Bv = Vec<Lit>;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Gate {
    And(usize, usize),
    Xor(usize, usize),
    Ite(usize, usize, usize),
}

pub(crate) struct Bb {
    pub solver: Solver<'static>,
    t: Lit,
    gates: HashMap<Gate, Lit>,
    /// The values of the last satisfying assignment, by variable index.
    model: Vec<bool>,
    /// Variables created (inputs and gates).
    pub nvars: usize,
}

impl Bb {
    pub fn new() -> Self {
        let mut solver = Solver::new();
        let t = solver.new_lit();
        solver.add_clause(&[t]);
        Bb {
            solver,
            t,
            gates: HashMap::new(),
            model: Vec::new(),
            nvars: 1,
        }
    }

    pub fn tru(&self) -> Lit {
        self.t
    }

    pub fn fls(&self) -> Lit {
        !self.t
    }

    pub fn lit(&self, b: bool) -> Lit {
        if b { self.t } else { !self.t }
    }

    pub fn fresh(&mut self) -> Lit {
        self.nvars += 1;
        self.solver.new_lit()
    }

    pub fn fresh_bv(&mut self, w: u32) -> Bv {
        (0..w).map(|_| self.fresh()).collect()
    }

    pub fn assert(&mut self, l: Lit) {
        self.solver.add_clause(&[l]);
    }

    /// Satisfiable under `assume`? On `true` the model is kept.
    pub fn check(&mut self, assume: &[Lit]) -> bool {
        self.solver.assume(assume);
        let sat = self.solver.solve().expect("varisat");
        if sat {
            let m = self.solver.model().expect("model");
            let n = m.iter().map(|l| l.index() + 1).max().unwrap_or(0);
            self.model = vec![false; n];
            for l in m {
                self.model[l.index()] = l.is_positive();
            }
        }
        sat
    }

    /// The value of `l` in the last model.
    pub fn value(&self, l: Lit) -> bool {
        let v = self.model.get(l.index()).copied().unwrap_or(false);
        v ^ l.is_negative()
    }

    pub fn value_bv(&self, v: &[Lit]) -> BigUint {
        let mut x = BigUint::default();
        for (i, &l) in v.iter().enumerate() {
            if self.value(l) {
                x.set_bit(i as u64, true);
            }
        }
        x
    }

    fn is_t(&self, l: Lit) -> bool {
        l == self.t
    }

    fn is_f(&self, l: Lit) -> bool {
        l == !self.t
    }

    // ------------------------------------------------------------ gates

    pub fn and(&mut self, a: Lit, b: Lit) -> Lit {
        if self.is_f(a) || self.is_f(b) || a == !b {
            return self.fls();
        }
        if self.is_t(a) || a == b {
            return b;
        }
        if self.is_t(b) {
            return a;
        }
        let (x, y) = if a.code() < b.code() { (a, b) } else { (b, a) };
        let key = Gate::And(x.code(), y.code());
        if let Some(&o) = self.gates.get(&key) {
            return o;
        }
        let o = self.fresh();
        self.solver.add_clause(&[!o, a]);
        self.solver.add_clause(&[!o, b]);
        self.solver.add_clause(&[o, !a, !b]);
        self.gates.insert(key, o);
        o
    }

    pub fn or(&mut self, a: Lit, b: Lit) -> Lit {
        !self.and(!a, !b)
    }

    pub fn xor(&mut self, a: Lit, b: Lit) -> Lit {
        if self.is_f(a) {
            return b;
        }
        if self.is_f(b) {
            return a;
        }
        if self.is_t(a) {
            return !b;
        }
        if self.is_t(b) {
            return !a;
        }
        if a == b {
            return self.fls();
        }
        if a == !b {
            return self.tru();
        }
        // Normalise to positive inputs so `a ^ b` and `!a ^ !b` share.
        let flip = a.is_negative() ^ b.is_negative();
        let (a, b) = (a.var().positive(), b.var().positive());
        let (x, y) = if a.code() < b.code() { (a, b) } else { (b, a) };
        let key = Gate::Xor(x.code(), y.code());
        let o = match self.gates.get(&key) {
            Some(&o) => o,
            None => {
                let o = self.fresh();
                self.solver.add_clause(&[!o, x, y]);
                self.solver.add_clause(&[!o, !x, !y]);
                self.solver.add_clause(&[o, !x, y]);
                self.solver.add_clause(&[o, x, !y]);
                self.gates.insert(key, o);
                o
            }
        };
        if flip { !o } else { o }
    }

    pub fn ite(&mut self, c: Lit, t: Lit, e: Lit) -> Lit {
        if self.is_t(c) || t == e {
            return t;
        }
        if self.is_f(c) {
            return e;
        }
        if self.is_t(t) {
            return self.or(c, e);
        }
        if self.is_f(t) {
            return self.and(!c, e);
        }
        if self.is_t(e) {
            return self.or(!c, t);
        }
        if self.is_f(e) {
            return self.and(c, t);
        }
        let key = Gate::Ite(c.code(), t.code(), e.code());
        if let Some(&o) = self.gates.get(&key) {
            return o;
        }
        let o = self.fresh();
        self.solver.add_clause(&[!c, !t, o]);
        self.solver.add_clause(&[!c, t, !o]);
        self.solver.add_clause(&[c, !e, o]);
        self.solver.add_clause(&[c, e, !o]);
        self.gates.insert(key, o);
        o
    }

    pub fn and_all(&mut self, ls: impl IntoIterator<Item = Lit>) -> Lit {
        let mut acc = self.tru();
        for l in ls {
            acc = self.and(acc, l);
        }
        acc
    }

    pub fn or_all(&mut self, ls: impl IntoIterator<Item = Lit>) -> Lit {
        let mut acc = self.fls();
        for l in ls {
            acc = self.or(acc, l);
        }
        acc
    }

    pub fn implies(&mut self, a: Lit, b: Lit) -> Lit {
        self.or(!a, b)
    }

    // ------------------------------------------------------ bit-vectors

    pub fn konst(&self, v: &BigUint, w: u32) -> Bv {
        (0..w).map(|i| self.lit(v.bit(u64::from(i)))).collect()
    }

    /// Zero- or sign-extend (or truncate) to `w` bits.
    pub fn ext(&self, a: &[Lit], w: u32, signed: bool) -> Bv {
        let w = w as usize;
        if a.len() >= w {
            return a[..w].to_vec();
        }
        let fill = if signed {
            *a.last().unwrap()
        } else {
            self.fls()
        };
        let mut v = a.to_vec();
        v.resize(w, fill);
        v
    }

    pub fn not_bv(&self, a: &[Lit]) -> Bv {
        a.iter().map(|&l| !l).collect()
    }

    pub fn zip(&mut self, a: &[Lit], b: &[Lit], f: fn(&mut Self, Lit, Lit) -> Lit) -> Bv {
        a.iter().zip(b).map(|(&x, &y)| f(self, x, y)).collect()
    }

    pub fn ite_bv(&mut self, c: Lit, t: &[Lit], e: &[Lit]) -> Bv {
        t.iter().zip(e).map(|(&x, &y)| self.ite(c, x, y)).collect()
    }

    /// `a + b + cin`, the width of `a`.
    fn add_c(&mut self, a: &[Lit], b: &[Lit], cin: Lit) -> Bv {
        let mut c = cin;
        let mut out = Vec::with_capacity(a.len());
        for (&x, &y) in a.iter().zip(b) {
            let xy = self.xor(x, y);
            out.push(self.xor(xy, c));
            let g = self.and(x, y);
            let p = self.and(xy, c);
            c = self.or(g, p);
        }
        out
    }

    pub fn add(&mut self, a: &[Lit], b: &[Lit]) -> Bv {
        let f = self.fls();
        self.add_c(a, b, f)
    }

    pub fn sub(&mut self, a: &[Lit], b: &[Lit]) -> Bv {
        let nb = self.not_bv(b);
        let t = self.tru();
        self.add_c(a, &nb, t)
    }

    pub fn neg(&mut self, a: &[Lit]) -> Bv {
        let z = self.konst(&BigUint::default(), a.len() as u32);
        self.sub(&z, a)
    }

    /// Shift-and-add multiplier, truncated to the operand width.
    pub fn mul(&mut self, a: &[Lit], b: &[Lit]) -> Bv {
        let w = a.len();
        let mut acc = self.konst(&BigUint::default(), w as u32);
        for (i, &bi) in b.iter().enumerate() {
            if self.is_f(bi) {
                continue;
            }
            let mut pp = vec![self.fls(); w];
            for j in i..w {
                pp[j] = self.and(a[j - i], bi);
            }
            acc = self.add(&acc, &pp);
        }
        acc
    }

    pub fn eq(&mut self, a: &[Lit], b: &[Lit]) -> Lit {
        let mut acc = self.tru();
        for (&x, &y) in a.iter().zip(b) {
            let d = self.xor(x, y);
            acc = self.and(acc, !d);
        }
        acc
    }

    /// Unsigned `a < b`.
    pub fn ult(&mut self, a: &[Lit], b: &[Lit]) -> Lit {
        let mut lt = self.fls();
        for (&x, &y) in a.iter().zip(b) {
            // lt' = (!x & y) | (!(x ^ y) & lt)
            let here = self.and(!x, y);
            let d = self.xor(x, y);
            let keep = self.and(!d, lt);
            lt = self.or(here, keep);
        }
        lt
    }

    pub fn ule(&mut self, a: &[Lit], b: &[Lit]) -> Lit {
        !self.ult(b, a)
    }

    fn flip_msb(a: &[Lit]) -> Bv {
        let mut v = a.to_vec();
        if let Some(m) = v.last_mut() {
            *m = !*m;
        }
        v
    }

    pub fn slt(&mut self, a: &[Lit], b: &[Lit]) -> Lit {
        let (a, b) = (Self::flip_msb(a), Self::flip_msb(b));
        self.ult(&a, &b)
    }

    pub fn sle(&mut self, a: &[Lit], b: &[Lit]) -> Lit {
        !self.slt(b, a)
    }

    /// Barrel shifter. `kind`: 0 `<<`, 1 logical `>>`, 2 arithmetic `>>`.
    /// `n` is unsigned, of any width.
    pub fn shift(&mut self, a: &[Lit], n: &[Lit], kind: u8) -> Bv {
        let w = a.len();
        let fill = if kind == 2 {
            *a.last().unwrap()
        } else {
            self.fls()
        };
        let mut cur = a.to_vec();
        let mut over = self.fls();
        for (j, &nj) in n.iter().enumerate() {
            let s = 1usize.checked_shl(j as u32).unwrap_or(usize::MAX);
            if s >= w {
                // A set amount bit of this weight shifts everything out.
                over = self.or(over, nj);
                continue;
            }
            let shifted: Bv = (0..w)
                .map(|i| match kind {
                    0 => {
                        if i >= s {
                            cur[i - s]
                        } else {
                            self.fls()
                        }
                    }
                    _ => {
                        if i + s < w {
                            cur[i + s]
                        } else {
                            fill
                        }
                    }
                })
                .collect();
            cur = self.ite_bv(nj, &shifted, &cur);
        }
        let all = vec![fill; w];
        self.ite_bv(over, &all, &cur)
    }

    /// Restoring division: `(quotient, remainder)`; by zero, the quotient is
    /// all ones and the remainder is `a` (SMT-LIB semantics).
    pub fn udivrem(&mut self, a: &[Lit], b: &[Lit]) -> (Bv, Bv) {
        let w = a.len();
        let bx = self.ext(b, w as u32 + 1, false);
        let mut rem = vec![self.fls(); w + 1];
        let mut q = vec![self.fls(); w];
        for i in (0..w).rev() {
            // rem = (rem << 1) | a[i]
            let mut r = Vec::with_capacity(w + 1);
            r.push(a[i]);
            r.extend_from_slice(&rem[..w]);
            let lt = self.ult(&r, &bx);
            q[i] = !lt;
            let d = self.sub(&r, &bx);
            rem = self.ite_bv(lt, &r, &d);
        }
        (q, rem[..w].to_vec())
    }

    /// Signed division: truncating; the remainder takes the dividend's sign.
    pub fn sdivrem(&mut self, a: &[Lit], b: &[Lit]) -> (Bv, Bv) {
        let sa = *a.last().unwrap();
        let sb = *b.last().unwrap();
        let na = self.neg(a);
        let nb = self.neg(b);
        let ua = self.ite_bv(sa, &na, a);
        let ub = self.ite_bv(sb, &nb, b);
        let (q, r) = self.udivrem(&ua, &ub);
        let sq = self.xor(sa, sb);
        let nq = self.neg(&q);
        let nr = self.neg(&r);
        (self.ite_bv(sq, &nq, &q), self.ite_bv(sa, &nr, &r))
    }
}
