//! §11.6 / §11.8.1 — the self-determined type of an expression.

use crate::ir::{BinOp, Expr, Problem, UnOp};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Ty {
    pub w: u32,
    pub s: bool,
}

/// `int`: the type of `size()`, a `foreach` index, and an unsized literal.
pub(crate) const INT: Ty = Ty { w: 32, s: true };
/// The 1-bit unsigned result of a relational, equality, logical or
/// reduction operator.
pub(crate) const BIT: Ty = Ty { w: 1, s: false };

/// Context-determined operands of an operator meet at the wider width and
/// stay signed only if both are signed (§11.6.1, §11.8.1).
pub(crate) fn join(a: Ty, b: Ty) -> Ty {
    Ty {
        w: a.w.max(b.w),
        s: a.s && b.s,
    }
}

pub(crate) fn is_relational(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne
    )
}

pub(crate) fn is_logical(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::LogAnd | BinOp::LogOr | BinOp::Implies | BinOp::Equiv
    )
}

pub(crate) fn is_shift(op: BinOp) -> bool {
    matches!(op, BinOp::Shl | BinOp::Shr | BinOp::AShr)
}

impl Problem {
    pub(crate) fn ty(&self, e: &Expr) -> Ty {
        match e {
            Expr::Const(b) => Ty {
                w: b.width(),
                s: b.signed(),
            },
            Expr::Var(v) => Ty {
                w: self.vars[v.0].width,
                s: self.vars[v.0].signed,
            },
            Expr::Elem(a, _) => Ty {
                w: self.arrays[a.0].width,
                s: self.arrays[a.0].signed,
            },
            Expr::Size(_) | Expr::Loop(_) => INT,
            Expr::Unary(UnOp::Plus | UnOp::Neg | UnOp::BitNot, a) => self.ty(a),
            Expr::Unary(..) => BIT,
            Expr::Binary(op, l, r) => {
                if is_relational(*op) || is_logical(*op) {
                    BIT
                } else if is_shift(*op) {
                    self.ty(l)
                } else {
                    join(self.ty(l), self.ty(r))
                }
            }
            Expr::Cond(_, t, e) => join(self.ty(t), self.ty(e)),
            Expr::Concat(es) => Ty {
                w: es.iter().map(|e| self.ty(e).w).sum(),
                s: false,
            },
            Expr::Replicate(n, e) => Ty {
                w: n * self.ty(e).w,
                s: false,
            },
            Expr::Slice { msb, lsb, .. } => Ty {
                w: msb - lsb + 1,
                s: false,
            },
            Expr::Bit { .. } | Expr::Inside(..) => BIT,
            Expr::Cast { width, signed, .. } => Ty {
                w: *width,
                s: *signed,
            },
            Expr::Call { width, signed, .. } => Ty {
                w: *width,
                s: *signed,
            },
        }
    }
}
