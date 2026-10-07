//! The constraint problem a simulator hands to the generator.
//!
//! The caller (xezim) lowers one `randomize()` call into a [`Problem`]:
//! - every active rand variable becomes a [`Problem::var`] or [`Problem::array`]
//!   (inactive ones, `rand_mode(0)`, are state);
//! - every state operand (non-rand members, `this.configuration.x`, locals)
//!   is evaluated by the caller and passed as [`Expr::Const`];
//! - every enabled constraint block becomes [`Problem::constraint`] with its
//!   soft priority (§18.5.14.1: later blocks, and derived-class blocks, rank
//!   higher).
//!
//! Expressions keep SystemVerilog's operators and operand types; the widths
//! and signedness rules of §11.6 / §11.8 are applied by the generator.

use crate::value::Bits;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VarId(pub(crate) usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ArrayId(pub(crate) usize);

/// The index variable of one `foreach`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LoopId(pub(crate) usize);

/// A function called from a constraint; the number is the caller's.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FuncId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    Plus,
    Neg,
    BitNot,
    LogNot,
    RedAnd,
    RedOr,
    RedXor,
    RedNand,
    RedNor,
    RedXnor,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    BitAnd,
    BitOr,
    BitXor,
    BitXnor,
    /// `<<` and `<<<`
    Shl,
    /// `>>`
    Shr,
    /// `>>>`
    AShr,
    Lt,
    Le,
    Gt,
    Ge,
    /// `==` and `===` (the values are two-state)
    Eq,
    /// `!=` and `!==`
    Ne,
    LogAnd,
    LogOr,
    /// `->`
    Implies,
    /// `<->`
    Equiv,
}

#[derive(Clone, Debug)]
pub enum Expr {
    Const(Bits),
    Var(VarId),
    /// `arr[index]`; the index must not depend on rand variables.
    Elem(ArrayId, Box<Expr>),
    /// `arr.size()`
    Size(ArrayId),
    /// The index of an enclosing `foreach`.
    Loop(LoopId),
    Unary(UnOp, Box<Expr>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Cond(Box<Expr>, Box<Expr>, Box<Expr>),
    Concat(Vec<Expr>),
    Replicate(u32, Box<Expr>),
    /// `base[msb:lsb]` with the bounds normalised to bit offsets.
    Slice {
        base: Box<Expr>,
        msb: u32,
        lsb: u32,
    },
    /// `base[index]` with a non-constant index (a bit offset).
    Bit {
        base: Box<Expr>,
        index: Box<Expr>,
    },
    /// `T'(e)`, `N'(e)`, `$signed(e)`, `$unsigned(e)`.
    Cast {
        width: u32,
        signed: bool,
        expr: Box<Expr>,
    },
    Inside(Box<Expr>, Vec<SetItem>),
    /// §18.5.12: the rand variables in `args` are solved first; the caller
    /// then evaluates the call with their values ([`crate::FuncEval`]).
    Call {
        func: FuncId,
        width: u32,
        signed: bool,
        args: Vec<Expr>,
    },
}

#[derive(Clone, Debug)]
pub enum SetItem {
    Value(Expr),
    Range(Expr, Expr),
}

#[derive(Clone, Debug)]
pub enum Weight {
    /// `:=` — every value of the item gets the weight.
    Each(Expr),
    /// `:/` — the weight is shared by the values of the item.
    Spread(Expr),
}

#[derive(Clone, Debug)]
pub struct DistItem {
    pub item: SetItem,
    /// `None` is `:= 1`.
    pub weight: Option<Weight>,
}

#[derive(Clone, Debug)]
pub enum Item {
    Expr(Expr),
    /// `cond -> { items }`
    Implies(Expr, Vec<Item>),
    /// `if (cond) { then } else { else }`
    IfElse(Expr, Vec<Item>, Vec<Item>),
    Dist(Expr, Vec<DistItem>),
    Foreach(ArrayId, LoopId, Vec<Item>),
    Unique(Vec<Expr>),
    Soft(Box<Item>),
}

/// A variable `solve ... before` can name.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VarRef {
    Var(VarId),
    Array(ArrayId),
}

#[derive(Clone, Copy, Debug)]
pub enum ArraySize {
    Fixed(usize),
    /// A rand dynamic array; its size is solved before its elements
    /// (§18.5.8.1). `max` bounds a size no constraint limits.
    Dynamic {
        max: usize,
    },
}

#[derive(Clone, Debug)]
pub(crate) struct VarDecl {
    pub name: String,
    pub width: u32,
    pub signed: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct ArrayDecl {
    pub name: String,
    pub width: u32,
    pub signed: bool,
    pub size: ArraySize,
}

#[derive(Clone, Debug)]
pub(crate) struct Block {
    pub priority: u32,
    pub items: Vec<Item>,
}

/// One `randomize()` call.
#[derive(Clone, Debug, Default)]
pub struct Problem {
    pub(crate) vars: Vec<VarDecl>,
    pub(crate) arrays: Vec<ArrayDecl>,
    pub(crate) loops: usize,
    pub(crate) blocks: Vec<Block>,
    pub(crate) before: Vec<(Vec<VarRef>, Vec<VarRef>)>,
}

impl Problem {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn var(&mut self, name: &str, width: u32, signed: bool) -> VarId {
        self.vars.push(VarDecl {
            name: name.to_string(),
            width,
            signed,
        });
        VarId(self.vars.len() - 1)
    }

    pub fn array(&mut self, name: &str, width: u32, signed: bool, size: ArraySize) -> ArrayId {
        self.arrays.push(ArrayDecl {
            name: name.to_string(),
            width,
            signed,
            size,
        });
        ArrayId(self.arrays.len() - 1)
    }

    pub fn var_name(&self, v: VarId) -> &str {
        &self.vars[v.0].name
    }

    pub fn array_name(&self, a: ArrayId) -> &str {
        &self.arrays[a.0].name
    }

    /// A fresh index variable for a `foreach`.
    pub fn loop_var(&mut self) -> LoopId {
        self.loops += 1;
        LoopId(self.loops - 1)
    }

    /// One constraint block. Higher `priority` wins between conflicting soft
    /// items; within a block a later item ranks higher.
    pub fn constraint(&mut self, priority: u32, items: Vec<Item>) {
        self.blocks.push(Block { priority, items });
    }

    /// `solve before_ before after;`
    pub fn solve_before(&mut self, before: Vec<VarRef>, after: Vec<VarRef>) {
        self.before.push((before, after));
    }
}

/// The values chosen by one solve.
#[derive(Clone, Debug, Default)]
pub struct Solution {
    pub(crate) vars: Vec<Option<Bits>>,
    pub(crate) arrays: Vec<Vec<Bits>>,
}

impl Solution {
    pub fn var(&self, v: VarId) -> &Bits {
        self.vars[v.0].as_ref().expect("variable was not solved")
    }

    pub fn array(&self, a: ArrayId) -> &[Bits] {
        &self.arrays[a.0]
    }
}

/// Short constructors, so a caller (or a test) can write expressions
/// without boxing by hand.
pub mod build {
    use super::*;

    pub fn c(width: u32, signed: bool, v: i64) -> Expr {
        Expr::Const(Bits::from_i64(width, signed, v))
    }
    /// A 32-bit signed literal, the type of an unsized decimal constant.
    pub fn int(v: i64) -> Expr {
        c(32, true, v)
    }
    pub fn var(v: VarId) -> Expr {
        Expr::Var(v)
    }
    pub fn elem(a: ArrayId, i: Expr) -> Expr {
        Expr::Elem(a, Box::new(i))
    }
    pub fn size(a: ArrayId) -> Expr {
        Expr::Size(a)
    }
    pub fn lp(l: LoopId) -> Expr {
        Expr::Loop(l)
    }
    pub fn un(op: UnOp, a: Expr) -> Expr {
        Expr::Unary(op, Box::new(a))
    }
    pub fn bin(op: BinOp, a: Expr, b: Expr) -> Expr {
        Expr::Binary(op, Box::new(a), Box::new(b))
    }
    pub fn cond(c: Expr, t: Expr, e: Expr) -> Expr {
        Expr::Cond(Box::new(c), Box::new(t), Box::new(e))
    }
    pub fn cast(width: u32, signed: bool, e: Expr) -> Expr {
        Expr::Cast {
            width,
            signed,
            expr: Box::new(e),
        }
    }
    pub fn inside(e: Expr, set: Vec<SetItem>) -> Expr {
        Expr::Inside(Box::new(e), set)
    }
    pub fn val(e: Expr) -> SetItem {
        SetItem::Value(e)
    }
    pub fn range(lo: Expr, hi: Expr) -> SetItem {
        SetItem::Range(lo, hi)
    }
    pub fn call(func: FuncId, width: u32, signed: bool, args: Vec<Expr>) -> Expr {
        Expr::Call {
            func,
            width,
            signed,
            args,
        }
    }
    pub fn item(e: Expr) -> Item {
        Item::Expr(e)
    }
    pub fn soft(i: Item) -> Item {
        Item::Soft(Box::new(i))
    }
    pub fn if_(c: Expr, t: Vec<Item>) -> Item {
        Item::IfElse(c, t, Vec::new())
    }
    pub fn if_else(c: Expr, t: Vec<Item>, e: Vec<Item>) -> Item {
        Item::IfElse(c, t, e)
    }
    pub fn foreach(a: ArrayId, l: LoopId, body: Vec<Item>) -> Item {
        Item::Foreach(a, l, body)
    }
    pub fn dist(e: Expr, items: Vec<DistItem>) -> Item {
        Item::Dist(e, items)
    }
    /// `item := w`
    pub fn each(item: SetItem, w: Expr) -> DistItem {
        DistItem {
            item,
            weight: Some(Weight::Each(w)),
        }
    }
    /// `item :/ w`
    pub fn spread(item: SetItem, w: Expr) -> DistItem {
        DistItem {
            item,
            weight: Some(Weight::Spread(w)),
        }
    }
}
