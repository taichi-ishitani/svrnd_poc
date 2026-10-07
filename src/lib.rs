//! `svrand` — SystemVerilog constrained randomization of any width, by
//! bit-blasting onto a SAT solver (varisat). A proof of concept for xezim.
//!
//! The caller lowers one `randomize()` into a [`Problem`] and calls
//! [`Problem::solve`]; see [`ir`] for what the caller is responsible for.

mod bb;
#[cfg(test)]
mod difftest;
mod domain;
mod eval;
pub mod ir;
mod lower;
mod solve;
mod types;
pub mod value;

pub use ir::{
    ArrayId, ArraySize, BinOp, DistItem, Expr, FuncId, Item, LoopId, Problem, SetItem, Solution,
    UnOp, VarId, VarRef, Weight, build,
};
pub use solve::{SolveError, Stats};
pub use value::Bits;

/// Evaluates a function called from a constraint, once its rand arguments
/// are fixed (§18.5.12).
pub trait FuncEval {
    fn call(&mut self, func: FuncId, args: &[Bits]) -> Bits;
}

/// For problems without function calls.
pub struct NoFuncs;

impl FuncEval for NoFuncs {
    fn call(&mut self, func: FuncId, _: &[Bits]) -> Bits {
        panic!("no function {func:?}")
    }
}
