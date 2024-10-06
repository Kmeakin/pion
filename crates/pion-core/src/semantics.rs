pub use ecow::{eco_vec, EcoVec};

use crate::env::{AbsoluteVar, EnvLen, SharedEnv, SliceEnv};
use crate::prim::PrimVar;
use crate::syntax::{Expr, FunArg, FunParam};

pub mod convertible;
pub mod elim;
pub mod eval;
pub mod quote;

pub use self::convertible::ConvertibleEnv;
pub use self::elim::ElimEnv;
pub use self::eval::EvalEnv;
pub use self::quote::QuoteEnv;

pub type LocalValues<'core> = SharedEnv<Value<'core>>;
pub type MetaValues<'core> = SliceEnv<Option<Value<'core>>>;

pub type Type<'core> = Value<'core>;
pub type Spine<'core> = EcoVec<Elim<'core>>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value<'core> {
    Bool(bool),
    Int(u32),
    Char(char),
    String(&'core str),

    Neutral(Head, Spine<'core>),

    FunType(FunParam<'core, &'core Expr<'core>>, Closure<'core>),
    FunLit(FunParam<'core, &'core Expr<'core>>, Closure<'core>),
}

impl Value<'_> {
    pub const ERROR: Self = Self::Neutral(Head::Error, EcoVec::new());

    pub const TYPE: Self = Self::prim_var(PrimVar::Type);
    pub const BOOL: Self = Self::prim_var(PrimVar::Bool);
    pub const INT: Self = Self::prim_var(PrimVar::Int);
    pub const STRING: Self = Self::prim_var(PrimVar::String);
    pub const CHAR: Self = Self::prim_var(PrimVar::Char);
    pub const UNIT_TYPE: Self = Self::prim_var(PrimVar::Unit);
    pub const UNIT_VALUE: Self = Self::prim_var(PrimVar::unit);

    pub const fn local_var(var: AbsoluteVar) -> Self {
        Self::Neutral(Head::LocalVar(var), EcoVec::new())
    }

    pub const fn meta_var(var: AbsoluteVar) -> Self {
        Self::Neutral(Head::MetaVar(var), EcoVec::new())
    }

    pub const fn prim_var(var: PrimVar) -> Self { Self::Neutral(Head::PrimVar(var), EcoVec::new()) }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Head {
    Error,
    LocalVar(AbsoluteVar),
    MetaVar(AbsoluteVar),
    PrimVar(PrimVar),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Elim<'core> {
    FunApp(FunArg<Value<'core>>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Closure<'core> {
    pub local_values: LocalValues<'core>,
    pub body: &'core Expr<'core>,
}

impl<'core> Closure<'core> {
    pub const fn new(local_values: LocalValues<'core>, body: &'core Expr<'core>) -> Self {
        Self { local_values, body }
    }

    pub const fn empty(body: &'core Expr<'core>) -> Self { Self::new(LocalValues::new(), body) }
}

#[derive(Debug, Copy, Clone)]
pub struct UnfoldOpts {
    pub unfold_fix: bool,
}

impl UnfoldOpts {
    pub const fn for_eval() -> Self { Self { unfold_fix: true } }
    pub const fn for_quote() -> Self { Self { unfold_fix: false } }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn type_sizes() {
        assert_eq!(size_of::<Value>(), 64);
        assert_eq!(size_of::<Head>(), 16);
        assert_eq!(size_of::<Elim>(), 72);
        assert_eq!(size_of::<Closure>(), 24);
    }
}
