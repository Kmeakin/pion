pub use ecow::{eco_vec, EcoVec};

use crate::env::{DeBruijnLevel, EnvLen, SharedEnv, SliceEnv};
use crate::prim::PrimVar;
use crate::symbol::Symbol;
use crate::syntax::{Expr, FunArg, FunParam, Lit, LocalVar, MetaVar};

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
    Lit(Lit<'core>),

    Neutral(Head<'core>, Spine<'core>),

    FunType(FunParam<'core, &'core Value<'core>>, Closure<'core>),
    FunLit(FunParam<'core, &'core Value<'core>>, Closure<'core>),

    RecordType(Telescope<'core>),
    RecordLit(RecordFields<'core, Self>),
}

pub type RecordFields<'core, Field> = &'core [(Symbol<'core>, Field)];

impl<'core> Value<'core> {
    pub const ERROR: Self = Self::Neutral(Head::Error, EcoVec::new());

    pub const TYPE: Self = Self::prim_var(PrimVar::Type);
    pub const BOOL: Self = Self::prim_var(PrimVar::Bool);
    pub const INT: Self = Self::prim_var(PrimVar::Int);
    pub const STRING: Self = Self::prim_var(PrimVar::String);
    pub const CHAR: Self = Self::prim_var(PrimVar::Char);
    pub const UNIT_TYPE: Self = Self::prim_var(PrimVar::Unit);
    pub const UNIT_VALUE: Self = Self::prim_var(PrimVar::unit);

    pub const fn local_var(var: LocalVar<'core, DeBruijnLevel>) -> Self {
        Self::Neutral(Head::LocalVar(var), EcoVec::new())
    }

    pub const fn meta_var(var: MetaVar) -> Self { Self::Neutral(Head::MetaVar(var), EcoVec::new()) }

    pub const fn prim_var(var: PrimVar) -> Self { Self::Neutral(Head::PrimVar(var), EcoVec::new()) }

    pub const fn bool(b: bool) -> Self { Self::Lit(Lit::Bool(b)) }
    pub const fn int(n: u32) -> Self { Self::Lit(Lit::Int(n)) }
    pub const fn char(c: char) -> Self { Self::Lit(Lit::Char(c)) }
    pub const fn string(s: &'core str) -> Self { Self::Lit(Lit::String(s)) }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Head<'core> {
    Error,
    LocalVar(LocalVar<'core, DeBruijnLevel>),
    MetaVar(MetaVar),
    PrimVar(PrimVar),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Elim<'core> {
    FunApp(FunArg<Value<'core>>),
    MatchBool(LocalValues<'core>, &'core Expr<'core>, &'core Expr<'core>),
    MatchInt(
        LocalValues<'core>,
        &'core [(u32, Expr<'core>)],
        &'core Expr<'core>,
    ),
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Telescope<'core> {
    pub local_values: LocalValues<'core>,
    pub fields: RecordFields<'core, Expr<'core>>,
}

impl<'core> Telescope<'core> {
    pub const fn empty() -> Self { Self::new(LocalValues::new(), &[]) }

    pub const fn new(
        local_values: LocalValues<'core>,
        fields: RecordFields<'core, Expr<'core>>,
    ) -> Self {
        Self {
            local_values,
            fields,
        }
    }
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
        assert_eq!(size_of::<Head>(), 32);
        assert_eq!(size_of::<Elim>(), 72);
        assert_eq!(size_of::<Closure>(), 24);
    }
}
