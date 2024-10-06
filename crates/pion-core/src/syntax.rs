use pion_interner::InternedStr;

use crate::env::{AbsoluteVar, RelativeVar};
use crate::prim::PrimVar;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Expr<'core> {
    Error,

    Lit(Lit<'core>),

    PrimVar(PrimVar),
    LocalVar(RelativeVar),
    MetaVar(AbsoluteVar),

    FunType(FunParam<'core, &'core Self>, &'core Self),
    FunLit(FunParam<'core, &'core Self>, &'core Self),
    FunApp(&'core Self, FunArg<&'core Self>),

    Do(&'core [Stmt<'core>], Option<&'core Self>),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Lit<'core> {
    Bool(bool),
    Int(u32),
    Char(char),
    String(&'core str),
}

impl<'core> Expr<'core> {
    pub const TYPE: Self = Self::PrimVar(PrimVar::Type);
    pub const BOOL: Self = Self::PrimVar(PrimVar::Bool);
    pub const INT: Self = Self::PrimVar(PrimVar::Int);
    pub const STRING: Self = Self::PrimVar(PrimVar::String);
    pub const CHAR: Self = Self::PrimVar(PrimVar::Char);
    pub const UNIT_TYPE: Self = Self::PrimVar(PrimVar::Unit);
    pub const UNIT_VALUE: Self = Self::PrimVar(PrimVar::unit);

    pub const fn bool(b: bool) -> Self { Self::Lit(Lit::Bool(b)) }
    pub const fn int(n: u32) -> Self { Self::Lit(Lit::Int(n)) }
    pub const fn char(c: char) -> Self { Self::Lit(Lit::Char(c)) }
    pub const fn string(s: &'core str) -> Self { Self::Lit(Lit::String(s)) }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Stmt<'core> {
    Let(LetBinding<'core, Expr<'core>>),
    Expr(Expr<'core>),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct LetBinding<'core, T> {
    pub name: Option<InternedStr<'core>>,
    pub r#type: T,
    pub init: T,
}

impl<'core, T> LetBinding<'core, T> {
    pub const fn new(name: Option<InternedStr<'core>>, r#type: T, init: T) -> Self {
        Self { name, r#type, init }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct FunParam<'core, T> {
    pub plicity: Plicity,
    pub name: Option<InternedStr<'core>>,
    pub r#type: T,
}

impl<'core, T> FunParam<'core, T> {
    pub const fn new(plicity: Plicity, name: Option<InternedStr<'core>>, r#type: T) -> Self {
        Self {
            plicity,
            name,
            r#type,
        }
    }
    pub const fn explicit(name: Option<InternedStr<'core>>, r#type: T) -> Self {
        Self::new(Plicity::Explicit, name, r#type)
    }
    pub const fn implicit(name: Option<InternedStr<'core>>, r#type: T) -> Self {
        Self::new(Plicity::Implicit, name, r#type)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct FunArg<T> {
    pub plicity: Plicity,
    pub expr: T,
}

impl<T> FunArg<T> {
    pub const fn new(plicity: Plicity, expr: T) -> Self { Self { plicity, expr } }
    pub const fn explicit(expr: T) -> Self { Self::new(Plicity::Explicit, expr) }
    pub const fn implicit(expr: T) -> Self { Self::new(Plicity::Implicit, expr) }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Plicity {
    /// Parameter/argument is inferred from context.
    Implicit,
    /// Parameter/argument is provided by the programmer.
    Explicit,
}

impl Plicity {
    pub const fn description(&self) -> &'static str {
        match self {
            Self::Implicit => "implicit",
            Self::Explicit => "explicit",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn type_sizes() {
        assert_eq!(size_of::<Expr>(), 48);
        assert_eq!(size_of::<Lit>(), 24);
        assert_eq!(size_of::<Stmt>(), 112);
        assert_eq!(size_of::<LetBinding<Expr>>(), 112);
        assert_eq!(size_of::<FunParam<Expr>>(), 72);
        assert_eq!(size_of::<FunArg<Expr>>(), 56);
    }
}
