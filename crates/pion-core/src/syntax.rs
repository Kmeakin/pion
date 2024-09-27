use pion_interner::InternedStr;

use crate::env::{AbsoluteVar, RelativeVar};
use crate::prim::PrimVar;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Expr<'core> {
    Error,

    Bool(bool),
    Int(u32),
    Char(char),
    String(&'core str),

    PrimVar(PrimVar),
    LocalVar(RelativeVar),
    MetaVar(AbsoluteVar),

    Let(LetBinding<'core, &'core Self>, &'core Self),

    FunType(FunParam<'core, &'core Self>, &'core Self),
    FunLit(FunParam<'core, &'core Self>, &'core Self),
    FunApp(&'core Self, FunArg<&'core Self>),
}

impl<'core> Expr<'core> {
    pub const TYPE: Self = Self::PrimVar(PrimVar::Type);
    pub const BOOL: Self = Self::PrimVar(PrimVar::Bool);
    pub const INT: Self = Self::PrimVar(PrimVar::Int);
    pub const STRING: Self = Self::PrimVar(PrimVar::String);
    pub const CHAR: Self = Self::PrimVar(PrimVar::Char);
    pub const UNIT_TYPE: Self = Self::PrimVar(PrimVar::Unit);
    pub const UNIT_VALUE: Self = Self::PrimVar(PrimVar::unit);
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
