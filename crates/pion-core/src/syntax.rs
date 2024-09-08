use crate::env::{AbsoluteVar, RelativeVar};
use crate::prim::PrimVar;

#[derive(Debug, Copy, Clone)]
pub enum Expr<'core> {
    Error,

    Bool(bool),
    Int(u32),
    Char(char),
    String(&'core str),

    PrimVar(PrimVar),
    LocalVar(RelativeVar),
    MetaVar(AbsoluteVar),

    Let {
        r#type: &'core Self,
        rhs: &'core Self,
        body: &'core Self,
    },

    FunType {
        param: FunParam<&'core Self>,
        body: &'core Self,
    },
    FunLit {
        param: FunParam<&'core Self>,
        body: &'core Self,
    },
    FunApp {
        fun: &'core Self,
        arg: FunArg<&'core Self>,
    },
}

#[derive(Debug, Copy, Clone)]
pub struct FunParam<T> {
    pub plicity: Plicity,
    pub r#type: T,
}

impl<T> FunParam<T> {
    pub const fn new(plicity: Plicity, r#type: T) -> Self { Self { plicity, r#type } }
    pub const fn explicit(r#type: T) -> Self { Self::new(Plicity::Explicit, r#type) }
    pub const fn implicit(r#type: T) -> Self { Self::new(Plicity::Implicit, r#type) }
}

#[derive(Debug, Copy, Clone)]
pub struct FunArg<T> {
    pub plicity: Plicity,
    pub expr: T,
}

impl<T> FunArg<T> {
    pub const fn new(plicity: Plicity, expr: T) -> Self { Self { plicity, expr } }
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
