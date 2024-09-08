use core::fmt;

use pion_interner::InternedStr;

use crate::env::{AbsoluteVar, RelativeVar};
use crate::prim::PrimVar;
use crate::semantics::Value;

#[derive(Clone, PartialEq, Eq)]
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
        binding: LetBinding<'core, &'core Self>,
        body: &'core Self,
    },

    FunType {
        param: FunParam<'core, &'core Self>,
        body: &'core Self,
    },
    FunLit {
        param: FunParam<'core, &'core Self>,
        body: &'core Self,
    },
    FunApp {
        fun: &'core Self,
        arg: FunArg<&'core Self>,
    },
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct LetBinding<'core, T> {
    pub name: Option<InternedStr<'core>>,
    pub r#type: T,
    pub rhs: T,
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

#[derive(Debug, Clone, PartialEq, Eq)]
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

impl<'core> fmt::Debug for Expr<'core> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Error => write!(f, "Error"),
            Self::Bool(b) => fmt::Debug::fmt(b, f),
            Self::Int(n) => fmt::Debug::fmt(n, f),
            Self::Char(c) => fmt::Debug::fmt(c, f),
            Self::String(s) => fmt::Debug::fmt(s, f),
            Self::PrimVar(var) => f.debug_tuple("PrimVar").field(var).finish(),
            Self::LocalVar(var) => f.debug_tuple("LocalVar").field(&usize::from(*var)).finish(),
            Self::MetaVar(var) => f.debug_tuple("MetaVar").field(&usize::from(*var)).finish(),
            Self::Let { binding, body } => f
                .debug_struct("Let")
                .field("binding", binding)
                .field("body", body)
                .finish(),
            Self::FunType { param, body } => {
                f.debug_tuple("forall").field(param).finish()?;
                write!(f, " ")?;
                fmt::Debug::fmt(body, f)?;
                Ok(())
            }
            Self::FunLit { param, body } => {
                f.debug_tuple("fun").field(param).finish()?;
                write!(f, " ")?;
                fmt::Debug::fmt(body, f)?;
                Ok(())
            }
            Self::FunApp { fun, arg } => f
                .debug_struct("FunApp")
                .field("fun", fun)
                .field("arg", arg)
                .finish(),
        }
    }
}

impl<'core> fmt::Debug for Value<'core> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Error => write!(f, "Error"),
            Self::Bool(b) => fmt::Debug::fmt(b, f),
            Self::Int(n) => fmt::Debug::fmt(n, f),
            Self::Char(c) => fmt::Debug::fmt(c, f),
            Self::String(s) => fmt::Debug::fmt(s, f),
            Self::Neutral(head, spine) if spine.is_empty() => fmt::Debug::fmt(head, f),
            Self::Neutral(head, spine) => {
                f.debug_tuple("Neutral").field(head).field(spine).finish()
            }
            Self::FunType { param, body } => {
                f.debug_tuple("forall").field(param).finish()?;
                write!(f, " ")?;
                fmt::Debug::fmt(body, f)?;
                Ok(())
            }
            Self::FunLit { param, body } => {
                f.debug_tuple("fun").field(param).finish()?;
                write!(f, " ")?;
                fmt::Debug::fmt(body, f)?;
                Ok(())
            }
        }
    }
}
