use core::fmt;

use crate::semantics::{Closure, Type};
use crate::syntax::*;

macro_rules! define_prims {
    ($name:ident { $($variant:ident = $value:literal $(,)?),* }) => {
        #[derive(Copy, Clone, PartialEq, Eq)]
        #[allow(non_camel_case_types,reason = "for consistency with the surface syntax")]
        pub enum $name {
            $($variant),*
        }

        impl std::str::FromStr for $name {
            type Err = ();

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                match s {
                    $($value => Ok(Self::$variant),)*
                    _ => Err(()),
                }
            }
        }

        impl $name {
            pub fn name(&self) -> &'static str {
                match self {
                    $(Self::$variant => $value,)*
                }
            }
        }
    };
}

define_prims!(PrimVar {
    Type = "Type",
    Bool = "Bool",
    Int = "Int",
    Char = "Char",
    String = "String",
    Unit = "Unit",
    unit = "unit",

    add = "add",
    sub = "sub",
    mul = "mul",
});

impl fmt::Debug for PrimVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{}", self.name()) }
}

impl fmt::Display for PrimVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { fmt::Debug::fmt(&self, f) }
}

impl PrimVar {
    pub const fn r#type(&self) -> Type<'static> {
        match self {
            // `Type: Type`
            // `Bool: Type`
            // `Int: Type`
            // `Char: Type`
            // `String: Type`
            // `Unit: Type`
            Self::Type | Self::Bool | Self::Int | Self::Char | Self::String | Self::Unit => {
                Type::TYPE
            }

            // `unit: Unit`
            Self::unit => Type::UNIT_TYPE,

            // `add: Int -> Int -> Int`
            // `sub: Int -> Int -> Int`
            // `mul: Int -> Int -> Int`
            Self::add | Self::sub | Self::mul => Type::FunType(
                FunParam::explicit(None, const { &Type::INT }),
                Closure::empty(
                    const { &Expr::FunType(FunParam::explicit(None, &Expr::INT), &Expr::INT) },
                ),
            ),
        }
    }
}
