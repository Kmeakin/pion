use core::fmt;

use crate::env::DeBruijnIndex;
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

    Eq = "Eq",
    refl = "refl",
    subst = "subst",
});

impl fmt::Debug for PrimVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{}", self.name()) }
}

impl fmt::Display for PrimVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { fmt::Debug::fmt(&self, f) }
}

impl PrimVar {
    #[rustfmt::skip]
    pub const fn r#type(&self) -> Type<'static> {
        const VAR0: Expr = Expr::LocalVar(LocalVar::new(None, DeBruijnIndex::new(0)));
        const VAR1: Expr = Expr::LocalVar(LocalVar::new(None, DeBruijnIndex::new(1)));
        const VAR2: Expr = Expr::LocalVar(LocalVar::new(None, DeBruijnIndex::new(2)));
        const VAR3: Expr = Expr::LocalVar(LocalVar::new(None, DeBruijnIndex::new(3)));
        const VAR4: Expr = Expr::LocalVar(LocalVar::new(None, DeBruijnIndex::new(4)));

        match self {
            // `Type: Type`
            // `Bool: Type`
            // `Int: Type`
            // `Char: Type`
            // `String: Type`
            // `Unit: Type`
            Self::Type | Self::Bool | Self::Int | Self::Char | Self::String | Self::Unit => Type::TYPE,

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

            // `Eq: forall(@A: Type) -> A -> A -> Type``
            Self::Eq => Type::FunType(
                FunParam::implicit(None, const { &Type::TYPE }),
                Closure::empty(
                    &const {
                        Expr::FunType(
                            FunParam::explicit(None, &VAR0),
                            &const { Expr::FunType(FunParam::explicit(None, &VAR1), &Expr::TYPE) },
                        )
                    },
                ),
            ),

            // `refl: forall(@A: Type, a: A) -> Eq(@A, a, a)`
            Self::refl => Type::FunType(
                FunParam::implicit(None, const { &Type::TYPE }),
                Closure::empty(
                    &const {
                        Expr::FunType(
                            FunParam::explicit(None, &VAR0),
                            &const {
                                Expr::FunApp(
                                    &const {
                                        Expr::FunApp(
                                            &const { Expr::FunApp(&Expr::PrimVar(Self::Eq), FunArg::implicit(&VAR1)) },
                                            FunArg::explicit(&VAR0),
                                        )
                                    },
                                    FunArg::explicit(&VAR0),
                                )
                            },
                        )
                    },
                ),
            ),

            // `subst: forall(@A: Type, @p: A -> Type, @a: A, @b: A) -> Eq(@A, a, b) -> p(a) -> p(b)`
            Self::subst => Type::FunType(
                FunParam::implicit(None, const { &Type::TYPE }),
                Closure::empty(
                    &const {
                        Expr::FunType(
                            FunParam::implicit(None, &const { Expr::FunType(FunParam::explicit(None, &VAR0), &Expr::TYPE) }),
                            &const {
                                Expr::FunType(
                                    FunParam::explicit(None, &VAR1),
                                    &const {
                                        Expr::FunType(
                                            FunParam::explicit(None, &VAR2),
                                            &const {
                                                Expr::FunType(
                                                    FunParam::explicit(
                                                        None,
                                                        &const {
                                                            Expr::FunApp(
                                                                &const {
                                                                    Expr::FunApp(
                                                                        &const { Expr::FunApp(&Expr::PrimVar(Self::Eq), FunArg::implicit(&VAR3)) },
                                                                        FunArg::explicit(&VAR1),
                                                                    )
                                                                },
                                                                FunArg::explicit(&VAR0),
                                                            )
                                                        },
                                                    ),
                                                    &const {
                                                        Expr::FunType(
                                                            FunParam::explicit(None, &const { Expr::FunApp(&VAR3, FunArg::explicit(&VAR2)) }),
                                                            &const { Expr::FunApp(&VAR4, FunArg::explicit(&VAR2)) },
                                                        )
                                                    },
                                                )
                                            },
                                        )
                                    },
                                )
                            },
                        )
                    },
                ),
            ),
        }
    }
}
