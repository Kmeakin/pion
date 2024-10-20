use core::fmt;

use crate::env::DeBruijnIndex;
use crate::semantics::{Closure, Type};
use crate::symbol::{sym, Symbol};
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
    eq = "eq",
    ne = "ne",
    lt = "lt",
    gt = "gt",
    le = "le",
    ge = "ge",

    Eq = "Eq",
    refl = "refl",
    subst = "subst",

    fix = "fix",
    bool_rec = "bool_rec",
});

impl fmt::Debug for PrimVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{}", self.name()) }
}

impl fmt::Display for PrimVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { fmt::Debug::fmt(&self, f) }
}

impl PrimVar {
    pub const fn r#type(&self) -> Type<'static> {
        pub const fn var(name: Option<Symbol<'static>>, index: usize) -> Expr<'static> {
            Expr::LocalVar(LocalVar::new(name, DeBruijnIndex::new(index)))
        }

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

            // `eq: Int -> Int -> Bool`
            // `ne: Int -> Int -> Bool`
            // `lt: Int -> Int -> Bool`
            // `gt: Int -> Int -> Bool`
            // `le: Int -> Int -> Bool`
            // `ge: Int -> Int -> Bool`
            Self::eq | Self::ne | Self::lt | Self::gt | Self::le | Self::ge => Type::FunType(
                FunParam::explicit(None, const { &Type::INT }),
                Closure::empty(
                    const { &Expr::FunType(FunParam::explicit(None, &Expr::INT), &Expr::BOOL) },
                ),
            ),

            // `Eq: forall(@A: Type) -> A -> A -> Type``
            Self::Eq => Type::FunType(
                FunParam::implicit(Some(sym::A), const { &Type::TYPE }),
                Closure::empty(
                    &const {
                        Expr::FunType(
                            FunParam::explicit(Some(sym::A), &const { var(Some(sym::A), 0) }),
                            &const {
                                Expr::FunType(
                                    FunParam::explicit(
                                        Some(sym::A),
                                        &const { var(Some(sym::A), 1) },
                                    ),
                                    &Expr::TYPE,
                                )
                            },
                        )
                    },
                ),
            ),

            // `refl: forall(@A: Type, a: A) -> Eq(@A, a, a)`
            Self::refl => Type::FunType(
                FunParam::implicit(Some(sym::A), const { &Type::TYPE }),
                Closure::empty(
                    &const {
                        Expr::FunType(
                            FunParam::explicit(Some(sym::a), &const { var(Some(sym::A), 0) }),
                            &const {
                                Expr::FunApp(
                                    &const {
                                        Expr::FunApp(
                                            &const {
                                                Expr::FunApp(
                                                    &Expr::PrimVar(Self::Eq),
                                                    FunArg::implicit(
                                                        &const { var(Some(sym::A), 1) },
                                                    ),
                                                )
                                            },
                                            FunArg::explicit(&const { var(Some(sym::a), 0) }),
                                        )
                                    },
                                    FunArg::explicit(&const { var(Some(sym::a), 0) }),
                                )
                            },
                        )
                    },
                ),
            ),

            // `subst: forall(@A: Type, @p: A -> Type, @a: A, @b: A) -> Eq(@A, a, b) -> p(a) ->
            // p(b)`
            Self::subst => Type::FunType(
                FunParam::implicit(Some(sym::A), const { &Type::TYPE }),
                Closure::empty(
                    &const {
                        Expr::FunType(
                            FunParam::implicit(
                                Some(sym::p),
                                &const {
                                    Expr::FunType(
                                        FunParam::explicit(None, &const { var(Some(sym::A), 0) }),
                                        &Expr::TYPE,
                                    )
                                },
                            ),
                            &const {
                                Expr::FunType(
                                    FunParam::implicit(
                                        Some(sym::a),
                                        &const { var(Some(sym::A), 1) },
                                    ),
                                    &const {
                                        Expr::FunType(
                                            FunParam::implicit(
                                                Some(sym::b),
                                                &const { var(Some(sym::A), 2) },
                                            ),
                                            &const {
                                                Expr::FunType(
                                                    FunParam::explicit(
                                                        None,
                                                        &const {
                                                            Expr::FunApp(
                                                                &const {
                                                                    Expr::FunApp(
                                                                        &const {
                                                                            Expr::FunApp(
                                                                                &Expr::PrimVar(
                                                                                    Self::Eq,
                                                                                ),
                                                                                FunArg::implicit(
                                                                                    &const {
                                                                                        var(Some(sym::A), 3)
                                                                                    },
                                                                                ),
                                                                            )
                                                                        },
                                                                        FunArg::explicit(
                                                                            &const {
                                                                                var(Some(sym::a), 1)
                                                                            },
                                                                        ),
                                                                    )
                                                                },
                                                                FunArg::explicit(
                                                                    &const { var(Some(sym::b), 0) },
                                                                ),
                                                            )
                                                        },
                                                    ),
                                                    &const {
                                                        Expr::FunType(
                                                            FunParam::explicit(
                                                                None,
                                                                &const {
                                                                    Expr::FunApp(
                                                                        &const { var(Some(sym::p), 3) },
                                                                        FunArg::explicit(
                                                                            &const {
                                                                                var(Some(sym::a), 2)
                                                                            },
                                                                        ),
                                                                    )
                                                                },
                                                            ),
                                                            &const {
                                                                Expr::FunApp(
                                                                    &const { var(Some(sym::p), 4) },
                                                                    FunArg::explicit(
                                                                        &const { var(Some(sym::b), 2) },
                                                                    ),
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
                        )
                    },
                ),
            ),

            // `fix: forall (@A : Type) (@B : Type) -> ((A -> B) -> A -> B) -> A -> B`
            Self::fix => Type::FunType(
                FunParam::implicit(Some(sym::A), const { &Type::TYPE }),
                Closure::empty(
                    &const {
                        Expr::FunType(
                            FunParam::implicit(Some(sym::B), &Expr::TYPE),
                            &const {
                                Expr::FunType(
                                    FunParam::explicit(
                                        None,
                                        // ((A -> B) -> A -> B)
                                        &const {
                                            Expr::FunType(
                                                FunParam::explicit(
                                                    None, // (A -> B)
                                                    &const {
                                                        Expr::FunType(
                                                            FunParam::explicit(
                                                                None,
                                                                &const { var(None, 1) },
                                                            ),
                                                            &const { var(None, 1) },
                                                        )
                                                    },
                                                ),
                                                &const {
                                                    Expr::FunType(
                                                        FunParam::explicit(
                                                            None,
                                                            &const { var(None, 2) },
                                                        ),
                                                        &const { var(None, 2) },
                                                    )
                                                },
                                            )
                                        },
                                    ),
                                    &const {
                                        Expr::FunType(
                                            FunParam::explicit(None, &const { var(None, 2) }),
                                            &const { var(None, 2) },
                                        )
                                    },
                                )
                            },
                        )
                    },
                ),
            ),

            // bool_rec : forall (@p: Bool -> Type) (b: Bool) -> p true -> p false -> p b
            Self::bool_rec => {
                const P: &Type = &Type::FunType(
                    FunParam::explicit(None, const { &Type::BOOL }),
                    Closure::empty(&Expr::TYPE),
                );

                Type::FunType(
                    FunParam::implicit(Some(sym::p), P),
                    Closure::empty(
                        &const {
                            Expr::FunType(
                                FunParam::explicit(Some(sym::b), &Expr::BOOL),
                                &const {
                                    Expr::FunType(
                                        FunParam::explicit(
                                            None,
                                            &const {
                                                Expr::FunApp(
                                                    &const { var(None, 1) },
                                                    FunArg::explicit(&const { Expr::bool(true) }),
                                                )
                                            },
                                        ),
                                        &const {
                                            Expr::FunType(
                                                FunParam::explicit(
                                                    None,
                                                    &const {
                                                        Expr::FunApp(
                                                            &const { var(None, 2) },
                                                            FunArg::explicit(
                                                                &const { Expr::bool(false) },
                                                            ),
                                                        )
                                                    },
                                                ),
                                                &const {
                                                    Expr::FunApp(
                                                        &const { var(None, 3) },
                                                        FunArg::explicit(&const { var(None, 2) }),
                                                    )
                                                },
                                            )
                                        },
                                    )
                                },
                            )
                        },
                    ),
                )
            }
        }
    }
}
