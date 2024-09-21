use ecow::EcoVec;

use crate::env::{AbsoluteVar, EnvLen, RelativeVar, SharedEnv, SliceEnv};
use crate::prim::PrimVar;
use crate::syntax::{Expr, FunArg, FunParam, Plicity};

pub type LocalValues<'core> = SharedEnv<Value<'core>>;
pub type MetaValues<'core> = SliceEnv<Option<Value<'core>>>;

pub type Type<'core> = Value<'core>;

#[derive(Clone, PartialEq, Eq)]
pub enum Value<'core> {
    Error,

    Bool(bool),
    Int(u32),
    Char(char),
    String(&'core str),

    Neutral(Head, EcoVec<Elim<'core>>),

    FunType {
        param: FunParam<'core, &'core Expr<'core>>,
        body: Closure<'core>,
    },
    FunLit {
        param: FunParam<'core, &'core Expr<'core>>,
        body: Closure<'core>,
    },
}

impl<'core> Value<'core> {
    pub const TYPE: Self = Self::prim_var(PrimVar::Type);
    pub const BOOL: Self = Self::prim_var(PrimVar::Bool);
    pub const INT: Self = Self::prim_var(PrimVar::Int);
    pub const STRING: Self = Self::prim_var(PrimVar::String);
    pub const CHAR: Self = Self::prim_var(PrimVar::Char);

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
pub struct EvalOpts {
    pub unfold_fix: bool,
}

impl EvalOpts {
    pub const fn for_eval() -> Self { Self { unfold_fix: true } }
    pub const fn for_quote() -> Self { Self { unfold_fix: false } }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error<'core> {
    EvalUnboundLocalVar {
        var: RelativeVar,
        len: EnvLen,
    },
    QuoteUnboundLocalVar {
        var: AbsoluteVar,
        len: EnvLen,
    },
    EvalUnboundMetaVar {
        var: AbsoluteVar,
        len: EnvLen,
    },

    FunAppPlicityMismatch {
        param_plicity: Plicity,
        arg_plicity: Plicity,
    },
    FunAppHeadNotFun {
        head: Value<'core>,
    },
}

pub mod equality {
    use super::*;
    use crate::syntax::LetBinding;

    pub trait AlphaEq {
        fn alpha_eq(&self, other: &Self) -> bool;
    }

    impl<'a, T: AlphaEq> AlphaEq for &'a T {
        fn alpha_eq(&self, other: &Self) -> bool { T::alpha_eq(self, other) }
    }

    impl<'core> AlphaEq for Value<'core> {
        fn alpha_eq(&self, other: &Self) -> bool {
            let (lhs, rhs) = (self, other);
            if std::ptr::eq(lhs, rhs) {
                return true;
            }

            match (lhs, rhs) {
                (Value::Error, Value::Error) => true,
                (Value::Bool(lhs), Value::Bool(rhs)) => lhs == rhs,
                (Value::Int(lhs), Value::Int(rhs)) => lhs == rhs,
                (Value::Char(lhs), Value::Char(rhs)) => lhs == rhs,
                (Value::String(lhs), Value::String(rhs)) => lhs == rhs,
                (Value::Neutral(lhs_head, lhs_spine), Value::Neutral(rhs_head, rhs_spine)) => {
                    lhs_head == rhs_head
                        && lhs_spine.len() == rhs_spine.len()
                        && lhs_spine
                            .iter()
                            .zip(rhs_spine.iter())
                            .all(|(lhs, rhs)| lhs.alpha_eq(rhs))
                }
                (
                    Value::FunType {
                        param: lhs_param,
                        body: lhs_body,
                    },
                    Value::FunType {
                        param: rhs_param,
                        body: rhs_body,
                    },
                )
                | (
                    Value::FunLit {
                        param: lhs_param,
                        body: lhs_body,
                    },
                    Value::FunLit {
                        param: rhs_param,
                        body: rhs_body,
                    },
                ) => lhs_param.r#type.alpha_eq(rhs_param.r#type) && lhs_body.alpha_eq(rhs_body),

                _ => false,
            }
        }
    }

    impl<'core> AlphaEq for Expr<'core> {
        fn alpha_eq(&self, other: &Self) -> bool {
            let (lhs, rhs) = (self, other);
            if std::ptr::eq(lhs, rhs) {
                return true;
            }

            match (lhs, rhs) {
                (Expr::Error, Expr::Error) => true,
                (Expr::Bool(lhs), Expr::Bool(rhs)) => lhs == rhs,
                (Expr::Int(lhs), Expr::Int(rhs)) => lhs == rhs,
                (Expr::Char(lhs), Expr::Char(rhs)) => lhs == rhs,
                (Expr::String(lhs), Expr::String(rhs)) => lhs == rhs,

                (Expr::PrimVar(lhs), Expr::PrimVar(rhs)) => lhs == rhs,
                (Expr::LocalVar(lhs), Expr::LocalVar(rhs)) => lhs == rhs,
                (Expr::MetaVar(lhs), Expr::MetaVar(rhs)) => lhs == rhs,

                (
                    Expr::Let {
                        binding: lhs_binding,
                        body: lhs_body,
                    },
                    Expr::Let {
                        binding: rhs_binding,
                        body: rhs_body,
                    },
                ) => lhs_binding.alpha_eq(rhs_binding) && lhs_body.alpha_eq(rhs_body),

                (
                    Expr::FunType {
                        param: lhs_param,
                        body: lhs_body,
                    },
                    Expr::FunType {
                        param: rhs_param,
                        body: rhs_body,
                    },
                )
                | (
                    Expr::FunLit {
                        param: lhs_param,
                        body: lhs_body,
                    },
                    Expr::FunLit {
                        param: rhs_param,
                        body: rhs_body,
                    },
                ) => lhs_param.alpha_eq(rhs_param) && lhs_body.alpha_eq(rhs_body),

                (
                    Expr::FunApp {
                        fun: lhs_fun,
                        arg: lhs_arg,
                    },
                    Expr::FunApp {
                        fun: rhs_fun,
                        arg: rhs_arg,
                    },
                ) => lhs_fun.alpha_eq(rhs_fun) && lhs_arg.alpha_eq(rhs_arg),

                _ => false,
            }
        }
    }

    impl<'core, T: AlphaEq> AlphaEq for LetBinding<'core, T> {
        fn alpha_eq(&self, other: &Self) -> bool {
            self.r#type.alpha_eq(&other.r#type) && self.rhs.alpha_eq(&other.rhs)
        }
    }

    impl<'core, T: AlphaEq> AlphaEq for FunParam<'core, T> {
        fn alpha_eq(&self, other: &Self) -> bool {
            let (lhs, rhs) = (self, other);
            lhs.plicity == rhs.plicity && lhs.r#type.alpha_eq(&rhs.r#type)
        }
    }

    impl<T: AlphaEq> AlphaEq for FunArg<T> {
        fn alpha_eq(&self, other: &Self) -> bool {
            let (lhs, rhs) = (self, other);
            lhs.plicity == rhs.plicity && lhs.expr.alpha_eq(&rhs.expr)
        }
    }

    impl<'core> AlphaEq for Closure<'core> {
        // FIXME: is this correct?
        fn alpha_eq(&self, other: &Self) -> bool { self.body.alpha_eq(other.body) }
    }

    impl AlphaEq for Head {
        fn alpha_eq(&self, other: &Self) -> bool { self == other }
    }

    impl<'core> AlphaEq for Elim<'core> {
        fn alpha_eq(&self, other: &Self) -> bool {
            let (lhs, rhs) = (self, other);
            match (lhs, rhs) {
                (Elim::FunApp(lhs), Elim::FunApp(rhs)) => lhs.alpha_eq(rhs),
            }
        }
    }
}

pub fn eval<'core, 'env>(
    expr: &Expr<'core>,
    opts: EvalOpts,
    local_values: &'env mut LocalValues<'core>,
    meta_values: &'env MetaValues<'core>,
) -> Result<Value<'core>, Error<'core>> {
    match expr {
        Expr::Error => Ok(Value::Error),

        Expr::Bool(b) => Ok(Value::Bool(*b)),
        Expr::Int(x) => Ok(Value::Int(*x)),
        Expr::Char(c) => Ok(Value::Char(*c)),
        Expr::String(s) => Ok(Value::String(s)),

        Expr::PrimVar(prim) => Ok(Value::Neutral(Head::PrimVar(*prim), EcoVec::new())),

        Expr::LocalVar(var) => match local_values.get_relative(*var) {
            None => Err(Error::EvalUnboundLocalVar {
                var: *var,
                len: local_values.len(),
            }),
            Some(value) => Ok(value.clone()),
        },
        Expr::MetaVar(var) => match meta_values.get_absolute(*var) {
            None => Err(Error::EvalUnboundMetaVar {
                var: *var,
                len: meta_values.len(),
            }),
            Some(Some(value)) => Ok(value.clone()),
            Some(None) => Ok(Value::meta_var(*var)),
        },
        Expr::Let { binding, body } => {
            let rhs = eval(binding.rhs, opts, local_values, meta_values)?;
            local_values.push(rhs);
            let body = eval(body, opts, local_values, meta_values);
            local_values.pop();
            body
        }
        Expr::FunType { param, body } => {
            let body = Closure::new(local_values.clone(), body);
            Ok(Value::FunType {
                param: *param,
                body,
            })
        }
        Expr::FunLit { param, body } => {
            let body = Closure::new(local_values.clone(), body);
            Ok(Value::FunLit {
                param: *param,
                body,
            })
        }
        Expr::FunApp { fun, arg } => {
            let fun = eval(fun, opts, local_values, meta_values)?;
            let arg_expr = eval(arg.expr, opts, local_values, meta_values)?;
            let arg = FunArg::new(arg.plicity, arg_expr);
            fun_app(fun, arg, opts, meta_values)
        }
    }
}

pub fn fun_app<'core>(
    fun: Value<'core>,
    arg: FunArg<Value<'core>>,
    opts: EvalOpts,
    meta_values: &MetaValues<'core>,
) -> Result<Value<'core>, Error<'core>> {
    match fun {
        Value::Error => Ok(Value::Error),
        Value::Neutral(head, mut spine) => {
            spine.push(Elim::FunApp(arg));
            Ok(Value::Neutral(head, spine))
        }
        Value::FunLit { param, body: _ } if param.plicity != arg.plicity => {
            Err(Error::FunAppPlicityMismatch {
                param_plicity: param.plicity,
                arg_plicity: arg.plicity,
            })
        }
        Value::FunLit { param: _, body } => apply_closure(body, arg.expr, opts, meta_values),
        _ => Err(Error::FunAppHeadNotFun { head: fun }),
    }
}

pub fn apply_closure<'core>(
    closure: Closure<'core>,
    arg: Value<'core>,
    opts: EvalOpts,
    meta_values: &MetaValues<'core>,
) -> Result<Value<'core>, Error<'core>> {
    let Closure {
        mut local_values,
        body,
    } = closure;
    local_values.push(arg);
    eval(body, opts, &mut local_values, meta_values)
}

pub fn quote<'core>(
    value: &Value<'core>,
    bump: &'core bumpalo::Bump,
    local_len: EnvLen,
    meta_values: &MetaValues<'core>,
) -> Result<Expr<'core>, Error<'core>> {
    match value {
        Value::Error => Ok(Expr::Error),

        Value::Bool(b) => Ok(Expr::Bool(*b)),
        Value::Int(x) => Ok(Expr::Int(*x)),
        Value::Char(c) => Ok(Expr::Char(*c)),
        Value::String(s) => Ok(Expr::String(s)),

        Value::Neutral(head, spine) => {
            let head = quote_head(*head, bump, local_len, meta_values)?;
            spine.iter().try_fold(head, |head, elim| match elim {
                Elim::FunApp(arg) => {
                    let arg_expr = quote(&arg.expr, bump, local_len, meta_values)?;
                    let (fun, arg_expr) = bump.alloc((head, arg_expr));
                    let arg = FunArg::new(arg.plicity, &*arg_expr);
                    Ok(Expr::FunApp { fun, arg })
                }
            })
        }
        Value::FunType { param, body } => {
            let (param, body) = quote_fun(*param, body, bump, local_len, meta_values)?;
            Ok(Expr::FunType { param, body })
        }
        Value::FunLit { param, body } => {
            let (param, body) = quote_fun(*param, body, bump, local_len, meta_values)?;
            Ok(Expr::FunLit { param, body })
        }
    }
}

fn quote_head<'core>(
    head: Head,
    bump: &'core bumpalo::Bump,
    local_len: EnvLen,
    meta_values: &MetaValues<'core>,
) -> Result<Expr<'core>, Error<'core>> {
    match head {
        Head::LocalVar(var) => match local_len.absolute_to_relative(var) {
            Some(var) => Ok(Expr::LocalVar(var)),
            None => Err(Error::QuoteUnboundLocalVar {
                var,
                len: local_len,
            }),
        },
        Head::MetaVar(var) => match meta_values.get_absolute(var) {
            Some(Some(value)) => quote(value, bump, local_len, meta_values),
            Some(None) => Ok(Expr::MetaVar(var)),
            None => Err(Error::EvalUnboundMetaVar {
                var,
                len: meta_values.len(),
            }),
        },
        Head::PrimVar(var) => Ok(Expr::PrimVar(var)),
    }
}

fn quote_fun<'core>(
    param: FunParam<'core, &'core Expr<'core>>,
    closure: &Closure<'core>,
    bump: &'core bumpalo::Bump,
    local_len: EnvLen,
    meta_values: &MetaValues<'core>,
) -> Result<(FunParam<'core, &'core Expr<'core>>, &'core Expr<'core>), Error<'core>> {
    let arg = Value::local_var(local_len.to_absolute());
    let body = apply_closure(closure.clone(), arg, EvalOpts::for_quote(), meta_values)?;
    let body = quote(&body, bump, local_len.succ(), meta_values)?;
    let body = bump.alloc(body);
    Ok((param, body))
}

pub fn update_metas<'core>(
    value: &Value<'core>,
    meta_values: &MetaValues<'core>,
) -> Result<Value<'core>, Error<'core>> {
    let mut value = value.clone();
    while let Value::Neutral(Head::MetaVar(var), spine) = value {
        match meta_values.get_absolute(var) {
            None => {
                return Err(Error::EvalUnboundMetaVar {
                    var,
                    len: meta_values.len(),
                })
            }
            Some(None) => return Ok(Value::Neutral(Head::MetaVar(var), spine)),
            Some(Some(head)) => {
                value = spine
                    .into_iter()
                    .try_fold(head.clone(), |head, elim| match elim {
                        Elim::FunApp(arg) => fun_app(head, arg, EvalOpts::for_quote(), meta_values),
                    })?;
            }
        }
    }
    Ok(value)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::UniqueEnv;
    use crate::syntax::LetBinding;

    #[track_caller]
    #[allow(clippy::needless_pass_by_value, reason = "It's only a test")]
    fn assert_eval(expr: Expr, expected: Result<Value, Error>) {
        let mut local_values = LocalValues::default();
        let meta_values = UniqueEnv::default();
        let value = eval(&expr, EvalOpts::for_eval(), &mut local_values, &meta_values);
        assert_eq!(value, expected);
    }

    #[track_caller]
    #[allow(clippy::needless_pass_by_value, reason = "It's only a test")]
    fn assert_quote(value: Value, expected: Result<Expr, Error>) {
        let bump = bumpalo::Bump::default();
        let local_len = EnvLen::default();
        let meta_values = UniqueEnv::default();

        let expr = quote(&value, &bump, local_len, &meta_values);
        assert_eq!(expr, expected);
    }

    #[test]
    fn eval_error() { assert_eval(Expr::Error, Ok(Value::Error)); }

    #[test]
    fn eval_lit() {
        assert_eval(Expr::Int(10), Ok(Value::Int(10)));
        assert_eval(Expr::Char('a'), Ok(Value::Char('a')));
    }

    #[test]
    fn eval_let() {
        assert_eval(
            Expr::Let {
                binding: LetBinding {
                    name: None,
                    r#type: &Expr::Error,
                    rhs: &Expr::Int(10),
                },
                body: &Expr::LocalVar(RelativeVar::new(0)),
            },
            Ok(Value::Int(10)),
        );
    }

    #[test]
    fn eval_unbound_local_var() {
        assert_eval(
            Expr::LocalVar(RelativeVar::new(0)),
            Err(Error::EvalUnboundLocalVar {
                var: RelativeVar::new(0),
                len: EnvLen::new(0),
            }),
        );

        assert_eval(
            Expr::Let {
                binding: LetBinding {
                    name: None,
                    r#type: &Expr::Error,
                    rhs: &Expr::Int(10),
                },
                body: &Expr::LocalVar(RelativeVar::new(1)),
            },
            Err(Error::EvalUnboundLocalVar {
                var: RelativeVar::new(1),
                len: EnvLen::new(1),
            }),
        );
    }

    #[test]
    fn eval_unbound_meta_var() {
        assert_eval(
            Expr::MetaVar(AbsoluteVar::new(0)),
            Err(Error::EvalUnboundMetaVar {
                var: AbsoluteVar::new(0),
                len: EnvLen::new(0),
            }),
        );
    }

    #[test]
    fn eval_fun_app_beta_reduction() {
        let fun = Expr::FunLit {
            param: FunParam::explicit(None, &Expr::Error),
            body: &Expr::LocalVar(RelativeVar::new(0)),
        };
        let arg = FunArg::explicit(&Expr::Int(10));
        let expr = Expr::FunApp { fun: &fun, arg };
        assert_eval(expr, Ok(Value::Int(10)));
    }

    #[test]
    fn eval_fun_app_plicity_mismatch() {
        let fun = Expr::FunLit {
            param: FunParam::implicit(None, &Expr::Error),
            body: &Expr::LocalVar(RelativeVar::new(0)),
        };
        let arg = FunArg::explicit(&Expr::Int(10));
        let expr = Expr::FunApp { fun: &fun, arg };
        assert_eval(
            expr,
            Err(Error::FunAppPlicityMismatch {
                param_plicity: Plicity::Implicit,
                arg_plicity: Plicity::Explicit,
            }),
        );

        let fun = Expr::FunLit {
            param: FunParam::explicit(None, &Expr::Error),
            body: &Expr::LocalVar(RelativeVar::new(0)),
        };
        let arg = FunArg::implicit(&Expr::Int(10));
        let expr = Expr::FunApp { fun: &fun, arg };
        assert_eval(
            expr,
            Err(Error::FunAppPlicityMismatch {
                param_plicity: Plicity::Explicit,
                arg_plicity: Plicity::Implicit,
            }),
        );
    }

    #[test]
    fn eval_fun_app_head_not_fun() {
        let fun = Expr::Char('a');
        let arg = FunArg::explicit(&Expr::Int(10));
        let expr = Expr::FunApp { fun: &fun, arg };
        assert_eval(
            expr,
            Err(Error::FunAppHeadNotFun {
                head: Value::Char('a'),
            }),
        );
    }

    #[test]
    fn eval_fun_app_error_head() {
        let fun = Expr::Error;
        let arg = FunArg::explicit(&Expr::Int(10));
        let expr = Expr::FunApp { fun: &fun, arg };
        assert_eval(expr, Ok(Value::Error));
    }

    #[test]
    fn quote_error() { assert_quote(Value::Error, Ok(Expr::Error)); }

    #[test]
    fn quote_lit() { assert_quote(Value::Int(10), Ok(Expr::Int(10))); }

    #[test]
    fn quote_fun_lit() {
        let body = Expr::LocalVar(RelativeVar::new(0));
        let fun = Value::FunLit {
            param: FunParam::explicit(None, &Expr::Error),
            body: Closure::empty(&body),
        };
        assert_quote(
            fun,
            Ok(Expr::FunLit {
                param: FunParam::explicit(None, &Expr::Error),
                body: &Expr::LocalVar(RelativeVar::new(0)),
            }),
        );
    }

    #[test]
    fn quote_fun_type() {
        let body = Expr::LocalVar(RelativeVar::new(0));
        let fun = Value::FunType {
            param: FunParam::explicit(None, &Expr::Error),
            body: Closure::empty(&body),
        };
        assert_quote(
            fun,
            Ok(Expr::FunType {
                param: FunParam::explicit(None, &Expr::Error),
                body: &Expr::LocalVar(RelativeVar::new(0)),
            }),
        );
    }
}
