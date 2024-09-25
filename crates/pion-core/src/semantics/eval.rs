use super::*;

/// Evaluate an `Expr` to a `Value`.
/// Does not reduce under `fun` or `forall`
pub fn eval<'core, 'env>(
    expr: &Expr<'core>,
    opts: UnfoldOpts,
    locals: &'env mut LocalValues<'core>,
    metas: &'env MetaValues<'core>,
) -> Result<Value<'core>, Error<'core>> {
    match expr {
        Expr::Error => Ok(Value::ERROR),

        Expr::Bool(b) => Ok(Value::Bool(*b)),
        Expr::Int(x) => Ok(Value::Int(*x)),
        Expr::Char(c) => Ok(Value::Char(*c)),
        Expr::String(s) => Ok(Value::String(s)),

        Expr::PrimVar(var) => Ok(Value::prim_var(*var)),

        Expr::LocalVar(var) => match locals.get_relative(*var) {
            None => Err(Error::EvalUnboundLocalVar {
                var: *var,
                len: locals.len(),
            }),
            Some(value) => Ok(value.clone()),
        },
        Expr::MetaVar(var) => match metas.get_absolute(*var) {
            None => Err(Error::UnboundMetaVar {
                var: *var,
                len: metas.len(),
            }),
            Some(Some(value)) => Ok(value.clone()),
            Some(None) => Ok(Value::meta_var(*var)),
        },
        Expr::Let(binding, body) => {
            let rhs = eval(binding.init, opts, locals, metas)?;
            locals.push(rhs);
            let body = eval(body, opts, locals, metas);
            locals.pop();
            body
        }
        Expr::FunType(param, body) => {
            let body = Closure::new(locals.clone(), body);
            Ok(Value::FunType(*param, body))
        }
        Expr::FunLit(param, body) => {
            let body = Closure::new(locals.clone(), body);
            Ok(Value::FunLit(*param, body))
        }
        Expr::FunApp(fun, arg) => {
            let fun = eval(fun, opts, locals, metas)?;
            let arg_expr = eval(arg.expr, opts, locals, metas)?;
            let arg = FunArg::new(arg.plicity, arg_expr);
            elim::apply(fun, arg, opts, metas)
        }
    }
}

#[cfg(test)]
mod tests {
    use ecow::eco_vec;

    use super::*;
    use crate::env::UniqueEnv;
    use crate::syntax::LetBinding;

    #[track_caller]
    #[allow(clippy::needless_pass_by_value, reason = "It's only a test")]
    fn assert_eval(expr: Expr, expected: Result<Value, Error>) {
        let mut local_values = LocalValues::default();
        let meta_values = UniqueEnv::default();
        let value = eval(
            &expr,
            UnfoldOpts::for_eval(),
            &mut local_values,
            &meta_values,
        );
        assert_eq!(value, expected);
    }

    #[test]
    fn eval_error() { assert_eval(Expr::Error, Ok(Value::ERROR)); }

    #[test]
    fn eval_lit() {
        assert_eval(Expr::Int(10), Ok(Value::Int(10)));
        assert_eval(Expr::Char('a'), Ok(Value::Char('a')));
    }

    #[test]
    fn eval_let() {
        assert_eval(
            Expr::Let(
                LetBinding {
                    name: None,
                    r#type: &Expr::Error,
                    init: &Expr::Int(10),
                },
                &Expr::LocalVar(RelativeVar::new(0)),
            ),
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
            Expr::Let(
                LetBinding {
                    name: None,
                    r#type: &Expr::Error,
                    init: &Expr::Int(10),
                },
                &Expr::LocalVar(RelativeVar::new(1)),
            ),
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
            Err(Error::UnboundMetaVar {
                var: AbsoluteVar::new(0),
                len: EnvLen::new(0),
            }),
        );
    }

    #[test]
    fn eval_fun_app_beta_reduction() {
        let body = Expr::LocalVar(RelativeVar::new(0));
        let fun = Expr::FunLit(FunParam::explicit(None, &Expr::Error), &body);
        let arg = FunArg::explicit(&Expr::Int(10));
        let expr = Expr::FunApp(&fun, arg);
        assert_eval(expr, Ok(Value::Int(10)));
    }

    #[test]
    fn eval_fun_app_plicity_mismatch() {
        let body = Expr::LocalVar(RelativeVar::new(0));
        let fun = Expr::FunLit(FunParam::implicit(None, &Expr::Error), &body);
        let arg = FunArg::explicit(&Expr::Int(10));
        let expr = Expr::FunApp(&fun, arg);
        assert_eval(
            expr,
            Err(Error::FunAppPlicityMismatch {
                param_plicity: Plicity::Implicit,
                arg_plicity: Plicity::Explicit,
            }),
        );

        let body = Expr::LocalVar(RelativeVar::new(0));
        let fun = Expr::FunLit(FunParam::explicit(None, &Expr::Error), &body);
        let arg = FunArg::implicit(&Expr::Int(10));
        let expr = Expr::FunApp(&fun, arg);
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
        let expr = Expr::FunApp(&fun, arg);
        assert_eval(
            expr,
            Err(Error::CalleeNotFun {
                callee: Value::Char('a'),
            }),
        );
    }

    #[test]
    fn eval_fun_app_error_head() {
        let fun = Expr::Error;
        let arg = FunArg::explicit(&Expr::Int(10));
        let expr = Expr::FunApp(&fun, arg);
        assert_eval(
            expr,
            Ok(Value::Neutral(
                Head::Error,
                eco_vec![Elim::FunApp(FunArg::explicit(Value::Int(10)))],
            )),
        );
    }
}
