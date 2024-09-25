use super::*;

/// Quote a value back to an expression.
pub fn quote<'core>(
    value: &Value<'core>,
    bump: &'core bumpalo::Bump,
    locals: EnvLen,
    metas: &MetaValues<'core>,
) -> Result<Expr<'core>, Error<'core>> {
    match value {
        Value::Bool(b) => Ok(Expr::Bool(*b)),
        Value::Int(x) => Ok(Expr::Int(*x)),
        Value::Char(c) => Ok(Expr::Char(*c)),
        Value::String(s) => Ok(Expr::String(s)),
        Value::Neutral(head, spine) => quote_neutral(*head, spine, bump, locals, metas),
        Value::FunType(param, body) => {
            let body = quote_closure(body, bump, locals, metas)?;
            Ok(Expr::FunType(*param, body))
        }
        Value::FunLit(param, body) => {
            let body = quote_closure(body, bump, locals, metas)?;
            Ok(Expr::FunLit(*param, body))
        }
    }
}

fn quote_head<'core>(
    head: Head,
    bump: &'core bumpalo::Bump,
    locals: EnvLen,
    metas: &MetaValues<'core>,
) -> Result<Expr<'core>, Error<'core>> {
    match head {
        Head::Error => Ok(Expr::Error),
        Head::LocalVar(var) => match locals.absolute_to_relative(var) {
            Some(var) => Ok(Expr::LocalVar(var)),
            None => Err(Error::QuoteUnboundLocalVar { var, len: locals }),
        },
        Head::MetaVar(var) => match metas.get_absolute(var) {
            Some(Some(value)) => quote(value, bump, locals, metas),
            Some(None) => Ok(Expr::MetaVar(var)),
            None => Err(Error::UnboundMetaVar {
                var,
                len: metas.len(),
            }),
        },
        Head::PrimVar(var) => Ok(Expr::PrimVar(var)),
    }
}

fn quote_neutral<'core>(
    head: Head,
    spine: &EcoVec<Elim<'core>>,
    bump: &'core bumpalo::Bump,
    locals: EnvLen,
    metas: &MetaValues<'core>,
) -> Result<Expr<'core>, Error<'core>> {
    let head = quote_head(head, bump, locals, metas)?;
    spine.iter().try_fold(head, |head, elim| match elim {
        Elim::FunApp(arg) => {
            let arg_expr = quote(&arg.expr, bump, locals, metas)?;
            let (fun, arg_expr) = bump.alloc((head, arg_expr));
            let arg = FunArg::new(arg.plicity, &*arg_expr);
            Ok(Expr::FunApp(fun, arg))
        }
    })
}

fn quote_closure<'core>(
    closure: &Closure<'core>,
    bump: &'core bumpalo::Bump,
    locals: EnvLen,
    metas: &MetaValues<'core>,
) -> Result<&'core Expr<'core>, Error<'core>> {
    let arg = Value::local_var(locals.to_absolute());
    let body = elim::beta_reduce(closure.clone(), arg, UnfoldOpts::for_quote(), metas)?;
    let body = quote(&body, bump, locals.succ(), metas)?;
    let body = bump.alloc(body);
    Ok(body)
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::env::UniqueEnv;

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
    fn quote_error() { assert_quote(Value::ERROR, Ok(Expr::Error)); }

    #[test]
    fn quote_lit() { assert_quote(Value::Int(10), Ok(Expr::Int(10))); }

    #[test]
    fn quote_fun_lit() {
        let body = Expr::LocalVar(RelativeVar::new(0));
        let fun = Value::FunLit(
            FunParam::explicit(None, &Expr::Error),
            Closure::empty(&body),
        );
        assert_quote(
            fun,
            Ok(Expr::FunLit(
                FunParam::explicit(None, &Expr::Error),
                &Expr::LocalVar(RelativeVar::new(0)),
            )),
        );
    }

    #[test]
    fn quote_fun_type() {
        let body = Expr::LocalVar(RelativeVar::new(0));
        let fun = Value::FunType(
            FunParam::explicit(None, &Expr::Error),
            Closure::empty(&body),
        );
        assert_quote(
            fun,
            Ok(Expr::FunType(
                FunParam::explicit(None, &Expr::Error),
                &Expr::LocalVar(RelativeVar::new(0)),
            )),
        );
    }
}