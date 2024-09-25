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

/// Quote a `Closure` back to an `Expr`.
///
/// NOTE: We can't simply return `closure.expr`, because `closure.expr` could
/// reference a local variable in `closure.env`. We *could* convert the closure
/// environment back to series of nested `let`s, but that would produce very big
/// terms!
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

    use ecow::eco_vec;

    use super::*;
    use crate::env::UniqueEnv;

    #[track_caller]
    #[allow(clippy::needless_pass_by_value, reason = "It's only a test")]
    fn assert_quote_in_env(
        locals: EnvLen,
        metas: &MetaValues,
        value: Value,
        expected: Result<Expr, Error>,
    ) {
        let bump = bumpalo::Bump::default();
        let expr = quote(&value, &bump, locals, metas);
        assert_eq!(expr, expected);
    }

    #[track_caller]
    #[allow(clippy::needless_pass_by_value, reason = "It's only a test")]
    fn assert_quote(value: Value, expected: Result<Expr, Error>) {
        assert_quote_in_env(EnvLen::default(), &UniqueEnv::default(), value, expected);
    }

    #[test]
    fn quote_error() { assert_quote(Value::ERROR, Ok(Expr::Error)); }

    #[test]
    fn quote_bool() {
        assert_quote(Value::Bool(true), Ok(Expr::Bool(true)));
        assert_quote(Value::Bool(false), Ok(Expr::Bool(false)));
    }

    #[test]
    fn quote_int() { assert_quote(Value::Int(10), Ok(Expr::Int(10))); }

    #[test]
    fn quote_char() { assert_quote(Value::Char('a'), Ok(Expr::Char('a'))); }

    #[test]
    fn quote_string() { assert_quote(Value::String("hello"), Ok(Expr::String("hello"))); }

    #[test]
    fn quote_unbound_local_var() {
        let value = Value::local_var(AbsoluteVar::new(0));
        assert_quote(
            value,
            Err(Error::QuoteUnboundLocalVar {
                var: AbsoluteVar::new(0),
                len: EnvLen::new(0),
            }),
        );
    }

    #[test]
    fn quote_unbound_meta_var() {
        let value = Value::meta_var(AbsoluteVar::new(0));
        assert_quote(
            value,
            Err(Error::UnboundMetaVar {
                var: AbsoluteVar::new(0),
                len: EnvLen::new(0),
            }),
        );
    }

    #[test]
    fn quote_bound_meta_var() {
        let locals = EnvLen::default();
        let mut metas = UniqueEnv::new();
        metas.push(None);

        let value = Value::meta_var(AbsoluteVar::new(0));
        assert_quote_in_env(
            locals,
            &metas,
            value,
            Ok(Expr::MetaVar(AbsoluteVar::new(0))),
        );

        metas.push(Some(Value::Int(42)));
        let value = Value::meta_var(AbsoluteVar::new(1));
        assert_quote_in_env(locals, &metas, value, Ok(Expr::Int(42)));
    }

    #[test]
    fn quote_neutral() {
        let locals = EnvLen::default().succ();
        let metas = UniqueEnv::new();

        let value = Value::Neutral(
            Head::LocalVar(AbsoluteVar::new(0)),
            eco_vec![Elim::FunApp(FunArg::explicit(Value::Int(42)))],
        );

        assert_quote_in_env(
            locals,
            &metas,
            value,
            Ok(Expr::FunApp(
                &Expr::LocalVar(RelativeVar::new(0)),
                FunArg::explicit(&Expr::Int(42)),
            )),
        );
    }

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
