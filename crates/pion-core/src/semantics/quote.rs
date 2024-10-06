use super::*;
use crate::env::DeBruijn;

#[derive(Debug, Copy, Clone)]
pub struct QuoteEnv<'env, 'core> {
    locals: EnvLen,
    metas: &'env MetaValues<'core>,
}

impl<'env, 'core> QuoteEnv<'env, 'core> {
    pub fn new(locals: EnvLen, metas: &'env MetaValues<'core>) -> Self { Self { locals, metas } }

    pub fn quote(&self, value: &Value<'core>, bump: &'core bumpalo::Bump) -> Expr<'core> {
        quote(value, bump, self.locals, self.metas)
    }
}

/// Quote a value back to an expression.
pub fn quote<'core>(
    value: &Value<'core>,
    bump: &'core bumpalo::Bump,
    locals: EnvLen,
    metas: &MetaValues<'core>,
) -> Expr<'core> {
    let value = elim::subst_metas(value, UnfoldOpts::for_quote(), metas);
    match value {
        Value::Lit(lit) => Expr::Lit(lit),
        Value::Neutral(head, spine) => quote_neutral(head, &spine, bump, locals, metas),
        Value::FunType(param, body) => {
            let body = quote_closure(&body, bump, locals, metas);
            Expr::FunType(param, body)
        }
        Value::FunLit(param, body) => {
            let body = quote_closure(&body, bump, locals, metas);
            Expr::FunLit(param, body)
        }
    }
}

fn quote_head<'core>(
    head: Head,
    bump: &'core bumpalo::Bump,
    locals: EnvLen,
    metas: &MetaValues<'core>,
) -> Expr<'core> {
    match head {
        Head::Error => Expr::Error,
        Head::LocalVar(var) => match var.to_index(locals) {
            Some(de_bruijn) => Expr::LocalVar(LocalVar::new(None, de_bruijn)),
            None => Expr::Error,
        },
        Head::MetaVar(var) => match metas.get(var) {
            Some(Some(value)) => quote(value, bump, locals, metas),
            Some(None) => Expr::MetaVar(var),
            None => Expr::Error,
        },
        Head::PrimVar(var) => Expr::PrimVar(var),
    }
}

fn quote_neutral<'core>(
    head: Head,
    spine: &EcoVec<Elim<'core>>,
    bump: &'core bumpalo::Bump,
    locals: EnvLen,
    metas: &MetaValues<'core>,
) -> Expr<'core> {
    let head = quote_head(head, bump, locals, metas);
    spine.iter().fold(head, |head, elim| match elim {
        Elim::FunApp(arg) => {
            let arg_expr = quote(&arg.expr, bump, locals, metas);
            let (fun, arg_expr) = bump.alloc((head, arg_expr));
            let arg = FunArg::new(arg.plicity, &*arg_expr);
            Expr::FunApp(fun, arg)
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
) -> &'core Expr<'core> {
    let arg = Value::local_var(LocalVar::new(None, locals.to_level()));
    let body = elim::apply_closure(closure.clone(), arg, UnfoldOpts::for_quote(), metas);
    let body = quote(&body, bump, locals.succ(), metas);
    let body = bump.alloc(body);
    body
}

#[cfg(test)]
mod tests {

    use ecow::eco_vec;

    use super::*;
    use crate::env::{DeBruijnIndex, UniqueEnv};

    #[track_caller]
    #[allow(clippy::needless_pass_by_value, reason = "It's only a test")]
    fn assert_quote_in_env(locals: EnvLen, metas: &MetaValues, value: Value, expected: Expr) {
        let bump = bumpalo::Bump::default();
        let expr = quote(&value, &bump, locals, metas);
        assert_eq!(expr, expected);
    }

    #[track_caller]
    #[allow(clippy::needless_pass_by_value, reason = "It's only a test")]
    fn assert_quote(value: Value, expected: Expr) {
        assert_quote_in_env(EnvLen::default(), &UniqueEnv::default(), value, expected);
    }

    #[test]
    fn quote_error() { assert_quote(Value::ERROR, Expr::Error); }

    #[test]
    fn quote_bool() {
        assert_quote(Value::bool(true), Expr::bool(true));
        assert_quote(Value::bool(false), Expr::bool(false));
    }

    #[test]
    fn quote_int() { assert_quote(Value::int(10), Expr::int(10)); }

    #[test]
    fn quote_char() { assert_quote(Value::char('a'), Expr::char('a')); }

    #[test]
    fn quote_string() { assert_quote(Value::string("hello"), Expr::string("hello")); }

    #[test]
    fn quote_unbound_local_var() {
        let value = Value::local_var(LocalVar::new(None, DeBruijnLevel::new(0)));
        assert_quote(value, Expr::Error);
    }

    #[test]
    fn quote_unbound_meta_var() {
        let value = Value::meta_var(MetaVar::new(DeBruijnLevel::new(0)));
        assert_quote(value, Expr::Error);
    }

    #[test]
    fn quote_bound_meta_var() {
        let locals = EnvLen::default();
        let mut metas = UniqueEnv::new();
        metas.push(None);

        let value = Value::meta_var(MetaVar::new(DeBruijnLevel::new(0)));
        assert_quote_in_env(
            locals,
            &metas,
            value,
            Expr::MetaVar(MetaVar::new(DeBruijnLevel::new(0))),
        );

        metas.push(Some(Value::int(42)));
        let value = Value::meta_var(MetaVar::new(DeBruijnLevel::new(1)));
        assert_quote_in_env(locals, &metas, value, Expr::int(42));
    }

    #[test]
    fn quote_neutral() {
        let locals = EnvLen::default().succ();
        let metas = UniqueEnv::new();

        let value = Value::Neutral(
            Head::LocalVar(LocalVar::new(None, DeBruijnLevel::new(0))),
            eco_vec![Elim::FunApp(FunArg::explicit(Value::int(42)))],
        );

        assert_quote_in_env(
            locals,
            &metas,
            value,
            Expr::FunApp(
                &Expr::LocalVar(LocalVar::new(None, DeBruijnIndex::new(0))),
                FunArg::explicit(&Expr::int(42)),
            ),
        );
    }

    #[test]
    fn quote_fun_lit() {
        let body = Expr::LocalVar(LocalVar::new(None, DeBruijnIndex::new(0)));
        let fun = Value::FunLit(
            FunParam::explicit(None, &Expr::Error),
            Closure::empty(&body),
        );
        assert_quote(
            fun,
            Expr::FunLit(
                FunParam::explicit(None, &Expr::Error),
                &Expr::LocalVar(LocalVar::new(None, DeBruijnIndex::new(0))),
            ),
        );
    }

    #[test]
    fn quote_fun_type() {
        let body = Expr::LocalVar(LocalVar::new(None, DeBruijnIndex::new(0)));
        let fun = Value::FunType(
            FunParam::explicit(None, &Expr::Error),
            Closure::empty(&body),
        );
        assert_quote(
            fun,
            Expr::FunType(
                FunParam::explicit(None, &Expr::Error),
                &Expr::LocalVar(LocalVar::new(None, DeBruijnIndex::new(0))),
            ),
        );
    }
}
