use super::*;
use crate::env::DeBruijn;
use crate::syntax::MatchBool;

#[derive(Debug, Copy, Clone)]
pub struct QuoteEnv<'env, 'core> {
    bump: &'core bumpalo::Bump,
    locals: EnvLen,
    metas: &'env MetaValues<'core>,
}

impl<'env, 'core> QuoteEnv<'env, 'core> {
    pub fn new(bump: &'core bumpalo::Bump, locals: EnvLen, metas: &'env MetaValues<'core>) -> Self {
        Self {
            bump,
            locals,
            metas,
        }
    }

    pub fn quote(&self, value: &Value<'core>) -> Expr<'core> {
        quote(value, self.bump, self.locals, self.metas)
    }

    pub fn quote_offset(&self, value: &Value<'core>, offset: EnvLen) -> Expr<'core> {
        quote(value, self.bump, self.locals + offset, self.metas)
    }
}

/// Quote a value back to an expression.
pub fn quote<'core>(
    value: &Value<'core>,
    bump: &'core bumpalo::Bump,
    mut locals: EnvLen,
    metas: &MetaValues<'core>,
) -> Expr<'core> {
    let value = elim::subst_metas(value, bump, UnfoldOpts::for_quote(), metas);
    match value {
        Value::Lit(lit) => Expr::Lit(lit),
        Value::Neutral(head, spine) => quote_neutral(head, spine, bump, locals, metas),
        Value::FunType(param, body) => {
            let (param, body) = quote_funs(&param, &body, bump, locals, metas);
            Expr::FunType(param, body)
        }
        Value::FunLit(param, body) => {
            let (param, body) = quote_funs(&param, &body, bump, locals, metas);
            Expr::FunLit(param, body)
        }
        Value::RecordType(mut telescope) => {
            let mut expr_fields = Vec::new_in(bump);
            while let Some((name, value, update_telescope)) =
                elim::split_telescope(&mut telescope, bump, UnfoldOpts::for_quote(), metas)
            {
                let var = Value::local_var(LocalVar::new(locals.to_level()));
                update_telescope(var);
                let expr = quote(&value, bump, locals, metas);
                expr_fields.push((name, expr));
                locals.push();
            }
            Expr::RecordType(expr_fields.leak())
        }
        Value::RecordLit(fields) => Expr::RecordLit(bump.alloc_slice_fill_iter(
            (fields.iter()).map(|(label, value)| (*label, quote(value, bump, locals, metas))),
        )),
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
            Some(de_bruijn) => Expr::LocalVar(LocalVar::new(de_bruijn)),
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
    spine: Spine<'core>,
    bump: &'core bumpalo::Bump,
    locals: EnvLen,
    metas: &MetaValues<'core>,
) -> Expr<'core> {
    let head = quote_head(head, bump, locals, metas);
    spine.into_iter().fold(head, |head, elim| match elim {
        Elim::FunApp(arg) => {
            let arg_expr = quote(&arg.expr, bump, locals, metas);
            let (fun, arg_expr) = bump.alloc((head, arg_expr));
            let arg = FunArg::new(arg.plicity, &*arg_expr);
            Expr::FunApp(fun, arg)
        }
        Elim::MatchBool(mut values, then, r#else) => {
            let then = {
                let value = eval::eval(then, bump, UnfoldOpts::for_quote(), &mut values, metas);
                quote(&value, bump, locals, metas)
            };
            let r#else = {
                let value = eval::eval(r#else, bump, UnfoldOpts::for_quote(), &mut values, metas);
                quote(&value, bump, locals, metas)
            };
            let (cond, then, r#else) = bump.alloc((head, then, r#else));
            let it = MatchBool {
                cond,
                motive: &Expr::Error,
                then,
                r#else,
            };
            Expr::MatchBool(it)
        }
        Elim::MatchInt(mut values, cases, default) => {
            let cases = bump.alloc_slice_fill_iter(cases.iter().map(|(n, expr)| {
                let value = eval::eval(expr, bump, UnfoldOpts::for_quote(), &mut values, metas);
                let expr = quote(&value, bump, locals, metas);
                (*n, expr)
            }));
            let default = {
                let value = eval::eval(default, bump, UnfoldOpts::for_quote(), &mut values, metas);
                quote(&value, bump, locals, metas)
            };
            let (head, default) = bump.alloc((head, default));
            Expr::MatchInt(head, cases, default)
        }
        Elim::RecordProj(label) => Expr::RecordProj(bump.alloc(head), label),
    })
}

/// Quote a `Closure` back to an `Expr`.
///
/// NOTE: We can't simply return `closure.expr`, because `closure.expr` could
/// reference a local variable in `closure.env`. We *could* convert the closure
/// environment back to series of nested `let`s, but that would produce very big
/// terms!
fn quote_funs<'core>(
    param: &FunParam<'core, &'core Type<'core>>,
    closure: &Closure<'core>,
    bump: &'core bumpalo::Bump,
    locals: EnvLen,
    metas: &MetaValues<'core>,
) -> (FunParam<'core, &'core Expr<'core>>, &'core Expr<'core>) {
    let param_type = quote(param.r#type, bump, locals, metas);

    let arg = Value::local_var(LocalVar::new(locals.to_level()));
    let body = elim::apply_closure(closure.clone(), arg, bump, UnfoldOpts::for_quote(), metas);
    let body = quote(&body, bump, locals.succ(), metas);

    let (param_type, body) = bump.alloc((param_type, body));
    let param = FunParam::new(param.plicity, param.name, &*param_type);
    (param, body)
}

#[cfg(test)]
mod tests {

    use ecow::eco_vec;

    use super::*;
    use crate::env::{DeBruijnIndex, UniqueEnv};
    use crate::symbol::sym;

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
        let value = Value::local_var(LocalVar::new(DeBruijnLevel::new(0)));
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
            Head::LocalVar(LocalVar::new(DeBruijnLevel::new(0))),
            eco_vec![Elim::FunApp(FunArg::explicit(Value::int(42)))],
        );

        assert_quote_in_env(
            locals,
            &metas,
            value,
            Expr::FunApp(
                &Expr::LocalVar(LocalVar::new(DeBruijnIndex::new(0))),
                FunArg::explicit(&Expr::int(42)),
            ),
        );
    }

    #[test]
    fn quote_fun_lit() {
        let ty = Type::ERROR;
        let body = Expr::LocalVar(LocalVar::new(DeBruijnIndex::new(0)));
        let fun = Value::FunLit(FunParam::explicit(None, &ty), Closure::empty(&body));
        assert_quote(
            fun,
            Expr::FunLit(
                FunParam::explicit(None, &Expr::Error),
                &Expr::LocalVar(LocalVar::new(DeBruijnIndex::new(0))),
            ),
        );
    }

    #[test]
    fn quote_fun_type() {
        let ty = Type::ERROR;
        let body = Expr::LocalVar(LocalVar::new(DeBruijnIndex::new(0)));
        let fun = Value::FunType(FunParam::explicit(None, &ty), Closure::empty(&body));
        assert_quote(
            fun,
            Expr::FunType(
                FunParam::explicit(None, &Expr::Error),
                &Expr::LocalVar(LocalVar::new(DeBruijnIndex::new(0))),
            ),
        );
    }

    #[test]
    fn quote_record_lit() {
        // `{}`
        let value = Value::RecordLit(&[]);
        assert_quote(value, Expr::RecordLit(&[]));

        // `{a=42}`
        let value = Value::RecordLit(const { &[(sym::a, Value::int(42))] });
        assert_quote(value, Expr::RecordLit(&[(sym::a, Expr::int(42))]));

        // `{a=42, b=24}`
        let value =
            Value::RecordLit(const { &[(sym::a, Value::int(42)), (sym::b, Value::int(24))] });
        assert_quote(
            value,
            Expr::RecordLit(&[(sym::a, Expr::int(42)), (sym::b, Expr::int(24))]),
        );
    }

    #[test]
    fn quote_record_type() {
        // `{}`
        let value = Value::RecordType(Telescope::empty());
        assert_quote(value, Expr::RecordType(&[]));

        // `{a: Int}`
        let value = Value::RecordType(Telescope::new(LocalValues::new(), &[(sym::a, Expr::INT)]));
        assert_quote(value, Expr::RecordType(&[(sym::a, Expr::INT)]));

        // `{a: Int, b: Char}`
        let value = Value::RecordType(Telescope::new(
            LocalValues::new(),
            &[(sym::a, Expr::INT), (sym::b, Expr::CHAR)],
        ));
        assert_quote(
            value,
            Expr::RecordType(&[(sym::a, Expr::INT), (sym::b, Expr::CHAR)]),
        );
    }
}
