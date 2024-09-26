use super::*;

/// Evaluate an `Expr` to a `Value`.
/// Does not reduce under `fun` or `forall`
pub fn eval<'core, 'env>(
    expr: &Expr<'core>,
    opts: UnfoldOpts,
    locals: &'env mut LocalValues<'core>,
    metas: &'env MetaValues<'core>,
) -> Value<'core> {
    match expr {
        Expr::Error => Value::ERROR,

        Expr::Bool(b) => Value::Bool(*b),
        Expr::Int(x) => Value::Int(*x),
        Expr::Char(c) => Value::Char(*c),
        Expr::String(s) => Value::String(s),

        Expr::PrimVar(var) => Value::prim_var(*var),

        Expr::LocalVar(var) => match locals.get_relative(*var) {
            None => Value::ERROR,
            Some(value) => value.clone(),
        },
        Expr::MetaVar(var) => match metas.get_absolute(*var) {
            None => Value::ERROR,
            Some(Some(value)) => value.clone(),
            Some(None) => Value::meta_var(*var),
        },
        Expr::Let(binding, body) => {
            let rhs = eval(binding.init, opts, locals, metas);
            locals.push(rhs);
            let body = eval(body, opts, locals, metas);
            locals.pop();
            body
        }
        Expr::FunType(param, body) => {
            let body = Closure::new(locals.clone(), body);
            Value::FunType(*param, body)
        }
        Expr::FunLit(param, body) => {
            let body = Closure::new(locals.clone(), body);
            Value::FunLit(*param, body)
        }
        Expr::FunApp(fun, arg) => {
            let fun = eval(fun, opts, locals, metas);
            let arg_expr = eval(arg.expr, opts, locals, metas);
            let arg = FunArg::new(arg.plicity, arg_expr);
            elim::apply_arg(fun, arg, opts, metas)
        }
    }
}

#[cfg(test)]
mod tests {
    use ecow::eco_vec;

    use super::*;
    use crate::env::{RelativeVar, UniqueEnv};
    use crate::syntax::LetBinding;

    #[track_caller]
    #[allow(clippy::needless_pass_by_value, reason = "It's only a test")]
    fn assert_eval_in_env<'env, 'core>(
        locals: &'env mut LocalValues<'core>,
        metas: &'env MetaValues<'core>,
        expr: Expr<'core>,
        expected: Value,
    ) {
        let opts = UnfoldOpts::for_eval();
        let result = eval(&expr, opts, locals, metas);
        assert_eq!(result, expected);
    }

    #[track_caller]
    #[allow(clippy::needless_pass_by_value, reason = "It's only a test")]
    fn assert_eval(expr: Expr, expected: Value) {
        assert_eval_in_env(&mut LocalValues::new(), &UniqueEnv::new(), expr, expected);
    }

    #[test]
    fn eval_error() { assert_eval(Expr::Error, Value::ERROR); }

    #[test]
    fn eval_bool() {
        assert_eval(Expr::Bool(true), Value::Bool(true));
        assert_eval(Expr::Bool(false), Value::Bool(false));
    }

    #[test]
    fn eval_int() { assert_eval(Expr::Int(42), Value::Int(42)); }

    #[test]
    fn eval_char() { assert_eval(Expr::Char('a'), Value::Char('a')); }

    #[test]
    fn eval_string() { assert_eval(Expr::String("hello"), Value::String("hello")); }

    #[test]
    fn eval_prim_var() {
        assert_eval(Expr::PrimVar(PrimVar::Bool), Value::prim_var(PrimVar::Bool));
    }

    #[test]
    fn eval_unbound_local_var() {
        let var = RelativeVar::new(0);
        assert_eval(Expr::LocalVar(var), Value::ERROR);
    }

    #[test]
    fn eval_meta_var() {
        let mut locals = LocalValues::new();
        let mut metas = UniqueEnv::new();
        metas.push(None);
        metas.push(Some(Value::Int(42)));

        assert_eval_in_env(
            &mut locals,
            &metas,
            Expr::MetaVar(AbsoluteVar::new(0)),
            Value::meta_var(AbsoluteVar::new(0)),
        );
        assert_eval_in_env(
            &mut locals,
            &metas,
            Expr::MetaVar(AbsoluteVar::new(1)),
            Value::Int(42),
        );
    }

    #[test]
    fn eval_unbound_meta_var() {
        let var = AbsoluteVar::new(0);
        assert_eval(Expr::MetaVar(var), Value::ERROR);
    }

    #[test]
    fn eval_let() {
        // `let x = 42; x`
        let expr = Expr::Let(
            LetBinding::new(None, &Expr::INT, &Expr::Int(42)),
            &const { Expr::LocalVar(RelativeVar::new(0)) },
        );
        assert_eval(expr, Value::Int(42));
    }

    #[test]
    fn eval_fun_type() {
        // `forall (b: Bool) -> Int`
        let expr = Expr::FunType(
            FunParam::explicit(None, &Expr::BOOL),
            &Expr::PrimVar(PrimVar::Int),
        );
        let expected = Value::FunType(
            FunParam::explicit(None, &Expr::BOOL),
            Closure::empty(&Expr::INT),
        );
        assert_eval(expr, expected);
    }

    #[test]
    fn eval_fun_lit() {
        // `fun (x: Int) => x`
        let body = Expr::LocalVar(RelativeVar::new(0));
        let expr = Expr::FunLit(FunParam::explicit(None, &Expr::INT), &body);
        let expected = Value::FunLit(
            FunParam::explicit(None, &Expr::INT),
            Closure::new(LocalValues::new(), &body),
        );
        assert_eval(expr, expected);
    }

    #[test]
    fn eval_fun_app_beta_reduce() {
        // `(fun (x : Int) => x)(42)`
        let body = Expr::LocalVar(RelativeVar::new(0));
        let fun = Expr::FunLit(FunParam::explicit(None, &Expr::INT), &body);
        let expr = Expr::FunApp(&fun, FunArg::explicit(&Expr::Int(42)));
        let expected = Value::Int(42);
        assert_eval(expr, expected);
    }

    #[test]
    fn eval_fun_app_stuck() {
        // `#error(42)`
        let expr = Expr::FunApp(&Expr::Error, FunArg::explicit(&Expr::Int(42)));
        let expected = Value::Neutral(
            Head::Error,
            eco_vec![Elim::FunApp(FunArg::explicit(Value::Int(42)))],
        );
        assert_eval(expr, expected);
    }

    #[test]
    fn eval_fun_app_not_fun() {
        // `42(24)`
        let expr = Expr::FunApp(&Expr::Int(42), FunArg::explicit(&Expr::Int(24)));
        let expected = Value::ERROR;
        assert_eval(expr, expected);
    }

    #[test]
    fn eval_fun_app_plicity_mismatch() {
        // `(fun (x : Int) => x)(@42)`
        let body = Expr::LocalVar(RelativeVar::new(0));
        let fun = Expr::FunLit(FunParam::explicit(None, &Expr::INT), &body);
        let expr = Expr::FunApp(&fun, FunArg::implicit(&Expr::Int(42)));
        let expected = Value::ERROR;
        assert_eval(expr, expected);
    }

    #[test]
    fn eval_fun_app_closure() {
        // `let y = 5; (fun _ => y)(42)`
        let expr = Expr::Let(
            LetBinding::new(None, &Expr::INT, &Expr::Int(5)),
            &const {
                Expr::FunApp(
                    &const {
                        Expr::FunLit(
                            FunParam::explicit(None, &Expr::INT),
                            &const { Expr::LocalVar(RelativeVar::new(1)) },
                        )
                    },
                    FunArg::explicit(&Expr::Int(42)),
                )
            },
        );

        let expected = Value::Int(5);
        assert_eval(expr, expected);
    }
}
