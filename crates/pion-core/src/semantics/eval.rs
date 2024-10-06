use super::*;
use crate::syntax::Stmt;

pub struct EvalEnv<'env, 'core> {
    opts: UnfoldOpts,
    locals: &'env mut LocalValues<'core>,
    metas: &'env MetaValues<'core>,
}

impl<'env, 'core> EvalEnv<'env, 'core> {
    pub fn new(
        opts: UnfoldOpts,
        locals: &'env mut LocalValues<'core>,
        metas: &'env MetaValues<'core>,
    ) -> Self {
        Self {
            opts,
            locals,
            metas,
        }
    }

    pub fn eval(self, expr: &Expr<'core>) -> Value<'core> {
        eval(expr, self.opts, self.locals, self.metas)
    }

    pub fn eval_stmt(self, stmt: &Stmt<'core>) {
        eval_stmt(stmt, self.opts, self.locals, self.metas);
    }
}

/// Evaluate an `Expr` to a `Value`.
/// Does not reduce under `fun` or `forall`
pub(super) fn eval<'core, 'env>(
    expr: &Expr<'core>,
    opts: UnfoldOpts,
    locals: &'env mut LocalValues<'core>,
    metas: &'env MetaValues<'core>,
) -> Value<'core> {
    match expr {
        Expr::Error => Value::ERROR,

        Expr::Lit(lit) => Value::Lit(*lit),

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
            elim::fun_app(fun, arg, opts, metas)
        }
        Expr::Do(stmts, trailing_expr) => {
            let len = locals.len();
            for stmt in *stmts {
                eval_stmt(stmt, opts, locals, metas);
            }
            let result = match trailing_expr {
                None => Value::UNIT_VALUE,
                Some(expr) => eval(expr, opts, locals, metas),
            };
            locals.truncate(len);
            result
        }
    }
}

/// Evaluate an `Stmt` for side effects.
/// NOTE: may add bindings to `locals`.
/// Don't forget to reset in the caller!
fn eval_stmt<'core, 'env>(
    stmt: &Stmt<'core>,
    opts: UnfoldOpts,
    locals: &'env mut LocalValues<'core>,
    metas: &'env MetaValues<'core>,
) {
    match stmt {
        Stmt::Expr(expr) => {
            eval(expr, opts, locals, metas);
        }
        Stmt::Let(binding) => {
            let rhs = eval(&binding.init, opts, locals, metas);
            locals.push(rhs);
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
        assert_eval(Expr::bool(true), Value::bool(true));
        assert_eval(Expr::bool(false), Value::bool(false));
    }

    #[test]
    fn eval_int() { assert_eval(Expr::int(42), Value::int(42)); }

    #[test]
    fn eval_char() { assert_eval(Expr::char('a'), Value::char('a')); }

    #[test]
    fn eval_string() { assert_eval(Expr::string("hello"), Value::string("hello")); }

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
        metas.push(Some(Value::int(42)));

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
            Value::int(42),
        );
    }

    #[test]
    fn eval_unbound_meta_var() {
        let var = AbsoluteVar::new(0);
        assert_eval(Expr::MetaVar(var), Value::ERROR);
    }

    #[test]
    fn eval_do() {
        // `do { let _ = 5; y }`
        let expr = Expr::Do(
            &const { [Stmt::Let(LetBinding::new(None, Expr::INT, Expr::int(5)))] },
            Some(&const { Expr::LocalVar(RelativeVar::new(0)) }),
        );

        let expected = Value::int(5);
        assert_eval(expr, expected);
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
        let int = Expr::int(42);
        let body = Expr::LocalVar(RelativeVar::new(0));
        let fun = Expr::FunLit(FunParam::explicit(None, &Expr::INT), &body);
        let expr = Expr::FunApp(&fun, FunArg::explicit(&int));
        let expected = Value::int(42);
        assert_eval(expr, expected);
    }

    #[test]
    fn eval_fun_app_stuck() {
        // `#error(42)`
        let int = Expr::int(42);
        let expr = Expr::FunApp(&Expr::Error, FunArg::explicit(&int));
        let expected = Value::Neutral(
            Head::Error,
            eco_vec![Elim::FunApp(FunArg::explicit(Value::int(42)))],
        );
        assert_eval(expr, expected);
    }

    #[test]
    fn eval_fun_app_not_fun() {
        // `42(24)`
        let int42 = Expr::int(42);
        let int24 = Expr::int(24);
        let expr = Expr::FunApp(&int42, FunArg::explicit(&int24));
        let expected = Value::ERROR;
        assert_eval(expr, expected);
    }

    #[test]
    fn eval_fun_app_plicity_mismatch() {
        // `(fun (x : Int) => x)(@42)`
        let int = Expr::int(42);
        let body = Expr::LocalVar(RelativeVar::new(0));
        let fun = Expr::FunLit(FunParam::explicit(None, &Expr::INT), &body);
        let expr = Expr::FunApp(&fun, FunArg::implicit(&int));
        let expected = Value::ERROR;
        assert_eval(expr, expected);
    }

    #[test]
    fn eval_fun_app_closure() {
        // `do { let y = 5; (fun _ => y)(42) }`
        let expr = Expr::Do(
            &const { [Stmt::Let(LetBinding::new(None, Expr::INT, Expr::int(5)))] },
            Some(
                &const {
                    Expr::FunApp(
                        &const {
                            Expr::FunLit(
                                FunParam::explicit(None, &Expr::INT),
                                &const { Expr::LocalVar(RelativeVar::new(1)) },
                            )
                        },
                        FunArg::explicit(&const { Expr::int(24) }),
                    )
                },
            ),
        );

        let expected = Value::int(5);
        assert_eval(expr, expected);
    }
}
