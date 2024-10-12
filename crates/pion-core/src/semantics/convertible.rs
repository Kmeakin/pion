use super::*;

#[derive(Debug, Copy, Clone)]
pub struct ConvertibleEnv<'env, 'core> {
    bump: &'core bumpalo::Bump,
    locals: EnvLen,
    metas: &'env MetaValues<'core>,
}

impl<'env, 'core> ConvertibleEnv<'env, 'core> {
    pub fn new(bump: &'core bumpalo::Bump, locals: EnvLen, metas: &'env MetaValues<'core>) -> Self {
        Self {
            bump,
            locals,
            metas,
        }
    }

    pub fn convertible(&self, lhs: &Value<'core>, rhs: &Value<'core>) -> bool {
        convertible(lhs, rhs, self.bump, self.locals, self.metas)
    }
}

/// Beta-eta equality of values.
fn convertible<'core>(
    lhs: &Value<'core>,
    rhs: &Value<'core>,
    bump: &'core bumpalo::Bump,
    locals: EnvLen,
    metas: &MetaValues<'core>,
) -> bool {
    match (lhs, rhs) {
        (Value::Lit(lhs), Value::Lit(rhs)) => lhs == rhs,
        (Value::Neutral(lhs_head, lhs_spine), Value::Neutral(rhs_head, rhs_spine)) => {
            convertible_neutral(
                (*lhs_head, lhs_spine),
                (*rhs_head, rhs_spine),
                bump,
                locals,
                metas,
            )
        }
        (Value::FunType(lhs_param, lhs_body), Value::FunType(rhs_param, rhs_body))
        | (Value::FunLit(lhs_param, lhs_body), Value::FunLit(rhs_param, rhs_body)) => {
            convertible_funs(
                lhs_param, lhs_body, rhs_param, rhs_body, bump, locals, metas,
            )
        }
        (Value::FunLit(param, body), value) | (value, Value::FunLit(param, body)) => {
            fun_eta_convertible(*param, body, value, bump, locals, metas)
        }
        _ => false,
    }
}

fn convertible_neutral<'core>(
    (lhs_head, lhs_spine): (Head<'core>, &Spine<'core>),
    (rhs_head, rhs_spine): (Head<'core>, &Spine<'core>),
    bump: &'core bumpalo::Bump,
    locals: EnvLen,
    metas: &MetaValues<'core>,
) -> bool {
    lhs_head == rhs_head
        && lhs_spine.len() == rhs_spine.len()
        && lhs_spine
            .iter()
            .zip(rhs_spine.iter())
            .all(|(lhs, rhs)| convertible_elim(lhs, rhs, bump, locals, metas))
}

fn convertible_elim<'core>(
    lhs: &Elim<'core>,
    rhs: &Elim<'core>,
    bump: &'core bumpalo::Bump,
    locals: EnvLen,
    metas: &MetaValues<'core>,
) -> bool {
    match (lhs, rhs) {
        (Elim::FunApp(lhs), Elim::FunApp(rhs)) => {
            lhs.plicity == rhs.plicity && convertible(&lhs.expr, &rhs.expr, bump, locals, metas)
        }
        (Elim::If(lhs_locals, lhs_then, lhs_else), Elim::If(rhs_locals, rhs_then, rhs_else)) => {
            let opts = UnfoldOpts::for_eval();

            let mut lhs_locals = lhs_locals.clone();
            let mut rhs_locals = rhs_locals.clone();

            let lhs_then = eval::eval(lhs_then, bump, opts, &mut lhs_locals, metas);
            let rhs_then = eval::eval(rhs_then, bump, opts, &mut rhs_locals, metas);
            if !convertible(&lhs_then, &rhs_then, bump, locals, metas) {
                return false;
            }

            let lhs_else = eval::eval(lhs_else, bump, opts, &mut lhs_locals, metas);
            let rhs_else = eval::eval(rhs_else, bump, opts, &mut rhs_locals, metas);

            convertible(&lhs_else, &rhs_else, bump, locals, metas)
        }
        _ => false,
    }
}

/// Check if a function is eta-convertible to a value:
/// `fun x => f` is eta-equivalent to `f`
fn fun_eta_convertible<'core>(
    lhs_param: FunParam<'core, &'core Value<'core>>,
    lhs_body: &Closure<'core>,
    rhs_value: &Value<'core>,
    bump: &'core bumpalo::Bump,
    locals: EnvLen,
    metas: &MetaValues<'core>,
) -> bool {
    let var = Value::local_var(LocalVar::new(lhs_param.name, locals.to_level()));
    let lhs = elim::apply_closure(
        lhs_body.clone(),
        var.clone(),
        bump,
        UnfoldOpts::for_quote(),
        metas,
    );
    let rhs = elim::fun_app(
        rhs_value.clone(),
        FunArg::new(lhs_param.plicity, var),
        bump,
        UnfoldOpts::for_quote(),
        metas,
    );

    convertible(&lhs, &rhs, bump, locals.succ(), metas)
}

fn convertible_funs<'core>(
    lhs_param: &FunParam<'core, &'core Value<'core>>,
    lhs: &Closure<'core>,
    rhs_param: &FunParam<'core, &'core Value<'core>>,
    rhs: &Closure<'core>,
    bump: &'core bumpalo::Bump,
    locals: EnvLen,
    metas: &MetaValues<'core>,
) -> bool {
    if lhs_param.plicity != rhs_param.plicity {
        return false;
    }

    if !convertible(lhs_param.r#type, rhs_param.r#type, bump, locals, metas) {
        return false;
    }

    let lhs = elim::apply_closure(
        lhs.clone(),
        Value::local_var(LocalVar::new(None, locals.to_level())),
        bump,
        UnfoldOpts::for_quote(),
        metas,
    );

    let rhs = elim::apply_closure(
        rhs.clone(),
        Value::local_var(LocalVar::new(None, locals.to_level())),
        bump,
        UnfoldOpts::for_quote(),
        metas,
    );
    convertible(&lhs, &rhs, bump, locals.succ(), metas)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{DeBruijnIndex, UniqueEnv};
    use crate::syntax::LocalVar;

    #[track_caller]
    fn assert_convertible<'core>(lhs: &Value<'core>, rhs: &Value<'core>) {
        let bump = bumpalo::Bump::new();
        let locals = EnvLen::default();
        let metas = UniqueEnv::default();
        assert!(convertible(lhs, rhs, &bump, locals, &metas));
        assert!(convertible(rhs, lhs, &bump, locals, &metas));
    }

    #[track_caller]
    fn assert_not_convertible<'core>(lhs: &Value<'core>, rhs: &Value<'core>) {
        let bump = bumpalo::Bump::new();
        let locals = EnvLen::default();
        let metas = UniqueEnv::default();
        assert!(!convertible(lhs, rhs, &bump, locals, &metas));
        assert!(!convertible(rhs, lhs, &bump, locals, &metas));
    }

    #[test]
    fn test_not_convertible() { assert_not_convertible(&Value::int(0), &Value::bool(false)); }

    #[test]
    fn test_convertible_bools() {
        assert_convertible(&Value::bool(true), &Value::bool(true));
        assert_convertible(&Value::bool(false), &Value::bool(false));
        assert_not_convertible(&Value::bool(true), &Value::bool(false));
    }

    #[test]
    fn test_convertible_ints() {
        assert_convertible(&Value::int(42), &Value::int(42));
        assert_not_convertible(&Value::int(42), &Value::int(43));
    }

    #[test]
    fn test_convertible_chars() {
        assert_convertible(&Value::char('a'), &Value::char('a'));
        assert_not_convertible(&Value::char('a'), &Value::char('b'));
    }

    #[test]
    fn test_convertible_strings() {
        assert_convertible(&Value::string("hello"), &Value::string("hello"));
        assert_not_convertible(&Value::string("hello"), &Value::string("world"));
    }

    #[test]
    fn test_convertible_fun_types() {
        // `forall (_ : Type) -> Int` == `forall (_ : Type) -> Int`

        let ty = Type::TYPE;
        let param = FunParam::explicit(None, &ty);
        let body = Closure::empty(&Expr::INT);
        let fun = Value::FunType(param, body);

        assert_convertible(&fun, &fun);

        // `forall (_ : Type) -> Int` != `forall (_ : Type) -> Bool`
        assert_not_convertible(&fun, &Value::FunType(param, Closure::empty(&Expr::BOOL)));
    }

    #[test]
    fn test_convertible_fun_expr() {
        // `fun (_ : Type) -> Int` == `fun (_ : Type) -> Int`

        let ty = Type::TYPE;
        let param = FunParam::explicit(None, &ty);
        let body = Closure::empty(&Expr::INT);
        let fun = Value::FunLit(param, body);

        assert_convertible(&fun, &fun);

        // `fun (_ : Type) -> Int` != `fun (_ : Type) -> Bool`
        assert_not_convertible(&fun, &Value::FunLit(param, Closure::empty(&Expr::BOOL)));
    }

    #[test]
    fn test_eta_convertible_fun() {
        // `fun (x : Int) => Bool(x)` == `Bool`

        let ty = Type::TYPE;
        let lhs = Value::FunLit(
            FunParam::explicit(None, &ty),
            Closure::empty(
                &const {
                    Expr::FunApp(
                        &Expr::BOOL,
                        FunArg::explicit(
                            &const { Expr::LocalVar(LocalVar::new(None, DeBruijnIndex::new(0))) },
                        ),
                    )
                },
            ),
        );
        let rhs = Value::BOOL;

        assert_convertible(&lhs, &rhs);
        assert_convertible(&rhs, &lhs);
    }
}
