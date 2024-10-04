use super::*;

/// Beta-eta equality of values.
pub fn convertible<'core>(
    lhs: &Value<'core>,
    rhs: &Value<'core>,
    locals: EnvLen,
    metas: &MetaValues<'core>,
) -> bool {
    match (lhs, rhs) {
        (Value::Bool(lhs), Value::Bool(rhs)) => lhs == rhs,
        (Value::Int(lhs), Value::Int(rhs)) => lhs == rhs,
        (Value::Char(lhs), Value::Char(rhs)) => lhs == rhs,
        (Value::String(lhs), Value::String(rhs)) => lhs == rhs,
        (Value::Neutral(lhs_head, lhs_spine), Value::Neutral(rhs_head, rhs_spine)) => {
            convertible_neutral(
                (*lhs_head, lhs_spine),
                (*rhs_head, rhs_spine),
                locals,
                metas,
            )
        }
        (Value::FunType(lhs_param, lhs_body), Value::FunType(rhs_param, rhs_body))
        | (Value::FunLit(lhs_param, lhs_body), Value::FunLit(rhs_param, rhs_body)) => {
            convertible_funlike(
                &(*lhs_param, lhs_body),
                &(*rhs_param, rhs_body),
                locals,
                metas,
            )
        }
        (Value::FunLit(param, body), value) | (value, Value::FunLit(param, body)) => {
            fun_eta_convertible(*param, body, value, locals, metas)
        }
        _ => false,
    }
}

fn convertible_neutral<'core>(
    (lhs_head, lhs_spine): (Head, &EcoVec<Elim<'core>>),
    (rhs_head, rhs_spine): (Head, &EcoVec<Elim<'core>>),
    locals: EnvLen,
    metas: &MetaValues<'core>,
) -> bool {
    lhs_head == rhs_head
        && lhs_spine.len() == rhs_spine.len()
        && lhs_spine
            .iter()
            .zip(rhs_spine.iter())
            .all(|(lhs, rhs)| convertible_elim(lhs, rhs, locals, metas))
}

fn convertible_elim<'core>(
    lhs: &Elim<'core>,
    rhs: &Elim<'core>,
    locals: EnvLen,
    metas: &MetaValues<'core>,
) -> bool {
    match (lhs, rhs) {
        (Elim::FunApp(lhs), Elim::FunApp(rhs)) => {
            lhs.plicity == rhs.plicity && convertible(&lhs.expr, &rhs.expr, locals, metas)
        }
    }
}

fn convertible_funlike<'core>(
    (lhs_param, lhs_closure): &(FunParam<'core, &'core Expr<'core>>, &Closure<'core>),
    (rhs_param, rhs_closure): &(FunParam<'core, &'core Expr<'core>>, &Closure<'core>),
    locals: EnvLen,
    metas: &MetaValues<'core>,
) -> bool {
    lhs_param.plicity == rhs_param.plicity
        && convertible_closure(lhs_closure, rhs_closure, locals, metas)
}

/// Check if a function is eta-convertible to a value:
/// `fun x => f` is eta-equivalent to `f`
fn fun_eta_convertible<'core>(
    lhs_param: FunParam<'core, &'core Expr<'core>>,
    lhs_body: &Closure<'core>,
    rhs_value: &Value<'core>,
    locals: EnvLen,
    metas: &MetaValues<'core>,
) -> bool {
    let var = Value::local_var(locals.to_absolute());
    let lhs = elim::beta_reduce(
        lhs_body.clone(),
        var.clone(),
        UnfoldOpts::for_quote(),
        metas,
    );
    let rhs = elim::apply_arg(
        rhs_value.clone(),
        FunArg::new(lhs_param.plicity, var),
        UnfoldOpts::for_quote(),
        metas,
    );

    convertible(&lhs, &rhs, locals.succ(), metas)
}

fn convertible_closure<'core>(
    lhs: &Closure<'core>,
    rhs: &Closure<'core>,
    locals: EnvLen,
    metas: &MetaValues<'core>,
) -> bool {
    let lhs = elim::beta_reduce(
        lhs.clone(),
        Value::local_var(locals.to_absolute()),
        UnfoldOpts::for_quote(),
        metas,
    );

    let rhs = elim::beta_reduce(
        rhs.clone(),
        Value::local_var(locals.to_absolute()),
        UnfoldOpts::for_quote(),
        metas,
    );
    convertible(&lhs, &rhs, locals.succ(), metas)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{RelativeVar, UniqueEnv};

    #[track_caller]
    fn assert_convertible<'core>(lhs: &Value<'core>, rhs: &Value<'core>) {
        let locals = EnvLen::default();
        let metas = UniqueEnv::default();
        assert!(convertible(lhs, rhs, locals, &metas));
        assert!(convertible(rhs, lhs, locals, &metas));
    }

    #[track_caller]
    fn assert_not_convertible<'core>(lhs: &Value<'core>, rhs: &Value<'core>) {
        let locals = EnvLen::default();
        let metas = UniqueEnv::default();
        assert!(!convertible(lhs, rhs, locals, &metas));
        assert!(!convertible(rhs, lhs, locals, &metas));
    }

    #[test]
    fn test_not_convertible() { assert_not_convertible(&Value::Int(0), &Value::Bool(false)); }

    #[test]
    fn test_convertible_bools() {
        assert_convertible(&Value::Bool(true), &Value::Bool(true));
        assert_convertible(&Value::Bool(false), &Value::Bool(false));
        assert_not_convertible(&Value::Bool(true), &Value::Bool(false));
    }

    #[test]
    fn test_convertible_ints() {
        assert_convertible(&Value::Int(42), &Value::Int(42));
        assert_not_convertible(&Value::Int(42), &Value::Int(43));
    }

    #[test]
    fn test_convertible_chars() {
        assert_convertible(&Value::Char('a'), &Value::Char('a'));
        assert_not_convertible(&Value::Char('a'), &Value::Char('b'));
    }

    #[test]
    fn test_convertible_strings() {
        assert_convertible(&Value::String("hello"), &Value::String("hello"));
        assert_not_convertible(&Value::String("hello"), &Value::String("world"));
    }

    #[test]
    fn test_convertible_fun_types() {
        // `forall (_ : Type) -> Int` == `forall (_ : Type) -> Int`

        let param = FunParam::explicit(None, &Expr::TYPE);
        let body = Closure::empty(&Expr::INT);
        let fun = Value::FunType(param, body);

        assert_convertible(&fun, &fun);

        // `forall (_ : Type) -> Int` != `forall (_ : Type) -> Bool`
        assert_not_convertible(&fun, &Value::FunType(param, Closure::empty(&Expr::BOOL)));
    }

    #[test]
    fn test_convertible_fun_expr() {
        // `fun (_ : Type) -> Int` == `fun (_ : Type) -> Int`

        let param = FunParam::explicit(None, &Expr::TYPE);
        let body = Closure::empty(&Expr::INT);
        let fun = Value::FunLit(param, body);

        assert_convertible(&fun, &fun);

        // `fun (_ : Type) -> Int` != `fun (_ : Type) -> Bool`
        assert_not_convertible(&fun, &Value::FunLit(param, Closure::empty(&Expr::BOOL)));
    }

    #[test]
    fn test_eta_convertible_fun() {
        // `fun (x : Int) => Bool(x)` == `Bool`

        let lhs = Value::FunLit(
            FunParam::explicit(None, &Expr::INT),
            Closure::empty(
                &const {
                    Expr::FunApp(
                        &Expr::BOOL,
                        FunArg::explicit(&const { Expr::LocalVar(RelativeVar::new(0)) }),
                    )
                },
            ),
        );
        let rhs = Value::BOOL;

        assert_convertible(&lhs, &rhs);
        assert_convertible(&rhs, &lhs);
    }
}
