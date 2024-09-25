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
    )
    .unwrap();
    let rhs = elim::beta_reduce(
        rhs.clone(),
        Value::local_var(locals.to_absolute()),
        UnfoldOpts::for_quote(),
        metas,
    )
    .unwrap();
    convertible(&lhs, &rhs, locals.succ(), metas)
}
