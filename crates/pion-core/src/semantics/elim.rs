//! Elimination rules

use super::*;

pub fn apply_eliminator<'core>(
    head: Value<'core>,
    elim: Elim<'core>,
    opts: UnfoldOpts,
    metas: &MetaValues<'core>,
) -> Result<Value<'core>, Error<'core>> {
    match elim {
        Elim::FunApp(arg) => apply_arg(head, arg, opts, metas),
    }
}

pub fn apply_spine<'core>(
    head: Value<'core>,
    spine: Spine<'core>,
    opts: UnfoldOpts,
    metas: &MetaValues<'core>,
) -> Result<Value<'core>, Error<'core>> {
    spine
        .into_iter()
        .try_fold(head, |head, elim| apply_eliminator(head, elim, opts, metas))
}

/// Apply `arg` to `callee`.
/// Performs beta reduction if `callee` is a lambda.
pub fn apply_arg<'core>(
    callee: Value<'core>,
    arg: FunArg<Value<'core>>,
    opts: UnfoldOpts,
    metas: &MetaValues<'core>,
) -> Result<Value<'core>, Error<'core>> {
    match callee {
        Value::Neutral(head, mut spine) => {
            spine.push(Elim::FunApp(arg));
            Ok(Value::Neutral(head, spine))
        }
        Value::FunLit(param, body) if param.plicity == arg.plicity => {
            beta_reduce(body, arg.expr, opts, metas)
        }
        Value::FunLit(param, _) => Err(Error::PlicityMismatch {
            param_plicity: param.plicity,
            arg_plicity: arg.plicity,
        }),
        _ => Err(Error::NotAFunction { callee }),
    }
}

/// Beta reduction: `(fun x => body)(arg)` -> `body[x := arg]`.
pub fn beta_reduce<'core>(
    closure: Closure<'core>,
    arg: Value<'core>,
    opts: UnfoldOpts,
    metas: &MetaValues<'core>,
) -> Result<Value<'core>, Error<'core>> {
    let Closure {
        mut local_values,
        body,
    } = closure;
    local_values.push(arg);
    eval::eval(body, opts, &mut local_values, metas)
}

/// Substitute meta variables in neutral spines with their values, and reduce
/// further if possible.
pub fn subst_metas<'core>(
    value: &Value<'core>,
    metas: &MetaValues<'core>,
) -> Result<Value<'core>, Error<'core>> {
    let mut value = value.clone();
    while let Value::Neutral(Head::MetaVar(var), spine) = value {
        match metas.get_absolute(var) {
            None => {
                return Err(Error::UnboundMetaVar {
                    var,
                    len: metas.len(),
                })
            }
            Some(None) => return Ok(Value::Neutral(Head::MetaVar(var), spine)),
            Some(Some(head)) => {
                value = apply_spine(head.clone(), spine, UnfoldOpts::for_quote(), metas)?;
            }
        }
    }
    Ok(value)
}

#[cfg(test)]
mod tests {

    use ecow::eco_vec;

    use super::*;
    use crate::env::UniqueEnv;

    #[test]
    fn test_apply_neutral() {
        // `_#0(42)``
        let var = AbsoluteVar::new(0);
        let callee = Value::local_var(var);
        let arg = FunArg::explicit(Value::Int(42));
        let opts = UnfoldOpts::for_eval();
        let meta_values = UniqueEnv::default();
        let result = apply_arg(callee, arg.clone(), opts, &meta_values);

        assert_eq!(
            result,
            Ok(Value::Neutral(
                Head::LocalVar(var),
                eco_vec![Elim::FunApp(arg)]
            ))
        );
    }

    #[test]
    fn test_subst_metas_unbound() {
        let var = AbsoluteVar::new(0);
        let value = Value::meta_var(var);
        let metas = UniqueEnv::default();
        let result = subst_metas(&value, &metas);
        assert_eq!(
            result,
            Err(Error::UnboundMetaVar {
                var,
                len: EnvLen::new(0)
            })
        );
    }

    #[test]
    fn test_subst_metas_bound() {
        // `?0(24)` in `[Some(fun x => 42)]`
        let mut metas = UniqueEnv::default();
        metas.push(Some(Value::FunLit(
            FunParam::explicit(None, &Expr::INT),
            Closure::empty(&Expr::Int(42)),
        )));

        let value = Value::Neutral(
            Head::MetaVar(AbsoluteVar::new(0)),
            eco_vec![Elim::FunApp(FunArg::explicit(Value::Int(24)))],
        );

        let result = subst_metas(&value, &metas);
        assert_eq!(result, Ok(Value::Int(42)));

        // `?0(24)` in `[None]`
        metas.clear();
        metas.push(None);
        let result = subst_metas(&value, &metas);
        assert_eq!(result, Ok(value));
    }

    #[test]
    fn test_subst_metas_reduce() {
        // `?0(24)` in `[Some(fun x => 42)]`
        let var = AbsoluteVar::new(0);
        let value = Value::Neutral(
            Head::MetaVar(var),
            eco_vec![Elim::FunApp(FunArg::explicit(Value::Int(24)))],
        );
        let mut metas = UniqueEnv::default();
        metas.push(Some(Value::FunLit(
            FunParam::explicit(None, &Expr::INT),
            Closure::empty(&Expr::Int(42)),
        )));
        let result = subst_metas(&value, &metas);
        assert_eq!(result, Ok(Value::Int(42)));
    }
}
