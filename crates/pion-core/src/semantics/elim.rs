use super::*;

/// Apply an argument to a function.
/// Performs beta reduction if the callee is a `fun`.
pub fn apply<'core>(
    callee: Value<'core>,
    arg: FunArg<Value<'core>>,
    opts: UnfoldOpts,
    meta_values: &MetaValues<'core>,
) -> Result<Value<'core>, Error<'core>> {
    match callee {
        Value::Neutral(head, mut spine) => {
            spine.push(Elim::FunApp(arg));
            Ok(Value::Neutral(head, spine))
        }
        Value::FunLit(param, body) if param.plicity == arg.plicity => {
            beta_reduce(body, arg.expr, opts, meta_values)
        }
        Value::FunLit(param, _) => Err(Error::FunAppPlicityMismatch {
            param_plicity: param.plicity,
            arg_plicity: arg.plicity,
        }),
        _ => Err(Error::CalleeNotFun { callee }),
    }
}

/// Beta reduction: `(fun x => body)(arg)` -> `body[x := arg]`.
pub fn beta_reduce<'core>(
    closure: Closure<'core>,
    arg: Value<'core>,
    opts: UnfoldOpts,
    meta_values: &MetaValues<'core>,
) -> Result<Value<'core>, Error<'core>> {
    let Closure {
        mut local_values,
        body,
    } = closure;
    local_values.push(arg);
    eval::eval(body, opts, &mut local_values, meta_values)
}

/// Substitute meta variables in neutral spines with their values.
pub fn update_metas<'core>(
    value: &Value<'core>,
    meta_values: &MetaValues<'core>,
) -> Result<Value<'core>, Error<'core>> {
    let mut value = value.clone();
    while let Value::Neutral(Head::MetaVar(var), spine) = value {
        match meta_values.get_absolute(var) {
            None => {
                return Err(Error::UnboundMetaVar {
                    var,
                    len: meta_values.len(),
                })
            }
            Some(None) => return Ok(Value::Neutral(Head::MetaVar(var), spine)),
            Some(Some(head)) => {
                value = spine
                    .into_iter()
                    .try_fold(head.clone(), |head, elim| match elim {
                        Elim::FunApp(arg) => apply(head, arg, UnfoldOpts::for_quote(), meta_values),
                    })?;
            }
        }
    }
    Ok(value)
}
