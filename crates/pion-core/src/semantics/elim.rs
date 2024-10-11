//! Elimination rules

use super::*;
use crate::syntax::Plicity;

#[derive(Debug, Copy, Clone)]
pub struct ElimEnv<'env, 'core> {
    bump: &'core bumpalo::Bump,
    opts: UnfoldOpts,
    metas: &'env MetaValues<'core>,
}

impl<'env, 'core> ElimEnv<'env, 'core> {
    pub fn new(
        bump: &'core bumpalo::Bump,
        opts: UnfoldOpts,
        metas: &'env MetaValues<'core>,
    ) -> Self {
        Self { bump, opts, metas }
    }

    pub fn fun_app(self, callee: Value<'core>, arg: FunArg<Value<'core>>) -> Value<'core> {
        fun_app(callee, arg, self.bump, self.opts, self.metas)
    }

    pub fn apply_closure(self, closure: Closure<'core>, arg: Value<'core>) -> Value<'core> {
        apply_closure(closure, arg, self.bump, self.opts, self.metas)
    }

    pub fn subst_metas(self, value: &Value<'core>) -> Value<'core> {
        subst_metas(value, self.bump, self.opts, self.metas)
    }
}

fn apply_eliminator<'core>(
    head: Value<'core>,
    elim: Elim<'core>,
    bump: &'core bumpalo::Bump,
    opts: UnfoldOpts,
    metas: &MetaValues<'core>,
) -> Value<'core> {
    match elim {
        Elim::FunApp(arg) => fun_app(head, arg, bump, opts, metas),
    }
}

fn apply_spine<'core>(
    head: Value<'core>,
    spine: Spine<'core>,
    bump: &'core bumpalo::Bump,
    opts: UnfoldOpts,
    metas: &MetaValues<'core>,
) -> Value<'core> {
    spine.into_iter().fold(head, |head, elim| {
        apply_eliminator(head, elim, bump, opts, metas)
    })
}

fn prim_app<'core>(var: PrimVar, spine: Spine<'core>, arg: FunArg<Value<'core>>) -> Value<'core> {
    fn neutral<'core>(
        var: PrimVar,
        mut spine: Spine<'core>,
        arg: FunArg<Value<'core>>,
    ) -> Value<'core> {
        spine.push(Elim::FunApp(arg));
        Value::Neutral(Head::PrimVar(var), spine)
    }

    macro_rules! match_args {
        ($(let $pat:pat = $place:expr ;)* $body:expr) => {{
            $(
                let $pat = $place else {
                    return neutral(var, spine, arg);
                };
            )*

            $body
        }};
    }

    match var {
        PrimVar::add => match_args! {
            let 1 = spine.len();
            let Some(Elim::FunApp(FunArg { plicity:Plicity::Explicit, expr: Value::Lit(Lit::Int(lhs)) })) = spine.first();
            let FunArg { plicity: Plicity::Explicit, expr: Value::Lit(Lit::Int(rhs)) } = arg;
            Value::int(u32::wrapping_add(*lhs, rhs))
        },
        PrimVar::sub => match_args! {
            let 1 = spine.len();
            let Some(Elim::FunApp(FunArg { plicity:Plicity::Explicit, expr: Value::Lit(Lit::Int(lhs)) })) = spine.first();
            let FunArg { plicity: Plicity::Explicit, expr: Value::Lit(Lit::Int(rhs)) } = arg;
            Value::int(u32::wrapping_sub(*lhs, rhs))
        },
        PrimVar::mul => match_args! {
            let 1 = spine.len();
            let Some(Elim::FunApp(FunArg { plicity:Plicity::Explicit, expr: Value::Lit(Lit::Int(lhs)) })) = spine.first();
            let FunArg { plicity: Plicity::Explicit, expr: Value::Lit(Lit::Int(rhs)) } = arg;
            Value::int(u32::wrapping_mul(*lhs, rhs))
        },

        PrimVar::Type
        | PrimVar::Bool
        | PrimVar::Int
        | PrimVar::Char
        | PrimVar::String
        | PrimVar::Unit
        | PrimVar::unit
        | PrimVar::Eq
        | PrimVar::refl
        | PrimVar::subst => neutral(var, spine, arg),
    }
}

/// Apply `arg` to `callee`.
/// Performs beta reduction if `callee` is a lambda.
pub(super) fn fun_app<'core>(
    callee: Value<'core>,
    arg: FunArg<Value<'core>>,
    bump: &'core bumpalo::Bump,
    opts: UnfoldOpts,
    metas: &MetaValues<'core>,
) -> Value<'core> {
    match callee {
        Value::Neutral(Head::PrimVar(var), spine) => prim_app(var, spine, arg),
        Value::Neutral(head, mut spine) => {
            spine.push(Elim::FunApp(arg));
            Value::Neutral(head, spine)
        }
        Value::FunLit(param, body) if param.plicity == arg.plicity => {
            apply_closure(body, arg.expr, bump, opts, metas)
        }
        _ => Value::ERROR,
    }
}

/// Beta reduction: `(fun x => body)(arg)` -> `body[x := arg]`.
pub(super) fn apply_closure<'core>(
    closure: Closure<'core>,
    arg: Value<'core>,
    bump: &'core bumpalo::Bump,
    opts: UnfoldOpts,
    metas: &MetaValues<'core>,
) -> Value<'core> {
    let Closure {
        mut local_values,
        body,
    } = closure;
    local_values.push(arg);
    eval::eval(body, bump, opts, &mut local_values, metas)
}

/// Substitute meta variables in neutral spines with their values, and reduce
/// further if possible.
pub(super) fn subst_metas<'core>(
    value: &Value<'core>,
    bump: &'core bumpalo::Bump,
    opts: UnfoldOpts,
    metas: &MetaValues<'core>,
) -> Value<'core> {
    let mut value = value.clone();
    while let Value::Neutral(Head::MetaVar(var), spine) = value {
        match metas.get(var) {
            None => return Value::ERROR,
            Some(None) => return Value::Neutral(Head::MetaVar(var), spine),
            Some(Some(head)) => {
                value = apply_spine(head.clone(), spine, bump, opts, metas);
            }
        }
    }
    value
}

#[cfg(test)]
mod tests {

    use ecow::eco_vec;

    use super::*;
    use crate::env::UniqueEnv;

    #[test]
    fn test_apply_neutral() {
        // `_#0(42)``
        let bump = bumpalo::Bump::new();
        let var = LocalVar::new(None, DeBruijnLevel::new(0));
        let callee = Value::local_var(var);
        let arg = FunArg::explicit(Value::int(42));
        let opts = UnfoldOpts::for_eval();
        let meta_values = UniqueEnv::default();
        let result = fun_app(callee, arg.clone(), &bump, opts, &meta_values);

        assert_eq!(
            result,
            Value::Neutral(Head::LocalVar(var), eco_vec![Elim::FunApp(arg)])
        );
    }

    #[test]
    fn test_subst_metas_unbound() {
        let bump = bumpalo::Bump::new();
        let var = MetaVar::new(DeBruijnLevel::new(0));
        let value = Value::meta_var(var);
        let metas = UniqueEnv::default();
        let result = subst_metas(&value, &bump, UnfoldOpts::for_eval(), &metas);
        assert_eq!(result, Value::ERROR);
    }

    #[test]
    fn test_subst_metas_bound() {
        // `?0(24)` in `[Some(fun x => 42)]`
        let bump = bumpalo::Bump::new();
        let int = Expr::int(42);
        let ty = Type::INT;
        let mut metas = UniqueEnv::default();
        metas.push(Some(Value::FunLit(
            FunParam::explicit(None, &ty),
            Closure::empty(&int),
        )));

        let value = Value::Neutral(
            Head::MetaVar(MetaVar::new(DeBruijnLevel::new(0))),
            eco_vec![Elim::FunApp(FunArg::explicit(Value::int(24)))],
        );

        let result = subst_metas(&value, &bump, UnfoldOpts::for_eval(), &metas);
        assert_eq!(result, (Value::int(42)));

        // `?0(24)` in `[None]`
        metas.clear();
        metas.push(None);
        let result = subst_metas(&value, &bump, UnfoldOpts::for_eval(), &metas);
        assert_eq!(result, value);
    }

    #[test]
    fn test_subst_metas_reduce() {
        // `?0(24)` in `[Some(fun x => 42)]`
        let bump = bumpalo::Bump::new();
        let int = Expr::int(42);
        let ty = Type::INT;
        let var = DeBruijnLevel::new(0);
        let value = Value::Neutral(
            Head::MetaVar(MetaVar::new(var)),
            eco_vec![Elim::FunApp(FunArg::explicit(Value::int(24)))],
        );
        let mut metas = UniqueEnv::default();
        metas.push(Some(Value::FunLit(
            FunParam::explicit(None, &ty),
            Closure::empty(&int),
        )));
        let result = subst_metas(&value, &bump, UnfoldOpts::for_eval(), &metas);
        assert_eq!(result, Value::int(42));
    }
}
