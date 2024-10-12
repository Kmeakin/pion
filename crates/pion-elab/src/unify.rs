use codespan_reporting::diagnostic::Diagnostic;
use pion_core::env::{
    DeBruijn, DeBruijnIndex, DeBruijnLevel, EnvLen, SharedEnv, SliceEnv, UniqueEnv,
};
use pion_core::semantics::{
    self, Closure, Elim, Head, LocalValues, MetaValues, Type, UnfoldOpts, Value,
};
use pion_core::syntax::{Expr, FunArg, FunParam, LocalVar, MetaVar, Name};

/// Unification environment.
pub struct UnifyEnv<'env, 'core> {
    bump: &'core bumpalo::Bump,
    renaming: &'env mut PartialRenaming,
    locals: EnvLen,
    metas: &'env mut MetaValues<'core>,
}

/// A partial renaming from a source environment to a target environment.
#[derive(Default)]
pub struct PartialRenaming {
    /// Mapping from local variables in the source environment to local
    /// variables in the target environment.
    source: UniqueEnv<Option<DeBruijnLevel>>,
    /// The length of the target binding environment
    target: EnvLen,
}

impl PartialRenaming {
    /// Re-initialize the renaming to the requested `source_len`, reusing the
    /// previous allocation.
    fn init(&mut self, source_len: EnvLen) {
        self.source.clear();
        self.source.resize(source_len, None);
        self.target.clear();
    }

    fn next_local_var<'core>(&self, name: Name<'core>) -> Value<'core> {
        Value::local_var(LocalVar::new(name, self.source.len().to_level()))
    }

    /// Set a local source variable to local target variable mapping, ensuring
    /// that the variable appears uniquely.
    ///
    /// # Returns
    ///
    /// - `true` if the local binding was set successfully.
    /// - `false` if the local binding was already set.
    fn set_local(&mut self, source_var: LocalVar<DeBruijnLevel>) -> bool {
        let is_unique = self.get_local(source_var).is_none();

        if is_unique {
            let target_var = Some(self.target.to_level());
            self.source.set(source_var, target_var);
            self.target.push();
        }

        is_unique
    }

    /// Push an extra local binding onto the renaming.
    fn push_local(&mut self) {
        let target_var = self.target.to_level();
        self.source.push(Some(target_var));
        self.target.push();
    }

    /// Pop a local binding off the renaming.
    fn pop_local(&mut self) {
        self.source.pop();
        self.target.pop();
    }

    /// Get the local variable in the target environment that will be used in
    /// place of the `source_var`.
    fn get_local(&self, source_var: LocalVar<DeBruijnLevel>) -> Option<DeBruijnLevel> {
        self.source.get(source_var).copied().flatten()
    }

    /// Rename a local variable in the source environment to a local variable in
    /// the target environment.
    fn rename_local<'core>(
        &self,
        source_var: LocalVar<'core, DeBruijnLevel>,
    ) -> Option<LocalVar<'core, DeBruijnIndex>> {
        let target_var = self.get_local(source_var)?;
        Some(LocalVar::new(
            source_var.name,
            target_var.to_index(self.target).unwrap(),
        ))
    }
}

impl<'env, 'core> UnifyEnv<'env, 'core> {
    pub fn new(
        bump: &'core bumpalo::Bump,
        renaming: &'env mut PartialRenaming,
        locals: EnvLen,
        metas: &'env mut SliceEnv<Option<Value<'core>>>,
    ) -> Self {
        Self {
            bump,
            renaming,
            locals,
            metas,
        }
    }

    fn elim_env(&self) -> semantics::ElimEnv<'_, 'core> {
        semantics::ElimEnv::new(self.bump, UnfoldOpts::for_eval(), self.metas)
    }

    fn eval_env(
        &'env self,
        locals: &'env mut LocalValues<'core>,
    ) -> semantics::EvalEnv<'env, 'core> {
        semantics::EvalEnv::new(self.bump, UnfoldOpts::for_eval(), locals, self.metas)
    }

    /// Unify two values, updating the solution environment if necessary.
    pub fn unify(
        &mut self,
        left: &Value<'core>,
        right: &Value<'core>,
    ) -> Result<(), UnifyError<'core>> {
        if std::ptr::eq(left, right) {
            return Ok(());
        }

        let left = self.elim_env().subst_metas(left);
        let right = self.elim_env().subst_metas(right);

        match (left, right) {
            (Value::Lit(left), Value::Lit(right)) if left == right => Ok(()),

            (
                Value::Neutral(Head::LocalVar(left_var), left_spine),
                Value::Neutral(Head::LocalVar(right_var), right_spine),
            ) if left_var.de_bruijn == right_var.de_bruijn => {
                self.unify_spines(&left_spine, &right_spine)
            }

            (
                Value::Neutral(Head::MetaVar(left_var), left_spine),
                Value::Neutral(Head::MetaVar(right_var), right_spine),
            ) if left_var == right_var => self.unify_spines(&left_spine, &right_spine),

            (
                Value::Neutral(Head::PrimVar(left_var), left_spine),
                Value::Neutral(Head::PrimVar(right_var), right_spine),
            ) if left_var == right_var => self.unify_spines(&left_spine, &right_spine),

            (
                Value::FunType(left_param, left_closure),
                Value::FunType(right_param, right_closure),
            )
            | (
                Value::FunLit(left_param, left_closure),
                Value::FunLit(right_param, right_closure),
            ) => self.unify_funs(left_param, left_closure, right_param, right_closure),

            // Unify a function literal with a value, using eta-conversion:
            // `(fun x => f x) ?= f`
            (Value::FunLit(param, closure), value) | (value, Value::FunLit(param, closure)) => {
                let left_var = Value::local_var(LocalVar::new(param.name, self.locals.to_level()));
                let right_var = Value::local_var(LocalVar::new(param.name, self.locals.to_level()));

                let left_value = self.elim_env().apply_closure(closure, left_var);
                let right_value = self
                    .elim_env()
                    .fun_app(value, FunArg::new(param.plicity, right_var));

                self.locals.push();
                let result = self.unify(&left_value, &right_value);
                self.locals.pop();

                result
            }

            // One of the values has a metavariable at its head, so we
            // attempt to solve it using pattern unification.
            (Value::Neutral(Head::MetaVar(var), spine), value)
            | (value, Value::Neutral(Head::MetaVar(var), spine)) => self.solve(var, &spine, &value),

            _ => Err(UnifyError::Mismatch),
        }
    }

    /// Unify two elimination spines.
    fn unify_spines(
        &mut self,
        left_spine: &[Elim<'core>],
        right_spine: &[Elim<'core>],
    ) -> Result<(), UnifyError<'core>> {
        if left_spine.len() != right_spine.len() {
            return Err(UnifyError::Mismatch);
        }

        for (left_elim, right_elim) in Iterator::zip(left_spine.iter(), right_spine.iter()) {
            match (left_elim, right_elim) {
                (Elim::FunApp(left_arg), Elim::FunApp(right_arg))
                    if left_arg.plicity == right_arg.plicity =>
                {
                    self.unify(&left_arg.expr, &right_arg.expr)?;
                }
                _ => return Err(UnifyError::Mismatch),
            }
        }
        Ok(())
    }

    /// Unify two [closures][Closure].
    fn unify_funs(
        &mut self,
        left_param: FunParam<'core, &'core Type<'core>>,
        left_closure: Closure<'core>,
        right_param: FunParam<'core, &'core Type<'core>>,
        right_closure: Closure<'core>,
    ) -> Result<(), UnifyError<'core>> {
        if left_param.plicity != right_param.plicity {
            return Err(UnifyError::Mismatch);
        }

        self.unify(left_param.r#type, right_param.r#type)?;

        let left_var = Value::local_var(LocalVar::new(left_param.name, self.locals.to_level()));
        let right_var = Value::local_var(LocalVar::new(right_param.name, self.locals.to_level()));

        let left_value = self.elim_env().apply_closure(left_closure, left_var);
        let right_value = self.elim_env().apply_closure(right_closure, right_var);

        self.locals.push();
        let result = self.unify(&left_value, &right_value);
        self.locals.pop();

        result
    }

    /// Solve a pattern unification problem that looks like:
    ///
    /// ```text
    /// ?α spine =? value`
    /// ```
    ///
    /// If successful, the metavariable environment will be updated with a
    /// solution that looks something like:
    ///
    /// ```text
    /// ?α := fun spine => value
    /// ```
    fn solve(
        &mut self,
        meta_var: MetaVar,
        spine: &[Elim<'core>],
        value: &Value<'core>,
    ) -> Result<(), UnifyError<'core>> {
        self.init_renaming(spine)?;
        let expr = self.rename(meta_var, value)?;
        let fun_expr = self.fun_intros(spine, expr);
        let mut local_values = SharedEnv::new();
        let solution = self.eval_env(&mut local_values).eval(&fun_expr);
        self.metas.set(meta_var, Some(solution));
        Ok(())
    }

    /// Re-initialize the [`UnificationCtx::renaming`] by mapping the local
    /// variables in the spine to the local variables in the solution. This
    /// can fail if the spine does not contain distinct local variables.
    fn init_renaming(&mut self, spine: &[Elim<'core>]) -> Result<(), SpineError<'core>> {
        self.renaming.init(self.locals);

        for elim in spine {
            match elim {
                Elim::FunApp(arg) => match self.elim_env().subst_metas(&arg.expr) {
                    Value::Neutral(Head::LocalVar(var), spine)
                        if spine.is_empty() && self.renaming.set_local(var) => {}
                    Value::Neutral(Head::LocalVar(var), _) => {
                        return Err(SpineError::NonLinearSpine(var))
                    }
                    _ => return Err(SpineError::NonLocalFunApp),
                },
                Elim::If(..) => return Err(SpineError::If),
            }
        }
        Ok(())
    }

    /// Wrap `expr` in [function literals][Expr::FunLit] that correspond to the
    /// given `spine`.
    fn fun_intros(&self, spine: &[Elim<'core>], expr: Expr<'core>) -> Expr<'core> {
        spine.iter().fold(expr, |expr, elim| match elim {
            Elim::FunApp(arg) => Expr::FunLit(
                FunParam::new(arg.plicity, None, &Expr::Error),
                self.bump.alloc(expr),
            ),
            Elim::If(..) => unreachable!("should have been caught by `init_renaming`"),
        })
    }

    /// Rename `value` to an [`Expr`], while at the same time using the current
    /// renaming to update variable indices, failing if the partial renaming is
    /// not defined (resulting in an [scope error][Error::ScopeError]), and also
    /// checking for occurrences of the `meta_var` (resulting in an [occurs
    /// check error][Error::InfiniteSolution]).
    ///
    /// This allows us to subsequently wrap the returned expr in function
    /// literals, using [`UnificationContext::function_intros`].
    fn rename(
        &mut self,
        meta_var: MetaVar,
        value: &Value<'core>,
    ) -> Result<Expr<'core>, RenameError<'core>> {
        let value = self.elim_env().subst_metas(value);
        match value {
            Value::Lit(lit) => Ok(Expr::Lit(lit)),
            Value::Neutral(head, spine) => {
                let head = match head {
                    Head::Error => Expr::Error,
                    Head::PrimVar(var) => Expr::PrimVar(var),
                    Head::LocalVar(var) => match self.renaming.rename_local(var) {
                        None => return Err(RenameError::EscapingLocalVar(var)),
                        Some(var) => Expr::LocalVar(var),
                    },
                    Head::MetaVar(var) => match meta_var == var {
                        true => return Err(RenameError::InfiniteSolution),
                        false => Expr::MetaVar(var),
                    },
                };
                spine.iter().try_fold(head, |head, elim| match elim {
                    Elim::FunApp(arg) => {
                        let arg_expr = self.rename(meta_var, &arg.expr)?;
                        let (fun, arg_expr) = self.bump.alloc((head, arg_expr));
                        let arg = FunArg::new(arg.plicity, &*arg_expr);
                        Ok(Expr::FunApp(fun, arg))
                    }
                    Elim::If(locals, then, r#else) => {
                        let mut locals = locals.clone();
                        let then = {
                            let value = self.eval_env(&mut locals).eval(then);
                            self.rename(meta_var, &value)?
                        };
                        let r#else = {
                            let value = self.eval_env(&mut locals).eval(r#else);
                            self.rename(meta_var, &value)?
                        };
                        let (cond, then, r#else) = self.bump.alloc((head, then, r#else));
                        Ok(Expr::If(cond, then, r#else))
                    }
                })
            }
            Value::FunType(param, closure) => {
                let (param, body) = self.rename_closure(meta_var, param, closure)?;
                Ok(Expr::FunType(param, body))
            }
            Value::FunLit(param, closure) => {
                let (param, body) = self.rename_closure(meta_var, param, closure)?;
                Ok(Expr::FunLit(param, body))
            }
        }
    }

    /// Rename a closure back into an [`Expr`].
    fn rename_closure(
        &mut self,
        meta_var: MetaVar,
        param: FunParam<'core, &'core Value<'core>>,
        closure: Closure<'core>,
    ) -> Result<(FunParam<'core, &'core Expr<'core>>, &'core Expr<'core>), RenameError<'core>> {
        let param_type = self.rename(meta_var, param.r#type)?;

        let var = self.renaming.next_local_var(param.name);
        let body = self.elim_env().apply_closure(closure, var);

        self.renaming.push_local();
        let body = self.rename(meta_var, &body);
        self.renaming.pop_local();

        let (param_type, body) = self.bump.alloc((param_type, body?));
        let param = FunParam::new(param.plicity, param.name, &*param_type);
        Ok((param, body))
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum UnifyError<'core> {
    /// A known part of one value failed to match with a known part of the other
    /// value that we are comparing against.
    //
    // TODO: Return some sort of type-diff
    Mismatch,
    /// An error that was found in the problem spine.
    Spine(SpineError<'core>),
    /// An error that occurred when renaming the solution.
    Rename(RenameError<'core>),
}

impl<'core> UnifyError<'core> {
    pub fn to_diagnostic(self, from: &Expr<'core>, to: &Expr<'core>) -> Diagnostic<usize> {
        match self {
            Self::Mismatch => Diagnostic::error()
                .with_message(format!("Type mismatch: expected `{to}`, found `{from}`")),

            Self::Spine(SpineError::NonLinearSpine(..)) => Diagnostic::error()
                .with_message("variable appeared more than once in problem spine"),
            Self::Spine(SpineError::NonLocalFunApp) => Diagnostic::error()
                .with_message("non-variable function application in problem spine"),
            Self::Spine(SpineError::If) => {
                Diagnostic::error().with_message("`if` expression in problem spine")
            }

            Self::Rename(RenameError::EscapingLocalVar(_)) => {
                Diagnostic::error().with_message("escaping local variable in problem spine")
            }
            Self::Rename(RenameError::InfiniteSolution) => {
                Diagnostic::error().with_message("infinite solution")
            }
        }
    }
}

impl<'core> From<SpineError<'core>> for UnifyError<'core> {
    fn from(error: SpineError<'core>) -> Self { Self::Spine(error) }
}

impl<'core> From<RenameError<'core>> for UnifyError<'core> {
    fn from(error: RenameError<'core>) -> Self { Self::Rename(error) }
}

/// An error that was found in the spine of a unification problem.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum SpineError<'core> {
    /// A local variable appeared multiple times in the spine of a unification
    /// problem.
    ///
    /// For example:
    ///
    /// ```text
    /// ?α x x =? x`
    /// ```
    ///
    /// This results in two distinct solutions:
    ///
    /// - `?α := fun x _ => x`
    /// - `?α := fun _ x => x`
    ///
    /// We only want unification to result in a unique solution, so we fail
    /// to unify in this case.
    ///
    /// Another example, assuming `true : Bool`, is:
    ///
    /// ```text
    /// ?α true =? true
    /// ```
    ///
    /// This also has multiple solutions, for example:
    ///
    /// - `?α := fun _ => true`
    /// - `?α := fun x => x`
    /// - `?α := fun x => if x then true else false`
    ///
    /// It's also possible that the return type of `?α` is not always `Bool`,
    /// for example:
    ///
    /// ```text
    /// ?α : fun (b : Bool) -> if b then Bool else (Bool -> Bool)
    /// ```
    ///
    /// In this case the example solution `?α := fun _ => true` is not even
    /// well-typed! In contrast, if the problem spine only has distinct local
    /// variables, even if the return type is dependent, local variables block
    /// all computation in the return type, and the pattern solution is
    /// guaranteed to be well-typed.
    NonLinearSpine(LocalVar<'core, DeBruijnLevel>),
    /// A function application was in the problem spine, but it wasn't a local
    /// variable.
    NonLocalFunApp,
    If,
}

/// An error that occurred when renaming the solution.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum RenameError<'core> {
    /// A free local variable in the compared value does not occur in the
    /// problem spine.
    ///
    /// For example, where `z : Type` is a local variable:
    ///
    /// ```text
    /// ?α x y =? z -> z
    /// ```
    ///
    /// There is no solution for this metavariable because `?α` is the
    /// topmost-level scope, so it can only abstract over `x` and `y`, but
    /// these don't occur in `z -> z`.
    EscapingLocalVar(LocalVar<'core, DeBruijnLevel>),

    /// The metavariable occurs in the value being compared against.
    /// This is sometimes referred to as an 'occurs check' failure.
    ///
    /// For example:
    ///
    /// ```text
    /// ?α =? ?α -> ?α
    /// ```
    ///
    /// Here `?α` occurs in the right hand side, so in order to solve this
    /// metavariable we would end up going into an infinite loop,
    /// attempting to construct larger and larger solutions:
    ///
    /// - `?α =? ?α -> ?α`
    /// - `?α =? (?α -> ?α) -> (?α -> ?α)`
    /// - `?α =? ((?α -> ?α) -> (?α -> ?α)) -> ((?α -> ?α) -> (?α -> ?α))`
    InfiniteSolution,
}

#[cfg(test)]
mod tests {
    use pion_core::prim::PrimVar;
    use semantics::eco_vec;

    use super::*;

    #[track_caller]
    fn assert_unify<'core>(
        lhs: &Value<'core>,
        rhs: &Value<'core>,
        expected: Result<(), UnifyError>,
    ) {
        let bump = bumpalo::Bump::new();
        let mut renaming = PartialRenaming::default();
        let locals = EnvLen::default();
        let mut metas = UniqueEnv::default();
        let mut env = UnifyEnv::new(&bump, &mut renaming, locals, &mut metas);
        let result = env.unify(lhs, rhs);
        assert_eq!(result, expected);
    }

    #[test]
    fn unify_bool() {
        let tt = Value::bool(true);
        let ff = Value::bool(false);

        assert_unify(&tt, &tt, Ok(()));
        assert_unify(&ff, &ff, Ok(()));
        assert_unify(&tt, &ff, Err(UnifyError::Mismatch));
        assert_unify(&ff, &tt, Err(UnifyError::Mismatch));
    }

    #[test]
    fn unify_int() {
        let zero = Value::int(0);
        let one = Value::int(1);

        assert_unify(&zero, &zero, Ok(()));
        assert_unify(&one, &one, Ok(()));
        assert_unify(&zero, &one, Err(UnifyError::Mismatch));
        assert_unify(&one, &zero, Err(UnifyError::Mismatch));
    }

    #[test]
    fn unify_char() {
        let a = Value::char('a');
        let b = Value::char('b');

        assert_unify(&a, &a, Ok(()));
        assert_unify(&b, &b, Ok(()));
        assert_unify(&a, &b, Err(UnifyError::Mismatch));
        assert_unify(&b, &a, Err(UnifyError::Mismatch));
    }

    #[test]
    fn unify_string() {
        let a = Value::string("a");
        let b = Value::string("b");

        assert_unify(&a, &a, Ok(()));
        assert_unify(&b, &b, Ok(()));
        assert_unify(&a, &b, Err(UnifyError::Mismatch));
        assert_unify(&b, &a, Err(UnifyError::Mismatch));
    }

    #[test]
    fn unify_fun_type() {
        let bool = Type::BOOL;
        let var = Expr::LocalVar(LocalVar::new(None, DeBruijnIndex::new(0)));
        let lhs = Value::FunType(FunParam::explicit(None, &bool), Closure::empty(&var));
        let rhs = Value::FunType(FunParam::implicit(None, &bool), Closure::empty(&var));

        assert_unify(&lhs, &lhs, Ok(()));
        assert_unify(&rhs, &rhs, Ok(()));
        assert_unify(&lhs, &rhs, Err(UnifyError::Mismatch));
        assert_unify(&rhs, &lhs, Err(UnifyError::Mismatch));
    }

    #[test]
    fn unify_fun_lit() {
        let bool = Type::BOOL;
        let var = Expr::LocalVar(LocalVar::new(None, DeBruijnIndex::new(0)));
        let lhs = Value::FunLit(FunParam::explicit(None, &bool), Closure::empty(&var));
        let rhs = Value::FunLit(FunParam::implicit(None, &bool), Closure::empty(&var));

        assert_unify(&lhs, &lhs, Ok(()));
        assert_unify(&rhs, &rhs, Ok(()));
        assert_unify(&lhs, &rhs, Err(UnifyError::Mismatch));
        assert_unify(&rhs, &lhs, Err(UnifyError::Mismatch));
    }

    #[test]
    fn unify_fun_lit_eta() {
        // `fun(x : Int) => Bool(x) == Bool`
        let int = Type::INT;
        let var = Expr::LocalVar(LocalVar::new(None, DeBruijnIndex::new(0)));
        let body = Expr::FunApp(&Expr::BOOL, FunArg::explicit(&var));
        let lhs = Value::FunLit(FunParam::explicit(None, &int), Closure::empty(&body));
        let rhs = Value::BOOL;
        assert_unify(&lhs, &rhs, Ok(()));
        assert_unify(&rhs, &lhs, Ok(()));
    }

    #[test]
    fn unify_prims() {
        let lhs = Value::prim_var(PrimVar::Bool);
        let rhs = Value::prim_var(PrimVar::Int);
        assert_unify(&lhs, &lhs, Ok(()));
        assert_unify(&rhs, &rhs, Ok(()));
        assert_unify(&lhs, &rhs, Err(UnifyError::Mismatch));
        assert_unify(&rhs, &lhs, Err(UnifyError::Mismatch));
    }

    #[test]
    fn unify_locals() {
        let lhs = Value::local_var(LocalVar::new(None, DeBruijnLevel::new(0)));
        let rhs = Value::local_var(LocalVar::new(None, DeBruijnLevel::new(1)));
        assert_unify(&lhs, &lhs, Ok(()));
        assert_unify(&rhs, &rhs, Ok(()));
        assert_unify(&lhs, &rhs, Err(UnifyError::Mismatch));
        assert_unify(&rhs, &lhs, Err(UnifyError::Mismatch));

        let lhs = Value::Neutral(
            Head::LocalVar(LocalVar::new(None, DeBruijnLevel::new(0))),
            eco_vec![Elim::FunApp(FunArg::explicit(Value::int(42)))],
        );
        let rhs = Value::Neutral(
            Head::LocalVar(LocalVar::new(None, DeBruijnLevel::new(0))),
            eco_vec![Elim::FunApp(FunArg::explicit(Value::int(24)))],
        );
        assert_unify(&lhs, &lhs, Ok(()));
        assert_unify(&rhs, &rhs, Ok(()));
        assert_unify(&lhs, &rhs, Err(UnifyError::Mismatch));
        assert_unify(&rhs, &lhs, Err(UnifyError::Mismatch));
    }
}
