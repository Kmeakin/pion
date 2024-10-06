use codespan_reporting::diagnostic::Diagnostic;
use pion_core::env::{AbsoluteVar, EnvLen, RelativeVar, SharedEnv, SliceEnv, UniqueEnv};
use pion_core::semantics::{self, Closure, Elim, Head, MetaValues, Type, UnfoldOpts, Value};
use pion_core::syntax::{Expr, FunArg, FunParam};

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
    source: UniqueEnv<Option<AbsoluteVar>>,
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

    fn next_local_var<'core>(&self) -> Value<'core> {
        Value::local_var(self.source.len().to_absolute())
    }

    /// Set a local source variable to local target variable mapping, ensuring
    /// that the variable appears uniquely.
    ///
    /// # Returns
    ///
    /// - `true` if the local binding was set successfully.
    /// - `false` if the local binding was already set.
    fn set_local(&mut self, source_var: AbsoluteVar) -> bool {
        let is_unique = self.get_as_absolute(source_var).is_none();

        if is_unique {
            let target_var = Some(self.target.to_absolute());
            self.source.set_absolute(source_var, target_var);
            self.target.push();
        }

        is_unique
    }

    /// Push an extra local binding onto the renaming.
    fn push_local(&mut self) {
        let target_var = self.target.to_absolute();
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
    fn get_as_absolute(&self, source_var: AbsoluteVar) -> Option<AbsoluteVar> {
        self.source.get_absolute(source_var).copied().flatten()
    }

    /// Rename a local variable in the source environment to a local variable in
    /// the target environment.
    fn get_as_relative(&self, source_var: AbsoluteVar) -> Option<RelativeVar> {
        let target_var = self.get_as_absolute(source_var)?;
        Some(self.target.absolute_to_relative(target_var).unwrap())
    }

    fn len(&self) -> (EnvLen, EnvLen) { (self.source.len(), self.target) }

    fn truncate(&mut self, (source_len, target_len): (EnvLen, EnvLen)) {
        self.source.truncate(source_len);
        self.target.truncate(target_len);
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
        semantics::ElimEnv::new(UnfoldOpts::for_eval(), self.metas)
    }

    /// Unify two values, updating the solution environment if necessary.
    pub fn unify(&mut self, left: &Value<'core>, right: &Value<'core>) -> Result<(), UnifyError> {
        if std::ptr::eq(left, right) {
            return Ok(());
        }

        let left = self.elim_env().subst_metas(left);
        let right = self.elim_env().subst_metas(right);

        match (left, right) {
            (Value::Bool(left), Value::Bool(right)) if left == right => Ok(()),
            (Value::Int(left), Value::Int(right)) if left == right => Ok(()),
            (Value::Char(left), Value::Char(right)) if left == right => Ok(()),
            (Value::String(left), Value::String(right)) if left == right => Ok(()),

            (Value::Neutral(left_head, left_spine), Value::Neutral(right_head, right_spine))
                if left_head == right_head =>
            {
                self.unify_spines(&left_spine, &right_spine)
            }

            (
                Value::FunType(left_param, left_closure),
                Value::FunType(right_param, right_closure),
            ) if left_param.plicity == right_param.plicity => {
                self.unify_closures(left_closure, right_closure)
            }
            (
                Value::FunLit(left_param, left_closure),
                Value::FunLit(right_param, right_closure),
            ) if left_param.plicity == right_param.plicity => {
                self.unify_closures(left_closure, right_closure)
            }

            // Unify a function literal with a value, using eta-conversion:
            // `(fun x => f x) ?= f`
            (Value::FunLit(param, closure), value) | (value, Value::FunLit(param, closure)) => {
                let left_var = Value::local_var(self.locals.to_absolute());
                let right_var = Value::local_var(self.locals.to_absolute());

                let left_value = self.elim_env().beta_reduce(closure, left_var);
                let right_value = self
                    .elim_env()
                    .apply_arg(value, FunArg::new(param.plicity, right_var));

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
    ) -> Result<(), UnifyError> {
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
    fn unify_closures(
        &mut self,
        left_closure: Closure<'core>,
        right_closure: Closure<'core>,
    ) -> Result<(), UnifyError> {
        let left_var = Value::local_var(self.locals.to_absolute());
        let right_var = Value::local_var(self.locals.to_absolute());

        let left_value = self.elim_env().beta_reduce(left_closure, left_var);
        let right_value = self.elim_env().beta_reduce(right_closure, right_var);

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
        meta_var: AbsoluteVar,
        spine: &[Elim<'core>],
        value: &Value<'core>,
    ) -> Result<(), UnifyError> {
        self.init_renaming(spine)?;
        let expr = self.rename(meta_var, value)?;
        let fun_expr = self.fun_intros(spine, expr);
        let mut local_values = SharedEnv::new();
        let solution =
            semantics::EvalEnv::new(UnfoldOpts::for_eval(), &mut local_values, self.metas)
                .eval(&fun_expr);
        self.metas.set_absolute(meta_var, Some(solution));
        Ok(())
    }

    /// Re-initialize the [`UnificationCtx::renaming`] by mapping the local
    /// variables in the spine to the local variables in the solution. This
    /// can fail if the spine does not contain distinct local variables.
    fn init_renaming(&mut self, spine: &[Elim<'core>]) -> Result<(), SpineError> {
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
        meta_var: AbsoluteVar,
        value: &Value<'core>,
    ) -> Result<Expr<'core>, RenameError> {
        let value = self.elim_env().subst_metas(value);
        match value {
            Value::Bool(b) => Ok(Expr::Bool(b)),
            Value::Int(n) => Ok(Expr::Int(n)),
            Value::Char(c) => Ok(Expr::Char(c)),
            Value::String(s) => Ok(Expr::String(s)),
            Value::Neutral(head, spine) => {
                let head = match head {
                    Head::Error => Expr::Error,
                    Head::PrimVar(var) => Expr::PrimVar(var),
                    Head::LocalVar(var) => match self.renaming.get_as_relative(var) {
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
                })
            }
            Value::FunType(param, closure) => {
                let closure = self.rename_closure(meta_var, closure)?;
                Ok(Expr::FunType(param, closure))
            }
            Value::FunLit(param, closure) => {
                let closure = self.rename_closure(meta_var, closure)?;
                Ok(Expr::FunLit(param, closure))
            }
        }
    }

    /// Rename a closure back into an [`Expr`].
    fn rename_closure(
        &mut self,
        meta_var: AbsoluteVar,
        closure: Closure<'core>,
    ) -> Result<&'core Expr<'core>, RenameError> {
        let var = self.renaming.next_local_var();
        let body = self.elim_env().beta_reduce(closure, var);

        self.renaming.push_local();
        let body = self.rename(meta_var, &body);
        self.renaming.pop_local();

        Ok(self.bump.alloc(body?))
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum UnifyError {
    /// A known part of one value failed to match with a known part of the other
    /// value that we are comparing against.
    //
    // TODO: Return some sort of type-diff
    Mismatch,
    /// An error that was found in the problem spine.
    Spine(SpineError),
    /// An error that occurred when renaming the solution.
    Rename(RenameError),
}

impl UnifyError {
    pub fn to_diagnostic<'core>(self, from: &Type<'core>, to: &Type<'core>) -> Diagnostic<usize> {
        match self {
            Self::Mismatch => Diagnostic::error()
                .with_message(format!("Type mismatch: expected `{to}`, found `{from}`")),

            Self::Spine(SpineError::NonLinearSpine(..)) => Diagnostic::error()
                .with_message("variable appeared more than once in problem spine"),
            Self::Spine(SpineError::NonLocalFunApp) => Diagnostic::error()
                .with_message("non-variable function application in problem spine"),

            Self::Rename(RenameError::EscapingLocalVar(_)) => {
                Diagnostic::error().with_message("escaping local variable in problem spine")
            }
            Self::Rename(RenameError::InfiniteSolution) => {
                Diagnostic::error().with_message("infinite solution")
            }
        }
    }
}

impl From<SpineError> for UnifyError {
    fn from(error: SpineError) -> Self { Self::Spine(error) }
}

impl From<RenameError> for UnifyError {
    fn from(error: RenameError) -> Self { Self::Rename(error) }
}

/// An error that was found in the spine of a unification problem.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum SpineError {
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
    NonLinearSpine(AbsoluteVar),
    /// A function application was in the problem spine, but it wasn't a local
    /// variable.
    NonLocalFunApp,
}

/// An error that occurred when renaming the solution.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum RenameError {
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
    EscapingLocalVar(AbsoluteVar),

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
        let tt = Value::Bool(true);
        let ff = Value::Bool(false);

        assert_unify(&tt, &tt, Ok(()));
        assert_unify(&ff, &ff, Ok(()));
        assert_unify(&tt, &ff, Err(UnifyError::Mismatch));
        assert_unify(&ff, &tt, Err(UnifyError::Mismatch));
    }

    #[test]
    fn unify_int() {
        let zero = Value::Int(0);
        let one = Value::Int(1);

        assert_unify(&zero, &zero, Ok(()));
        assert_unify(&one, &one, Ok(()));
        assert_unify(&zero, &one, Err(UnifyError::Mismatch));
        assert_unify(&one, &zero, Err(UnifyError::Mismatch));
    }

    #[test]
    fn unify_char() {
        let a = Value::Char('a');
        let b = Value::Char('b');

        assert_unify(&a, &a, Ok(()));
        assert_unify(&b, &b, Ok(()));
        assert_unify(&a, &b, Err(UnifyError::Mismatch));
        assert_unify(&b, &a, Err(UnifyError::Mismatch));
    }

    #[test]
    fn unify_string() {
        let a = Value::String("a");
        let b = Value::String("b");

        assert_unify(&a, &a, Ok(()));
        assert_unify(&b, &b, Ok(()));
        assert_unify(&a, &b, Err(UnifyError::Mismatch));
        assert_unify(&b, &a, Err(UnifyError::Mismatch));
    }

    #[test]
    fn unify_fun_type() {
        let var = Expr::LocalVar(RelativeVar::new(0));
        let lhs = Value::FunType(FunParam::explicit(None, &Expr::BOOL), Closure::empty(&var));
        let rhs = Value::FunType(FunParam::implicit(None, &Expr::BOOL), Closure::empty(&var));

        assert_unify(&lhs, &lhs, Ok(()));
        assert_unify(&rhs, &rhs, Ok(()));
        assert_unify(&lhs, &rhs, Err(UnifyError::Mismatch));
        assert_unify(&rhs, &lhs, Err(UnifyError::Mismatch));
    }

    #[test]
    fn unify_fun_lit() {
        let var = Expr::LocalVar(RelativeVar::new(0));
        let lhs = Value::FunLit(FunParam::explicit(None, &Expr::BOOL), Closure::empty(&var));
        let rhs = Value::FunLit(FunParam::implicit(None, &Expr::BOOL), Closure::empty(&var));

        assert_unify(&lhs, &lhs, Ok(()));
        assert_unify(&rhs, &rhs, Ok(()));
        assert_unify(&lhs, &rhs, Err(UnifyError::Mismatch));
        assert_unify(&rhs, &lhs, Err(UnifyError::Mismatch));
    }

    #[test]
    fn unify_fun_lit_eta() {
        // `fun(x : Int) => Bool(x) == Bool`
        let var = Expr::LocalVar(RelativeVar::new(0));
        let body = Expr::FunApp(&Expr::BOOL, FunArg::explicit(&var));
        let lhs = Value::FunLit(FunParam::explicit(None, &Expr::INT), Closure::empty(&body));
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
        let lhs = Value::local_var(AbsoluteVar::new(0));
        let rhs = Value::local_var(AbsoluteVar::new(1));
        assert_unify(&lhs, &lhs, Ok(()));
        assert_unify(&rhs, &rhs, Ok(()));
        assert_unify(&lhs, &rhs, Err(UnifyError::Mismatch));
        assert_unify(&rhs, &lhs, Err(UnifyError::Mismatch));

        let lhs = Value::Neutral(
            Head::LocalVar(AbsoluteVar::new(0)),
            eco_vec![Elim::FunApp(FunArg::explicit(Value::Int(42)))],
        );
        let rhs = Value::Neutral(
            Head::LocalVar(AbsoluteVar::new(0)),
            eco_vec![Elim::FunApp(FunArg::explicit(Value::Int(24)))],
        );
        assert_unify(&lhs, &lhs, Ok(()));
        assert_unify(&rhs, &rhs, Ok(()));
        assert_unify(&lhs, &rhs, Err(UnifyError::Mismatch));
        assert_unify(&rhs, &lhs, Err(UnifyError::Mismatch));
    }
}
