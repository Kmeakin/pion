use codespan_reporting::diagnostic::Diagnostic;
use compile::MatchResult;
use matrix::{PatMatrix, PatRow};
use pion_core::semantics::Type;
use pion_core::syntax::*;
use pion_surface::syntax as surface;
use pion_surface::syntax::Located;

use super::Check;
use crate::Elaborator;

mod compile;
mod constructors;
mod decompose;
mod matrix;

impl<'core> Elaborator<'core> {
    pub fn check_match_expr(
        &mut self,
        scrut: Located<&surface::Expr>,
        cases: &[Located<surface::MatchCase>],
        expected: &Type<'core>,
    ) -> Check<Expr<'core>> {
        let (scrut_expr, scrut_type) = self.synth_expr(scrut);

        let mut matrix =
            PatMatrix::with_capacity(self.bump, cases.len(), usize::from(!cases.is_empty()));
        let mut bodies = Vec::with_capacity_in(cases.len(), self.bump);

        for (index, case) in cases.iter().enumerate() {
            let len = self.env.locals.len();
            let pat = self.check_pat(case.data.pat.as_ref(), &scrut_type);
            let bindings = self.destruct_pat(&pat, &scrut_expr, &scrut_type, false);
            self.push_let_bindings(&bindings);
            let expr = self.check_expr(case.data.expr.as_ref(), expected);
            let expr = Expr::wrap_in_lets(self.bump, &bindings, expr);
            self.env.locals.truncate(len);

            matrix.push_row(PatRow::new(&[(pat, scrut_expr)], index));
            bodies.push(Body::Success { expr });
        }

        let MatchResult {
            expr,
            inexhaustive,
            reachable_rows,
        } = self.compile_match(&mut matrix, &bodies);

        for (idx, is_reachable) in reachable_rows.iter().enumerate() {
            if !is_reachable {
                self.diagnostic(
                    cases[idx].data.expr.range,
                    Diagnostic::warning().with_message("Unreachable match case"),
                );
            }
        }

        if inexhaustive {
            self.diagnostic(
                scrut.range,
                Diagnostic::error().with_message("Inexhaustive match expression"),
            );
        }

        expr
    }
}

/// The right hand side of a match case
#[derive(Debug)]
pub enum Body<'core> {
    Success {
        /// The expression to be evaluated
        expr: Expr<'core>,
    },

    #[cfg(false)]
    GuardIf {
        /// The variables to be let-bound before `guard_expr` and `expr` are
        /// evaluated
        let_vars: &'core [LetBinding<'core, Expr<'core>>],

        /// The condition, `expr` is only evaluated if `guard_expr` evaluates to
        /// `true`
        guard_expr: Expr<'core>,

        /// The expression to be evaluated
        expr: Expr<'core>,
    },
}
