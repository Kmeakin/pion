use codespan_reporting::diagnostic::{Diagnostic, Label};
use env::ElabEnv;
use pion_core::semantics::{Closure, EvalOpts, Value};
use pion_core::syntax::Expr;
use text_size::TextRange;

pub mod env;

mod elab;

pub struct Elaborator<'core> {
    bump: &'core bumpalo::Bump,
    interner: &'core mut pion_interner::Interner<'core, str>,
    env: ElabEnv<'core>,

    file_id: usize,
    diagnostics: Vec<Diagnostic<usize>>,
}

impl<'core> Elaborator<'core> {
    pub fn new(
        bump: &'core bumpalo::Bump,
        interner: &'core mut pion_interner::Interner<'core, str>,
        file_id: usize,
    ) -> Self {
        Self {
            bump,
            interner,
            env: ElabEnv::default(),

            file_id,
            diagnostics: Vec::new(),
        }
    }

    pub fn diagnostic(&mut self, range: TextRange, diagnostic: Diagnostic<usize>) {
        self.diagnostics
            .push(diagnostic.with_labels(vec![Label::primary(self.file_id, range)]));
    }

    pub fn finish(self) -> Vec<Diagnostic<usize>> { self.diagnostics }

    fn eval_expr(&mut self, expr: &Expr<'core>) -> Value<'core> {
        pion_core::semantics::eval(
            expr,
            EvalOpts::for_eval(),
            &mut self.env.locals.values,
            &self.env.metas.values,
        )
        .unwrap()
    }

    fn quote_value(&self, value: &Value<'core>) -> Expr<'core> {
        pion_core::semantics::quote(
            value,
            self.bump,
            self.env.locals.len(),
            &self.env.metas.values,
        )
        .unwrap()
    }

    fn apply_closure(&self, closure: Closure<'core>, arg: Value<'core>) -> Value<'core> {
        pion_core::semantics::apply_closure(
            closure,
            arg,
            EvalOpts::for_eval(),
            &self.env.metas.values,
        )
        .unwrap()
    }

    fn convertible(&self, lhs: &Value<'core>, rhs: &Value<'core>) -> bool {
        pion_core::semantics::convertible(lhs, rhs, self.env.locals.len(), &self.env.metas.values)
    }
}
