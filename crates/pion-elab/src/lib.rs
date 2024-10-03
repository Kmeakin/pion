#![feature(allocator_api)]

use codespan_reporting::diagnostic::{Diagnostic, Label};
use env::ElabEnv;
use pion_core::semantics::{Closure, UnfoldOpts, Value};
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
    command_output: Vec<String>,
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
            command_output: Vec::new(),
        }
    }

    pub fn diagnostic(&mut self, range: TextRange, diagnostic: Diagnostic<usize>) {
        self.diagnostics
            .push(diagnostic.with_labels(vec![Label::primary(self.file_id, range)]));
    }

    pub fn finish(self) -> (Vec<Diagnostic<usize>>, Vec<String>) {
        (self.diagnostics, self.command_output)
    }

    fn eval_expr(&mut self, expr: &Expr<'core>) -> Value<'core> {
        pion_core::semantics::eval::eval(
            expr,
            UnfoldOpts::for_eval(),
            &mut self.env.locals.values,
            &self.env.metas.values,
        )
    }

    fn quote_value(&self, value: &Value<'core>) -> Expr<'core> {
        pion_core::semantics::quote::quote(
            value,
            self.bump,
            self.env.locals.len(),
            &self.env.metas.values,
        )
    }

    fn apply_closure(&self, closure: Closure<'core>, arg: Value<'core>) -> Value<'core> {
        pion_core::semantics::elim::beta_reduce(
            closure,
            arg,
            UnfoldOpts::for_eval(),
            &self.env.metas.values,
        )
    }

    fn convertible(&self, lhs: &Value<'core>, rhs: &Value<'core>) -> bool {
        pion_core::semantics::convertible::convertible(
            lhs,
            rhs,
            self.env.locals.len(),
            &self.env.metas.values,
        )
    }
}
