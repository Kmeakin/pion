#![feature(allocator_api)]

use codespan_reporting::diagnostic::{Diagnostic, Label};
use env::ElabEnv;
use pion_core::semantics::{
    Closure, ConvertibleEnv, ElimEnv, EvalEnv, QuoteEnv, UnfoldOpts, Value,
};
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
        EvalEnv::new(
            UnfoldOpts::for_eval(),
            &mut self.env.locals.values,
            &self.env.metas.values,
        )
        .eval(expr)
    }

    fn quote_value(&self, value: &Value<'core>) -> Expr<'core> {
        QuoteEnv::new(self.env.locals.len(), &self.env.metas.values).quote(value, self.bump)
    }

    fn apply_closure(&self, closure: Closure<'core>, arg: Value<'core>) -> Value<'core> {
        ElimEnv::new(UnfoldOpts::for_eval(), &self.env.metas.values).beta_reduce(closure, arg)
    }

    fn convertible(&self, lhs: &Value<'core>, rhs: &Value<'core>) -> bool {
        ConvertibleEnv::new(self.env.locals.len(), &self.env.metas.values).convertible(lhs, rhs)
    }
}
