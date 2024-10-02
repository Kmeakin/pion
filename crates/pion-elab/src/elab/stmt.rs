use std::fmt::Write;

use pion_core::print::Prec;
use pion_core::syntax::*;
use pion_surface::syntax as surface;

use super::Synth;
use crate::Elaborator;

impl<'text, 'surface, 'core> Elaborator<'core> {
    /// Synthesize statements.
    /// NOTE: may push onto local environment.
    /// Don't forget to reset in the caller!
    pub fn stmts(
        &mut self,
        stmts: &'surface [surface::Stmt<'text, 'surface>],
    ) -> &'core [Stmt<'core>] {
        let mut collected = Vec::with_capacity_in(stmts.len(), self.bump);
        for stmt in stmts {
            if let Some(stmt) = self.stmt(stmt) {
                collected.push(stmt);
            }
        }
        collected.leak()
    }

    /// Synthesize statement.
    /// NOTE: may push onto local environment.
    /// Don't forget to reset in the caller!
    fn stmt(&mut self, stmt: &'surface surface::Stmt<'text, 'surface>) -> Option<Stmt<'core>> {
        match stmt {
            surface::Stmt::Expr(expr) => {
                // TODO: should we store the inferred type somewhere?
                let (expr, _type) = self.synth_expr(*expr);
                Some(Stmt::Expr(expr))
            }
            surface::Stmt::Let(binding) => {
                let (binding, r#type) = self.let_binding(binding.as_ref());
                let value = self.eval_expr(&binding.init);
                self.env.locals.push_let(binding.name, r#type, value);
                Some(Stmt::Let(binding))
            }
            surface::Stmt::Command(command) => {
                self.command(command);
                None
            }
        }
    }

    fn let_binding(
        &mut self,
        binding: surface::Located<&surface::LetBinding<'text, 'surface>>,
    ) -> Synth<'core, LetBinding<'core, Expr<'core>>> {
        let surface::LetBinding { pat, init } = binding.data;
        let (pat, r#type_value) = self.synth_pat(pat.as_ref());
        let init = self.check_expr(init.as_ref(), &r#type_value);
        let r#type = self.quote_value(&r#type_value);
        let binding = LetBinding::new(pat.name(), r#type, init);
        (binding, r#type_value)
    }

    fn command(&mut self, command: &surface::Command<'text, 'surface>) {
        match command {
            surface::Command::Check(expr) => {
                let (expr, r#type) = self.synth_expr(*expr);
                pion_core::print::type_ann_expr(&mut self.command_output, &expr, &r#type).unwrap();
            }
            surface::Command::Eval(expr) => {
                let (expr, _type) = self.synth_expr(*expr);
                let value = self.eval_expr(&expr);
                pion_core::print::expr_prec(&mut self.command_output, &expr, Prec::MAX).unwrap();
                write!(self.command_output, " ⇝ ").unwrap();
                pion_core::print::value_prec(&mut self.command_output, &value, Prec::MAX).unwrap();
            }
        }
    }
}
