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
            let stmt = self.stmt(stmt);
            collected.push(stmt);
        }
        collected.leak()
    }

    /// Synthesize statement.
    /// NOTE: may push onto local environment.
    /// Don't forget to reset in the caller!
    fn stmt(&mut self, stmt: &'surface surface::Stmt<'text, 'surface>) -> Stmt<'core> {
        match stmt {
            surface::Stmt::Expr(expr) => {
                // TODO: should we store the inferred type somewhere?
                let (expr, _type) = self.synth_expr(*expr);
                Stmt::Expr(expr)
            }
            surface::Stmt::Let(binding) => {
                let (binding, r#type) = self.let_binding(binding.as_ref());
                let value = self.eval_expr(&binding.init);
                self.env.locals.push_let(binding.name, r#type, value);
                Stmt::Let(binding)
            }
            surface::Stmt::Command(_) => todo!(),
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
}
