use pion_core::print::{Prec, Printer};
use pion_core::syntax::*;
use pion_surface::syntax as surface;

use crate::env::LocalInfo;
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
            match stmt {
                surface::Stmt::Command(command) => self.command(command),
                surface::Stmt::Expr(expr) => {
                    // TODO: should we store the inferred type somewhere?
                    let (expr, _type) = self.synth_expr(*expr);
                    collected.push(Stmt::Expr(expr));
                }
                surface::Stmt::Let(binding) => {
                    let (pat, type_value) = self.synth_pat(binding.data.pat.as_ref());
                    let init = self.check_expr(binding.data.init.as_ref(), &type_value);
                    let bindings = self.destruct_pat(&pat, &init, &r#type_value, false);
                    self.push_let_bindings(&bindings);
                    collected.extend(bindings.into_iter().map(Stmt::Let));
                }
            }
        }
        collected.leak()
    }

    fn command(&mut self, command: &surface::Command<'text, 'surface>) {
        match command {
            surface::Command::Check(expr) => {
                let (expr, r#type) = self.synth_expr(*expr);
                let r#type = self.quote_env().quote(&r#type);
                let printer = Printer::new(self.bump);
                let doc = printer.type_ann_expr(&expr, &r#type).into_doc();
                let out = doc.pretty(80).to_string();
                self.command_output.push(out);
            }
            surface::Command::Eval(expr) => {
                let (expr, _type) = self.synth_expr(*expr);
                let value = self.eval_env().eval(&expr);
                let value = self.quote_env().quote(&value);

                let printer = Printer::new(self.bump);
                let doc = printer
                    .expr_prec(&expr, Prec::MAX)
                    .append(" ⇝ ")
                    .append(printer.expr_prec(&value, Prec::MAX))
                    .into_doc();
                let out = doc.pretty(80).to_string();
                self.command_output.push(out);
            }
            surface::Command::Show(expr) => {
                let (expr, r#type) = self.synth_expr(*expr);
                let r#type = self.quote_env().quote(&r#type);
                match expr {
                    Expr::LocalVar(var) => {
                        match self.env.locals.infos.get(var.de_bruijn).unwrap() {
                            LocalInfo::Param => {
                                self.command_output.push(format!(
                                    "parameter {} : {}",
                                    var.name.unwrap(),
                                    r#type
                                ));
                            }
                            LocalInfo::Let(init) => {
                                let printer = Printer::new(self.bump);
                                let init = init.shift(self.bump, self.env.locals.len());
                                let binding = LetBinding::new(var.name, r#type, init);
                                let doc = printer.let_stmt(&binding).into_doc();
                                let out = doc.pretty(80).to_string();
                                self.command_output.push(out);
                            }
                        }
                    }
                    _ => {
                        let printer = Printer::new(self.bump);
                        let doc = printer.type_ann_expr(&expr, &r#type).into_doc();
                        let out = doc.pretty(80).to_string();
                        self.command_output.push(out);
                    }
                }
            }
        }
    }
}
