#![feature(allocator_api)]

use codespan_reporting::diagnostic::{Diagnostic, Label};
use env::{ElabEnv, LocalInfo, MetaSource};
use pion_core::env::{DeBruijn, DeBruijnLevel};
use pion_core::semantics::{ElimEnv, EvalEnv, QuoteEnv, Type, UnfoldOpts, Value};
use pion_core::syntax::{Expr, FunArg, LocalVar, MetaVar, Plicity};
use text_size::TextRange;
use unify::UnifyEnv;

pub mod env;

mod elab;
mod unify;

pub struct Elaborator<'core> {
    bump: &'core bumpalo::Bump,
    interner: &'core mut pion_core::symbol::Interner<'core>,
    env: ElabEnv<'core>,

    file_id: usize,
    diagnostics: Vec<Diagnostic<usize>>,
    command_output: Vec<String>,
}

impl<'core> Elaborator<'core> {
    pub fn new(
        bump: &'core bumpalo::Bump,
        interner: &'core mut pion_core::symbol::Interner<'core>,
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

    fn push_unsolved_expr(
        &mut self,
        source: MetaSource<'core>,
        r#type: Type<'core>,
    ) -> Expr<'core> {
        let var = self.env.metas.len().to_level();
        self.env.metas.push(source, r#type);

        let mut expr = Expr::MetaVar(MetaVar::new(var));
        for ((level, info), name) in DeBruijnLevel::iter()
            .zip(self.env.locals.infos.iter())
            .zip(self.env.locals.names.iter())
        {
            match info {
                LocalInfo::Let => {}
                LocalInfo::Param => {
                    let index = level.to_index(self.env.locals.len()).unwrap();
                    let arg = Expr::LocalVar(LocalVar::new(*name, index));
                    let (fun, arg) = self.bump.alloc((expr, arg));
                    let arg = FunArg::new(Plicity::Explicit, &*arg);
                    expr = Expr::FunApp(fun, arg);
                }
            }
        }
        expr
    }

    fn push_unsolved_type(&mut self, source: MetaSource<'core>) -> Value<'core> {
        let expr = self.push_unsolved_expr(source, Value::TYPE);
        self.eval_env().eval(&expr)
    }

    pub fn report_unsolved_metas(&mut self) {
        let meta_env = std::mem::take(&mut self.env.metas);
        for (source, _, value) in meta_env.iter() {
            if value.is_none() {
                let message = match source {
                    MetaSource::PatType(_, Some(name)) => format!("type of variable `{name}`"),
                    MetaSource::PatType(_, None) => String::from("type of wildcard pattern"),
                    MetaSource::HoleType(_) => String::from("type of hole"),
                    MetaSource::HoleExpr(_) => String::from("expression to solve hole"),
                    MetaSource::ImplicitArg(_, Some(name)) => format!("implicit argument `{name}`"),
                    MetaSource::ImplicitArg(_, None) => String::from("implicit argument"),
                };
                self.diagnostic(
                    source.range(),
                    Diagnostic::error().with_message(format!("Could not infer {message}")),
                );
            }
        }
        self.env.metas = meta_env;
    }

    fn elim_env(&self) -> ElimEnv<'_, 'core> {
        ElimEnv::new(self.bump, UnfoldOpts::for_eval(), &self.env.metas.values)
    }

    fn eval_env(&mut self) -> EvalEnv<'_, 'core> {
        EvalEnv::new(
            self.bump,
            UnfoldOpts::for_eval(),
            &mut self.env.locals.values,
            &self.env.metas.values,
        )
    }

    fn quote_env(&self) -> QuoteEnv<'_, 'core> {
        QuoteEnv::new(self.bump, self.env.locals.len(), &self.env.metas.values)
    }

    fn unify_env(&mut self) -> UnifyEnv<'_, 'core> {
        UnifyEnv::new(
            self.bump,
            &mut self.env.renaming,
            self.env.locals.len(),
            &mut self.env.metas.values,
        )
    }
}
