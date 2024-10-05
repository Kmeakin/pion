#![feature(allocator_api)]

use codespan_reporting::diagnostic::{Diagnostic, Label};
use env::{ElabEnv, LocalInfo, MetaSource};
use pion_core::env::AbsoluteVar;
use pion_core::semantics::{
    Closure, ConvertibleEnv, ElimEnv, EvalEnv, QuoteEnv, Type, UnfoldOpts, Value,
};
use pion_core::syntax::{Expr, FunArg, Plicity};
use text_size::TextRange;
use unify::{UnifyEnv, UnifyError};

pub mod env;

mod elab;
mod unify;

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

    fn unify(&mut self, lhs: &Value<'core>, rhs: &Value<'core>) -> Result<(), UnifyError> {
        UnifyEnv::new(
            self.bump,
            &mut self.env.renaming,
            self.env.locals.len(),
            &mut self.env.metas.values,
        )
        .unify(lhs, rhs)
    }

    fn push_unsolved_expr(
        &mut self,
        source: MetaSource<'core>,
        r#type: Type<'core>,
    ) -> Expr<'core> {
        let var = self.env.metas.len().to_absolute();
        self.env.metas.push(source, r#type);

        let mut expr = Expr::MetaVar(var);
        for (var, info) in AbsoluteVar::iter().zip(self.env.locals.infos.iter()) {
            match info {
                LocalInfo::Let => {}
                LocalInfo::Param => {
                    let var = self.env.locals.len().absolute_to_relative(var).unwrap();
                    let arg = Expr::LocalVar(var);
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
        self.eval_expr(&expr)
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
        ElimEnv::new(UnfoldOpts::for_eval(), &self.env.metas.values)
    }
}
