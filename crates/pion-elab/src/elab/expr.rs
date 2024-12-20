use std::borrow::Cow;
use std::str::FromStr;

use codespan_reporting::diagnostic::{Diagnostic, Label};
use pion_core::env::{DeBruijnIndex, EnvLen};
use pion_core::prim::PrimVar;
use pion_core::semantics::{Closure, Telescope, Type, Value};
use pion_core::syntax::{Expr, FunArg, FunParam, LocalVar, Plicity};
use pion_surface::syntax::{self as surface, Located};
use text_size::TextRange;

use super::pat::Pat;
use super::{Check, Synth};
use crate::env::MetaSource;
use crate::Elaborator;

pub type SynthExpr<'core> = Synth<'core, Expr<'core>>;
pub type CheckExpr<'core> = Check<Expr<'core>>;

impl<'text, 'surface, 'core> Elaborator<'core> {
    pub fn synth_expr(
        &mut self,
        expr: Located<&surface::Expr<'text, 'surface>>,
    ) -> SynthExpr<'core> {
        match expr.data {
            surface::Expr::Error => (Expr::Error, Type::ERROR),
            surface::Expr::Hole => {
                let r#type = self.push_unsolved_type(MetaSource::HoleType(expr.range));
                let expr =
                    self.push_unsolved_expr(MetaSource::HoleExpr(expr.range), r#type.clone());
                (expr, r#type)
            }
            surface::Expr::Var(name) => {
                let name = self.intern(name);
                if let Some((var, r#type, _)) = self.env.locals.lookup(name) {
                    return (Expr::LocalVar(var), r#type.clone());
                }

                if let Ok(var) = PrimVar::from_str(name.as_ref()) {
                    return (Expr::PrimVar(var), var.r#type());
                }

                self.diagnostic(
                    expr.range,
                    Diagnostic::error().with_message(format!("Unbound variable: `{name}`")),
                );

                (Expr::Error, Type::ERROR)
            }
            surface::Expr::Lit(lit) => {
                let lit = Located::new(expr.range, *lit);
                let (lit, r#type) = self.synth_lit(lit);
                let expr = match lit {
                    Ok(lit) => Expr::Lit(lit),
                    Err(()) => Expr::Error,
                };
                (expr, r#type)
            }
            surface::Expr::Paren(expr) => self.synth_expr(*expr),
            surface::Expr::TypeAnnotation(expr, r#type) => {
                let r#type = self.check_expr(*r#type, &Type::TYPE);
                let r#type_value = self.eval_env().eval(&r#type);
                let expr = self.check_expr(*expr, &r#type_value);
                (expr, r#type_value)
            }
            surface::Expr::FunCall(callee, args) => self.synth_fun_call(*callee, args),
            surface::Expr::FunExpr(params, body) => self.synth_fun_expr(params, *body),
            surface::Expr::FunType(params, body) => self.synth_fun_type(params, *body),
            surface::Expr::FunArrow(domain, codomain) => {
                let domain = self.check_expr(*domain, &Type::TYPE);
                let codomain = {
                    let domain_value = self.eval_env().eval(&domain);
                    self.env.locals.push_param(None, domain_value);
                    let codomain = self.check_expr(*codomain, &Type::TYPE);
                    self.env.locals.pop();
                    codomain
                };
                let (domain, codomain) = self.bump.alloc((domain, codomain));
                let expr = Expr::FunType(FunParam::explicit(None, domain), codomain);
                (expr, Type::TYPE)
            }
            surface::Expr::Do(stmts, expr) => {
                let len = self.env.locals.len();
                let stmts = self.stmts(stmts);
                let expr = expr.map(|expr| self.synth_expr(expr));
                self.env.locals.truncate(len);

                match expr {
                    Some((trailing_expr, r#type)) => (
                        Expr::Do(stmts, Some(self.bump.alloc(trailing_expr))),
                        r#type,
                    ),
                    None => (Expr::Do(stmts, None), Type::UNIT_TYPE),
                }
            }
            surface::Expr::If(cond, then, r#else) => {
                let cond = self.check_expr(*cond, &Type::BOOL);
                let (then, r#type) = self.synth_expr(*then);
                let r#else = self.check_expr(*r#else, &r#type);
                let (cond, then, r#else) = self.bump.alloc((cond, then, r#else));
                let expr = Expr::MatchBool(cond, then, r#else);
                (expr, r#type)
            }
            surface::Expr::Match(scrut, cases) => {
                let r#type = self.push_unsolved_type(MetaSource::MatchType(expr.range));
                let expr = self.check_match_expr(*scrut, cases, &r#type);
                (expr, r#type)
            }
            surface::Expr::RecordType(fields) => {
                let mut type_fields = Vec::new_in(self.bump);
                let local_len = self.env.locals.len();

                for field in *fields {
                    let label = field.label;
                    let symbol = self.intern(label.data);

                    if let Some(index) = type_fields.iter().position(|(n, _)| *n == symbol) {
                        let diagnostic = Diagnostic::error()
                            .with_message(format!("Duplicate record field `{symbol}`"))
                            .with_labels(vec![
                                Label::primary(self.file_id, label.range),
                                Label::secondary(self.file_id, fields[index].label.range)
                                    .with_message(format!(
                                        "Help: `{symbol}` is already defined here"
                                    )),
                            ]);
                        self.diagnostics.push(diagnostic);
                        continue;
                    }

                    let r#type = self.check_expr(field.expr.as_ref(), &Type::TYPE);
                    let r#type_value = self.eval_env().eval(&r#type);
                    type_fields.push((symbol, r#type));
                    self.env.locals.push_param(Some(symbol), r#type_value);
                }
                self.env.locals.truncate(local_len);

                (Expr::RecordType(type_fields.leak()), Type::TYPE)
            }
            surface::Expr::RecordLit(fields) => {
                let mut expr_fields = Vec::new_in(self.bump);
                let mut type_fields = Vec::new_in(self.bump);

                for surface_field in *fields {
                    let label = surface_field.label;
                    let symbol = self.intern(label.data);

                    if let Some(index) = expr_fields.iter().position(|(n, _)| *n == symbol) {
                        let diagnostic = Diagnostic::error()
                            .with_message(format!("Duplicate record field `{symbol}`"))
                            .with_labels(vec![
                                Label::primary(self.file_id, label.range),
                                Label::secondary(self.file_id, fields[index].label.range)
                                    .with_message(format!(
                                        "Help: `{symbol}` is already defined here"
                                    )),
                            ]);
                        self.diagnostics.push(diagnostic);
                        continue;
                    }

                    let (expr, r#type) = self.synth_expr(surface_field.expr.as_ref());
                    let r#type = self
                        .quote_env()
                        .quote_offset(&r#type, EnvLen::from(expr_fields.len()));
                    expr_fields.push((symbol, expr));
                    type_fields.push((symbol, r#type));
                }

                let telescope = Telescope::new(self.env.locals.values.clone(), type_fields.leak());
                (
                    Expr::RecordLit(expr_fields.leak()),
                    Type::RecordType(telescope),
                )
            }
            surface::Expr::Unit => (Expr::RecordLit(&[]), Type::RecordType(Telescope::empty())),
            surface::Expr::RecordProj(scrut, label) => {
                let (scrut_expr, scrut_type) = self.synth_expr(*scrut);
                let scrut_type = self.elim_env().subst_metas(&scrut_type);

                let proj_label = self.intern(label.data);

                match scrut_type {
                    Value::RecordType(mut telescope) => {
                        let Some(_pos) =
                            (telescope.fields.iter()).find(|(label, _)| *label == proj_label)
                        else {
                            self.diagnostic(
                                scrut.range,
                                Diagnostic::error()
                                    .with_message(format!("Field `{proj_label}` not found")),
                            );
                            return (Expr::Error, Type::ERROR);
                        };

                        let scrut_value = self.eval_env().eval(&scrut_expr);
                        while let Some((label, r#type, update_telescope)) =
                            self.elim_env().split_telescope(&mut telescope)
                        {
                            if label == proj_label {
                                let expr = Expr::RecordProj(self.bump.alloc(scrut_expr), label);
                                return (expr, r#type);
                            }

                            let projected = self.elim_env().record_proj(scrut_value.clone(), label);
                            update_telescope(projected);
                        }

                        unreachable!()
                    }
                    _ => {
                        let found = self.pretty(&self.quote_env().quote(&scrut_type));
                        self.diagnostic(
                            scrut.range,
                            Diagnostic::error()
                                .with_message(format!("Expected record, found `{found}`")),
                        );
                        (Expr::Error, Type::ERROR)
                    }
                }
            }
        }
    }

    pub fn check_expr(
        &mut self,
        expr: Located<&surface::Expr<'text, 'surface>>,
        expected: &Type<'core>,
    ) -> CheckExpr<'core> {
        match expr.data {
            surface::Expr::Error
            | surface::Expr::Var(_)
            | surface::Expr::Hole
            | surface::Expr::Lit(_)
            | surface::Expr::TypeAnnotation(..)
            | surface::Expr::FunCall(..)
            | surface::Expr::FunType(..)
            | surface::Expr::FunArrow(..)
            | surface::Expr::RecordType(..)
            | surface::Expr::RecordProj(..) => self.synth_and_coerce_expr(expr, expected),
            surface::Expr::Paren(expr) => self.check_expr(*expr, expected),
            surface::Expr::FunExpr(params, body) => self.check_fun_expr(params, *body, expected),
            surface::Expr::Do(stmts, Some(trailing_expr)) => {
                let len = self.env.locals.len();
                let stmts = self.stmts(stmts);
                let trailing_expr = self.check_expr(*trailing_expr, expected);
                self.env.locals.truncate(len);
                Expr::Do(stmts, Some(&*self.bump.alloc(trailing_expr)))
            }
            surface::Expr::Do(stmts, None) => {
                let len = self.env.locals.len();
                let stmts = self.stmts(stmts);
                self.env.locals.truncate(len);
                let result_expr = Expr::Do(stmts, None);
                self.coerce_expr(
                    Located::new(expr.range, result_expr),
                    &Type::UNIT_TYPE,
                    expected,
                )
            }
            surface::Expr::If(cond, then, r#else) => {
                let cond = self.check_expr(*cond, &Type::BOOL);
                let then = self.check_expr(*then, expected);
                let r#else = self.check_expr(*r#else, expected);
                let (cond, then, r#else) = self.bump.alloc((cond, then, r#else));
                Expr::MatchBool(cond, then, r#else)
            }
            surface::Expr::Match(scrut, cases) => self.check_match_expr(*scrut, cases, expected),
            surface::Expr::RecordLit(fields) => {
                let Type::RecordType(telescope) = expected else {
                    return self.synth_and_coerce_expr(expr, expected);
                };

                if fields.len() != telescope.fields.len() {
                    return self.synth_and_coerce_expr(expr, expected);
                }

                // FIXME: better error message if fields don't match
                if (fields.iter())
                    .map(|field| self.intern(field.label.data))
                    .ne(telescope.fields.iter().map(|(label, _)| *label))
                {
                    return self.synth_and_coerce_expr(expr, expected);
                }

                let mut telescope = telescope.clone();
                let mut expr_fields = Vec::new_in(self.bump);
                for surface_field in *fields {
                    let (name, r#type, update_telescope) =
                        self.elim_env().split_telescope(&mut telescope).unwrap();
                    let expr = self.check_expr(surface_field.expr.as_ref(), &r#type);
                    let value = self.eval_env().eval(&expr);
                    update_telescope(value);
                    expr_fields.push((name, expr));
                }
                Expr::RecordLit(expr_fields.leak())
            }
            surface::Expr::Unit => match expected {
                _ if expected.is_type() => Expr::RecordType(&[]),
                _ => self.synth_and_coerce_expr(expr, expected),
            },
        }
    }

    pub fn synth_and_coerce_expr(
        &mut self,
        expr: Located<&surface::Expr<'text, 'surface>>,
        expected: &Type<'core>,
    ) -> CheckExpr<'core> {
        let expr_range = expr.range;
        let (expr, r#type) = self.synth_expr(expr);
        self.coerce_expr(Located::new(expr_range, expr), &r#type, expected)
    }

    fn coerce_expr(
        &mut self,
        expr: Located<Expr<'core>>,
        from: &Type<'core>,
        to: &Type<'core>,
    ) -> CheckExpr<'core> {
        // Attempt to specialize exprs with freshly inserted implicit
        // arguments if an explicit function was expected.
        let (expr, from) = match (expr.data, to) {
            (Expr::FunLit(..), _) => (expr, Cow::Borrowed(from)),
            (_, Type::FunType(param, ..)) if param.plicity == Plicity::Explicit => {
                let (specialized, from) =
                    self.insert_implicit_apps(expr.range, expr.data, from.clone());
                let expr = Located::new(expr.range, specialized);
                (expr, Cow::Owned(from))
            }
            _ => (expr, Cow::Borrowed(from)),
        };

        match self.unify_env().unify(&from, to) {
            Ok(()) => expr.data,
            Err(err) => {
                // Unification may have unblocked some metas
                let from = self.elim_env().subst_metas(&from);
                let to = self.elim_env().subst_metas(to);

                let from = self.quote_env().quote(&from);
                let to = self.quote_env().quote(&to);

                let from = self.pretty(&from);
                let to = self.pretty(&to);

                self.diagnostic(expr.range, err.to_diagnostic(&from, &to));
                Expr::Error
            }
        }
    }

    fn synth_fun_param(
        &mut self,
        param: Located<&surface::FunParam<'text, 'surface>>,
    ) -> Synth<'core, (FunParam<'core, Expr<'core>>, Pat<'core>)> {
        let surface::FunParam { plicity, pat } = param.data;
        let (pat, r#type) = self.synth_pat(pat.as_ref());
        let param = FunParam::new(
            surface_plicity_to_core(*plicity),
            pat.name(),
            self.quote_env().quote(&r#type),
        );
        ((param, pat), r#type)
    }

    fn check_fun_param(
        &mut self,
        param: Located<&surface::FunParam<'text, 'surface>>,
        expected: &Type<'core>,
    ) -> Check<(FunParam<'core, Expr<'core>>, Pat<'core>)> {
        let surface::FunParam { plicity, pat } = param.data;
        let pat = self.check_pat(pat.as_ref(), expected);
        let param = FunParam::new(
            surface_plicity_to_core(*plicity),
            pat.name(),
            self.quote_env().quote(expected),
        );
        (param, pat)
    }

    fn synth_fun_type(
        &mut self,
        params: &[Located<surface::FunParam<'text, 'surface>>],
        body: Located<&surface::Expr<'text, 'surface>>,
    ) -> SynthExpr<'core> {
        fn recur<'text, 'surface, 'core>(
            this: &mut Elaborator<'core>,
            params: &[Located<surface::FunParam<'text, 'surface>>],
            body: Located<&surface::Expr<'text, 'surface>>,
        ) -> Expr<'core> {
            match params {
                [] => this.check_expr(body, &Type::TYPE),
                [param, params @ ..] => {
                    let ((param, pat), r#param_type) = this.synth_fun_param(param.as_ref());

                    let body_expr = {
                        let len = this.env.locals.len();
                        let var = Expr::LocalVar(LocalVar::new(DeBruijnIndex::new(0)));
                        let bindings = this.destruct_pat(&pat, &var, &param_type, true);

                        this.env.locals.push_param(param.name, param_type);
                        this.push_let_bindings(&bindings);
                        let body_expr = recur(this, params, body);
                        this.env.locals.truncate(len);
                        Expr::wrap_in_lets(this.bump, &bindings, body_expr)
                    };

                    let (param_type, body_expr) = this.bump.alloc((param.r#type, body_expr));
                    Expr::FunType(
                        FunParam::new(param.plicity, param.name, param_type),
                        body_expr,
                    )
                }
            }
        }

        let expr = recur(self, params, body);
        (expr, Type::TYPE)
    }

    fn synth_fun_expr(
        &mut self,
        params: &[Located<surface::FunParam<'text, 'surface>>],
        body: Located<&surface::Expr<'text, 'surface>>,
    ) -> SynthExpr<'core> {
        match params {
            [] => self.synth_expr(body),
            [param, params @ ..] => {
                let ((param, pat), r#param_type) = self.synth_fun_param(param.as_ref());
                let (body_expr, body_type) = {
                    let len = self.env.locals.len();
                    let var = Expr::LocalVar(LocalVar::new(DeBruijnIndex::new(0)));
                    let bindings = self.destruct_pat(&pat, &var, &param_type, true);
                    self.env.locals.push_param(param.name, param_type.clone());
                    self.push_let_bindings(&bindings);
                    let (body_expr, body_type) = self.synth_fun_expr(params, body);
                    let body_type = self.quote_env().quote(&body_type);
                    self.env.locals.truncate(len);
                    let body_expr = Expr::wrap_in_lets(self.bump, &bindings, body_expr);
                    let body_type = Expr::wrap_in_lets(self.bump, &bindings, body_type);
                    let (body_expr, body_type) = self.bump.alloc((body_expr, body_type));
                    (body_expr, body_type)
                };

                let (t1, t2) = self.bump.alloc((param.r#type, param_type));

                let expr = Expr::FunLit(FunParam::new(param.plicity, param.name, t1), body_expr);
                let r#type = Type::FunType(
                    FunParam::new(param.plicity, param.name, t2),
                    Closure::new(self.env.locals.values.clone(), body_type),
                );
                (expr, r#type)
            }
        }
    }

    fn check_fun_expr(
        &mut self,
        params: &[Located<surface::FunParam<'text, 'surface>>],
        body: Located<&surface::Expr<'text, 'surface>>,
        expected: &Type<'core>,
    ) -> CheckExpr<'core> {
        let [param, rest @ ..] = params else {
            return self.check_expr(body, expected);
        };

        let Value::FunType(expected_param, expected_body) = expected else {
            // FIXME: this span is misleading
            let (expr, r#type) = self.synth_fun_expr(params, body);
            return self.coerce_expr(Located::new(body.range, expr), &r#type, expected);
        };

        match (param.data.plicity, expected_param.plicity) {
            (surface::Plicity::Implicit, Plicity::Explicit) => {
                // FIXME: this span is misleading
                let (expr, r#type) = self.synth_fun_expr(params, body);
                self.coerce_expr(Located::new(body.range, expr), &r#type, expected)
            }

            // If an implicit function is expected, try to generalize the
            // function literal by wrapping it in an implicit function
            (surface::Plicity::Explicit, Plicity::Implicit) => {
                let r#type = self.quote_env().quote(expected_param.r#type);
                let arg_value =
                    Value::local_var(LocalVar::new(self.env.locals.values.len().to_level()));
                (self.env.locals).push_param(expected_param.name, expected_param.r#type.clone());
                let expected = (self.elim_env()).apply_closure(expected_body.clone(), arg_value);
                let body = self.check_fun_expr(params, body, &expected);
                self.env.locals.pop();
                let (r#type, body) = self.bump.alloc((r#type, body));
                let param = FunParam::new(expected_param.plicity, expected_param.name, &*r#type);
                Expr::FunLit(param, body)
            }

            (surface::Plicity::Explicit, Plicity::Explicit)
            | (surface::Plicity::Implicit, Plicity::Implicit) => {
                let (param, pat) = self.check_fun_param(param.as_ref(), expected_param.r#type);
                let body_expr = {
                    let len = self.env.locals.len();
                    let var = Expr::LocalVar(LocalVar::new(DeBruijnIndex::new(0)));
                    let bindings = self.destruct_pat(&pat, &var, expected_param.r#type, true);

                    let arg_value =
                        Value::local_var(LocalVar::new(self.env.locals.values.len().to_level()));
                    (self.env.locals).push_param(param.name, expected_param.r#type.clone());
                    self.push_let_bindings(&bindings);
                    let expected =
                        (self.elim_env()).apply_closure(expected_body.clone(), arg_value);
                    let body_expr = self.check_fun_expr(rest, body, &expected);
                    self.env.locals.truncate(len);
                    Expr::wrap_in_lets(self.bump, &bindings, body_expr)
                };
                let (param_type, body_expr) = self.bump.alloc((param.r#type, body_expr));
                Expr::FunLit(
                    FunParam::new(param.plicity, param.name, param_type),
                    body_expr,
                )
            }
        }
    }

    fn synth_fun_call(
        &mut self,
        callee: Located<&surface::Expr<'text, 'surface>>,
        args: &[Located<surface::FunArg<'text, 'surface>>],
    ) -> (Expr<'core>, Value<'core>) {
        let (callee_expr, callee_type) = self.synth_expr(callee);
        let callee_range = callee.range;
        let mut result_expr = callee_expr;
        let mut result_type = callee_type.clone();

        for (arity, arg) in args.iter().enumerate() {
            let arg_plicity = surface_plicity_to_core(arg.data.plicity);

            if arg_plicity == Plicity::Explicit {
                (result_expr, result_type) =
                    self.insert_implicit_apps(callee_range, result_expr, result_type);
            }

            match result_type {
                Value::FunType(param, body) if arg_plicity == param.plicity => {
                    let param_type = param.r#type;
                    let arg_expr = self.check_expr(arg.data.expr.as_ref(), param_type);
                    let arg_value = self.eval_env().eval(&arg_expr);
                    let (expr, arg_expr) = self.bump.alloc((result_expr, arg_expr));
                    result_expr = Expr::FunApp(&*expr, FunArg::new(param.plicity, &*arg_expr));
                    result_type = self.elim_env().apply_closure(body, arg_value);
                }
                Value::FunType(param, _) => {
                    let callee_type = self.pretty(&self.quote_env().quote(&callee_type));
                    self.diagnostic(
                        arg.range,
                        Diagnostic::error()
                            .with_message(format!(
                                "Applied {} argument when {} argument was expected",
                                arg_plicity.description(),
                                param.plicity.description()
                            ))
                            .with_notes(vec![format!(
                                "Help: the type of the callee is `{}`",
                                callee_type
                            )]),
                    );
                    return (Expr::Error, Type::ERROR);
                }
                _ => {
                    let diagnostic = match arity {
                        0 => Diagnostic::error().with_message("Expected a function"),
                        _ => Diagnostic::error()
                            .with_message("Called function with too many arguments"),
                    };
                    let mut notes = vec![format!(
                        "Help: the type of the callee is `{}`",
                        self.pretty(&self.quote_env().quote(&callee_type))
                    )];
                    if arity > 0 {
                        notes.push(format!(
                            "Help: the function expects {arity} arguments, but received {}",
                            args.len()
                        ));
                    }
                    let diagnostic = diagnostic.with_notes(notes);
                    self.diagnostic(callee.range, diagnostic);
                    return (Expr::Error, Type::ERROR);
                }
            }
        }

        (result_expr, result_type)
    }

    /// Wrap an expr in fresh implicit applications that correspond to implicit
    /// parameters in the type provided.
    fn insert_implicit_apps(
        &mut self,
        range: TextRange,
        mut expr: Expr<'core>,
        mut r#type: Type<'core>,
    ) -> (Expr<'core>, Type<'core>) {
        loop {
            r#type = self.elim_env().subst_metas(&r#type);
            match r#type {
                Value::FunType { 0: param, 1: body } if param.plicity == Plicity::Implicit => {
                    let source = MetaSource::ImplicitArg(range, param.name);
                    let arg_expr = self.push_unsolved_expr(source, param.r#type.clone());
                    let arg_value = self.eval_env().eval(&arg_expr);

                    let (fun, arg_expr) = self.bump.alloc((expr, arg_expr));

                    let arg = FunArg::new(param.plicity, &*arg_expr);
                    expr = Expr::FunApp(fun, arg);
                    r#type = self.elim_env().apply_closure(body, arg_value);
                }
                _ => break,
            }
        }
        (expr, r#type)
    }
}

fn surface_plicity_to_core(surface_plicity: surface::Plicity) -> Plicity {
    match surface_plicity {
        surface::Plicity::Explicit => Plicity::Explicit,
        surface::Plicity::Implicit => Plicity::Implicit,
    }
}
