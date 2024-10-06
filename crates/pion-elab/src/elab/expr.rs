use std::borrow::Cow;
use std::str::FromStr;

use codespan_reporting::diagnostic::Diagnostic;
use pion_core::prim::PrimVar;
use pion_core::semantics::{Closure, Type, Value};
use pion_core::syntax::{Expr, FunArg, FunParam, LocalVar, Plicity};
use pion_surface::syntax::{self as surface, Located};
use text_size::{TextRange, TextSize};

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
                let name = self.bump.alloc_str(name);
                let name = self.interner.intern(name);

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
            surface::Expr::Lit(lit) => match lit {
                surface::Lit::Bool(b) => (Expr::bool(*b), Type::BOOL),
                surface::Lit::Int(text) => {
                    (self.synth_int(Located::new(expr.range, text)), Type::INT)
                }
                surface::Lit::Char(text) => {
                    (self.synth_char(Located::new(expr.range, text)), Type::CHAR)
                }
                surface::Lit::String(text) => (
                    self.synth_string(Located::new(expr.range, text)),
                    Type::STRING,
                ),
            },
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
            | surface::Expr::FunArrow(..) => self.synth_and_coerce_expr(expr, expected),
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
        match self.unify_env().unify(from, to) {
            Ok(()) => expr.data,
            Err(err) => {
                self.diagnostic(expr.range, err.to_diagnostic(from, to));
                Expr::Error
            }
        }
    }

    fn synth_fun_param(
        &mut self,
        param: Located<&surface::FunParam<'text, 'surface>>,
    ) -> Synth<'core, FunParam<'core, Expr<'core>>> {
        let surface::FunParam { pat } = param.data;
        let (pat, r#type) = self.synth_pat(pat.as_ref());
        let param = FunParam::new(
            Plicity::Explicit,
            pat.name(),
            self.quote_env().quote(&r#type, self.bump),
        );
        (param, r#type)
    }

    fn check_fun_param(
        &mut self,
        param: Located<&surface::FunParam<'text, 'surface>>,
        expected: &Type<'core>,
    ) -> Check<FunParam<'core, Expr<'core>>> {
        let surface::FunParam { pat } = param.data;
        let pat = self.check_pat(pat.as_ref(), expected);
        FunParam::new(
            Plicity::Explicit,
            pat.name(),
            self.quote_env().quote(expected, self.bump),
        )
    }

    fn synth_fun_type(
        &mut self,
        params: &[Located<surface::FunParam<'text, 'surface>>],
        body: Located<&surface::Expr<'text, 'surface>>,
    ) -> SynthExpr<'core> {
        match params {
            [] => {
                let body = self.check_expr(body, &Type::TYPE);
                (body, Type::TYPE)
            }
            [param, params @ ..] => {
                let (param, r#param_type) = self.synth_fun_param(param.as_ref());

                let body_expr = {
                    self.env.locals.push_param(param.name, param_type);
                    let (body_expr, _) = self.synth_fun_type(params, body);
                    self.env.locals.pop();
                    body_expr
                };

                let expr = Expr::FunType(
                    FunParam::new(param.plicity, param.name, self.bump.alloc(param.r#type)),
                    self.bump.alloc(body_expr),
                );
                (expr, Type::TYPE)
            }
        }
    }

    fn synth_fun_expr(
        &mut self,
        params: &[Located<surface::FunParam<'text, 'surface>>],
        body: Located<&surface::Expr<'text, 'surface>>,
    ) -> SynthExpr<'core> {
        match params {
            [] => self.synth_expr(body),
            [param, params @ ..] => {
                let (param, r#param_type) = self.synth_fun_param(param.as_ref());

                let (body_expr, body_type) = {
                    self.env.locals.push_param(param.name, param_type.clone());
                    let (body_expr, body_type) = self.synth_fun_expr(params, body);
                    let body_type = self.quote_env().quote(&body_type, self.bump);
                    self.env.locals.pop();
                    (body_expr, body_type)
                };

                let param =
                    FunParam::new(param.plicity, param.name, &*self.bump.alloc(param.r#type));
                let expr = Expr::FunLit(param, self.bump.alloc(body_expr));
                let r#type = Type::FunType(
                    param,
                    Closure::new(self.env.locals.values.clone(), self.bump.alloc(body_type)),
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
        let expected = self.elim_env().subst_metas(expected);
        match params {
            [] => self.check_expr(body, &expected),
            [param, rest @ ..] => match expected {
                Value::FunType(expected_param, expected_body) => {
                    let expected_param_type = self.eval_env().eval(expected_param.r#type);
                    let param = self.check_fun_param(param.as_ref(), &expected_param_type);
                    let body_expr = {
                        let arg_value = Value::local_var(LocalVar::new(
                            param.name,
                            self.env.locals.values.len().to_level(),
                        ));
                        self.env.locals.push_param(param.name, expected_param_type);
                        let expected = self
                            .elim_env()
                            .apply_closure(expected_body.clone(), arg_value);
                        let body_expr = self.check_fun_expr(rest, body, &expected);
                        self.env.locals.pop();
                        body_expr
                    };
                    let expr = Expr::FunLit(
                        FunParam::new(param.plicity, param.name, self.bump.alloc(param.r#type)),
                        self.bump.alloc(body_expr),
                    );
                    expr
                }
                _ => {
                    // FIXME: this span is misleading
                    let (expr, r#type) = self.synth_fun_expr(params, body);
                    self.coerce_expr(Located::new(body.range, expr), &r#type, &expected)
                }
            },
        }
    }

    fn synth_fun_call(
        &mut self,
        callee: Located<&surface::Expr<'text, 'surface>>,
        args: &[Located<surface::FunArg<'text, 'surface>>],
    ) -> (Expr<'core>, Value<'core>) {
        let (callee_expr, callee_type) = self.synth_expr(callee);
        let mut result_expr = callee_expr;
        let mut result_type = callee_type.clone();

        for (arity, arg) in args.iter().enumerate() {
            match result_type {
                Value::FunType(param, body) => {
                    let param_type = self.eval_env().eval(param.r#type);
                    let arg_expr = self.check_expr(arg.data.expr.as_ref(), &param_type);
                    let arg_value = self.eval_env().eval(&arg_expr);
                    let (expr, arg_expr) = self.bump.alloc((result_expr, arg_expr));
                    result_expr = Expr::FunApp(&*expr, FunArg::new(param.plicity, &*arg_expr));
                    result_type = self.elim_env().apply_closure(body, arg_value);
                }
                _ => {
                    let diagnostic = match arity {
                        0 => Diagnostic::error().with_message("Expected a function"),
                        _ => Diagnostic::error()
                            .with_message("Called function with too many arguments"),
                    };
                    let mut notes =
                        vec![format!("Help: the type of the callee is `{callee_type}`")];
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

    fn synth_int(&mut self, text: Located<&str>) -> Expr<'core> {
        let range = text.range;
        let text = match text.data.contains('_') {
            false => Cow::Borrowed(text.data),
            true => Cow::Owned(text.data.replace('_', "")),
        };

        let res = match () {
            () if text.starts_with("0b") || text.starts_with("0B") => {
                u32::from_str_radix(&text[2..], 16)
            }
            () if text.starts_with("0o") || text.starts_with("0O") => {
                u32::from_str_radix(&text[2..], 16)
            }
            () if text.starts_with("0x") || text.starts_with("0X") => {
                u32::from_str_radix(&text[2..], 16)
            }
            () => u32::from_str(&text),
        };

        match res {
            Ok(n) => Expr::int(n),
            Err(error) => {
                self.diagnostic(
                    range,
                    Diagnostic::error().with_message(format!("Invalid integer literal: {error}")),
                );
                Expr::Error
            }
        }
    }

    fn synth_string(&mut self, text: Located<&str>) -> Expr<'core> {
        let range = text.range;
        let text = text.data;

        let text = text.strip_prefix('"').expect("Guaranteed by lexer");

        let (text, mut terminated) = match text.strip_suffix('"') {
            Some(text) => (text, true),
            None => (text, false),
        };

        let mut error = false;
        let text = match text.contains('\\') {
            false => Cow::Borrowed(text),
            true => {
                let mut result = String::with_capacity(text.len());
                let mut chars = text.char_indices();

                while let Some((idx1, c)) = chars.next() {
                    match c {
                        '\\' => {
                            let Some((idx2, c)) = chars.next() else {
                                terminated = false;
                                break;
                            };
                            match c {
                                'n' => result.push('\n'),
                                'r' => result.push('\r'),
                                't' => result.push('\t'),
                                '\\' => result.push('\\'),
                                '"' => result.push('"'),
                                c => {
                                    error = true;
                                    let range = range + TextSize::from(1); // add 1 to skip past the leading '"'
                                    let idx1 = TextSize::try_from(idx1).unwrap();
                                    let idx2 = TextSize::try_from(idx2 + c.len_utf8()).unwrap();

                                    debug_assert_eq!(
                                        text[TextRange::new(idx1, idx2)],
                                        format!("\\{c}")
                                    );

                                    let range =
                                        TextRange::new(range.start() + idx1, range.start() + idx2);
                                    self.diagnostic(
                                        range,
                                        Diagnostic::error().with_message(format!(
                                            "Unknown escape character: `{c}`"
                                        )),
                                    );
                                }
                            }
                        }
                        c => result.push(c),
                    }
                }
                Cow::Owned(result)
            }
        };

        if !terminated {
            error = true;
            self.diagnostic(
                range,
                Diagnostic::error().with_message("Unterminated string literal"),
            );
        }

        if error {
            return Expr::Error;
        }

        Expr::string(self.bump.alloc_str(&text))
    }

    #[allow(
        unused_variables,
        clippy::unused_self,
        clippy::needless_pass_by_ref_mut,
        reason = "not implemented yet"
    )]
    fn synth_char(&mut self, text: Located<&str>) -> Expr<'core> {
        // TODO: Handle escape sequences, check string is terminated, check for invalid
        // characters
        Expr::char('\0')
    }
}
