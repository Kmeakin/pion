use std::borrow::Cow;
use std::str::FromStr;

use codespan_reporting::diagnostic::{Diagnostic, Label};
use pion_core::prim::PrimVar;
use pion_core::semantics::equality::AlphaEq;
use pion_core::semantics::{Closure, Type, Value};
use pion_core::syntax::{Expr, FunArg, FunParam, LetBinding, Plicity};
use pion_surface::syntax::{self as surface, Located};

use super::{Check, Synth};
use crate::Elaborator;

pub type SynthExpr<'core> = Synth<'core, Expr<'core>>;
pub type CheckExpr<'core> = Check<Expr<'core>>;

impl<'text, 'surface, 'core> Elaborator<'core> {
    pub fn synth_expr(
        &mut self,
        expr: Located<&surface::Expr<'text, 'surface>>,
    ) -> SynthExpr<'core> {
        match expr.data {
            surface::Expr::Error => (Expr::Error, Type::Error),
            surface::Expr::Var(name) => {
                let name = self.bump.alloc_str(name);
                let name = self.interner.intern(name);

                if let Some(var) = self.env.locals.lookup(name) {
                    let r#type = self.env.locals.types.get_relative(var).unwrap();
                    return (Expr::LocalVar(var), r#type.clone());
                }

                if let Ok(var) = PrimVar::from_str(name.as_ref()) {
                    return (Expr::PrimVar(var), var.r#type());
                }

                self.diagnostic(
                    expr.range,
                    Diagnostic::error().with_message(format!("Unbound variable: `{name}`")),
                );

                (Expr::Error, Type::Error)
            }
            surface::Expr::Bool(b) => (Expr::Bool(*b), Type::BOOL),
            surface::Expr::Number(text) => {
                (self.synth_number(Located::new(expr.range, text)), Type::INT)
            }
            surface::Expr::Char(text) => {
                (self.synth_char(Located::new(expr.range, text)), Type::CHAR)
            }
            surface::Expr::String(text) => (
                self.synth_string(Located::new(expr.range, text)),
                Type::STRING,
            ),
            surface::Expr::Paren(expr) => self.synth_expr(*expr),
            surface::Expr::FunCall { callee, args } => self.synth_fun_call(*callee, args),
            surface::Expr::FunExpr { params, body } => self.synth_fun_expr(params, *body),
            surface::Expr::FunType { params, body } => self.synth_fun_type(params, *body),
            surface::Expr::FunArrow { domain, codomain } => {
                let domain = self.check_expr(*domain, &Type::TYPE);
                let codomain = {
                    let domain_value = self.eval_expr(&domain);
                    self.env.locals.push_param(None, domain_value);
                    let codomain = self.check_expr(*codomain, &Type::TYPE);
                    self.env.locals.pop();
                    codomain
                };
                let (domain, codomain) = self.bump.alloc((domain, codomain));
                let expr = Expr::FunType {
                    param: FunParam::explicit(None, domain),
                    body: codomain,
                };
                (expr, Type::TYPE)
            }
            surface::Expr::Let { binding, body } => {
                let (binding, r#type) = self.synth_let_binding(*binding);

                let (body_expr, body_type) = {
                    let value = self.eval_expr(&binding.rhs);
                    self.env.locals.push_let(binding.name, r#type, value);
                    let (body_expr, body_type) = self.synth_expr(*body);
                    self.env.locals.pop();
                    (body_expr, body_type)
                };

                let expr = Expr::Let {
                    binding: LetBinding {
                        name: binding.name,
                        r#type: self.bump.alloc(binding.r#type),
                        rhs: self.bump.alloc(binding.rhs),
                    },
                    body: self.bump.alloc(body_expr),
                };
                (expr, body_type)
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
            | surface::Expr::Bool(_)
            | surface::Expr::Number(_)
            | surface::Expr::Char(_)
            | surface::Expr::String(_)
            | surface::Expr::Paren(_)
            | surface::Expr::FunCall { .. }
            | surface::Expr::FunType { .. }
            | surface::Expr::FunArrow { .. } => self.synth_and_coerce_expr(expr, expected),
            surface::Expr::FunExpr { params, body } => self.check_fun_expr(params, *body, expected),
            surface::Expr::Let { binding, body } => {
                let (binding, r#type) = self.synth_let_binding(*binding);

                let body_expr = {
                    let value = self.eval_expr(&binding.rhs);
                    self.env.locals.push_let(binding.name, r#type, value);
                    let body_expr = self.check_expr(*body, expected);
                    self.env.locals.pop();
                    body_expr
                };

                let expr = Expr::Let {
                    binding: LetBinding {
                        name: binding.name,
                        r#type: self.bump.alloc(binding.r#type),
                        rhs: self.bump.alloc(binding.rhs),
                    },
                    body: self.bump.alloc(body_expr),
                };
                expr
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

    pub fn coerce_expr(
        &mut self,
        expr: Located<Expr<'core>>,
        from: &Type<'core>,
        to: &Type<'core>,
    ) -> CheckExpr<'core> {
        match from.alpha_eq(to) {
            true => expr.data,
            false => {
                self.diagnostic(
                    expr.range,
                    Diagnostic::error()
                        .with_message(format!("Type mismatch: expected `{to:?}`, found {from:?}")),
                );
                Expr::Error
            }
        }
    }

    fn synth_let_binding(
        &mut self,
        binding: Located<&surface::LetBinding<'text, 'surface>>,
    ) -> Synth<'core, LetBinding<'core, Expr<'core>>> {
        let surface::LetBinding {
            pat,
            r#type,
            expr: rhs,
        } = binding.data;
        let (pat, r#type) = self.synth_ann_pat(pat.as_ref(), r#type.as_ref().map(|ty| ty.as_ref()));
        let rhs = self.check_expr(rhs.as_ref(), &r#type);

        let binding = LetBinding {
            name: pat.name(),
            r#type: self.quote_value(&r#type),
            rhs,
        };
        (binding, r#type)
    }

    fn synth_fun_param(
        &mut self,
        param: Located<&surface::FunParam<'text, 'surface>>,
    ) -> Synth<'core, FunParam<'core, Expr<'core>>> {
        let surface::FunParam { pat, r#type } = param.data;
        let (pat, r#type) = self.synth_ann_pat(pat.as_ref(), r#type.as_ref().map(|ty| ty.as_ref()));
        let param = FunParam::new(Plicity::Explicit, pat.name(), self.quote_value(&r#type));
        (param, r#type)
    }

    fn check_fun_param(
        &mut self,
        param: Located<&surface::FunParam<'text, 'surface>>,
        expected: &Type<'core>,
    ) -> Check<FunParam<'core, Expr<'core>>> {
        let surface::FunParam { pat, r#type } = param.data;
        let pat = self.check_ann_pat(
            pat.as_ref(),
            r#type.as_ref().map(|ty| ty.as_ref()),
            expected,
        );
        FunParam::new(Plicity::Explicit, pat.name(), self.quote_value(expected))
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

                let expr = Expr::FunType {
                    param: FunParam {
                        plicity: param.plicity,
                        name: param.name,
                        r#type: self.bump.alloc(param.r#type),
                    },
                    body: self.bump.alloc(body_expr),
                };
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
                    let body_type = self.quote_value(&body_type);
                    self.env.locals.pop();
                    (body_expr, body_type)
                };

                let param = FunParam {
                    plicity: param.plicity,
                    name: param.name,
                    r#type: &*self.bump.alloc(param.r#type),
                };
                let expr = Expr::FunLit {
                    param,
                    body: self.bump.alloc(body_expr),
                };
                let r#type = Type::FunType {
                    param: FunParam::new(param.plicity, param.name, self.bump.alloc(param_type)),
                    body: Closure::new(self.env.locals.values.clone(), self.bump.alloc(body_type)),
                };
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
        match params {
            [] => self.check_expr(body, expected),
            [param, params @ ..] => match expected {
                Value::FunType {
                    param: expected_param,
                    body: expected_body,
                } => {
                    let param = self.check_fun_param(param.as_ref(), expected_param.r#type);
                    let body_expr = {
                        let arg_value =
                            Value::local_var(self.env.locals.values.len().to_absolute());
                        self.env
                            .locals
                            .push_param(param.name, expected_param.r#type.clone());
                        let expected = self.apply_closure(expected_body.clone(), arg_value);
                        let body_expr = self.check_fun_expr(params, body, &expected);
                        self.env.locals.pop();
                        body_expr
                    };
                    let expr = Expr::FunLit {
                        param: FunParam::new(
                            param.plicity,
                            param.name,
                            self.bump.alloc(param.r#type),
                        ),
                        body: self.bump.alloc(body_expr),
                    };
                    expr
                }
                _ => {
                    let (expr, r#type) = self.synth_fun_expr(params, body);
                    self.coerce_expr(Located::new(body.range, expr), &r#type, expected)
                }
            },
        }
    }

    fn synth_fun_call(
        &mut self,
        callee: Located<&surface::Expr<'text, 'surface>>,
        args: &&[Located<surface::FunArg<'text, 'surface>>],
    ) -> (Expr<'core>, Value<'core>) {
        let (callee_expr, callee_type) = self.synth_expr(callee);
        let mut result_expr = callee_expr.clone();
        let mut result_type = callee_type.clone();

        for (arity, arg) in args.iter().enumerate() {
            match result_type {
                Value::FunType { param, body } => {
                    let arg_expr = self.check_expr(arg.data.expr.as_ref(), param.r#type);
                    let arg_value = self.eval_expr(&arg_expr);
                    let (expr, arg_expr) = self.bump.alloc((result_expr, arg_expr));
                    result_expr = Expr::FunApp {
                        fun: &*expr,
                        arg: FunArg::new(param.plicity, &*arg_expr),
                    };
                    result_type = self.apply_closure(body, arg_value);
                }
                _ if arity == 0 => {
                    self.diagnostic(
                        callee.range,
                        Diagnostic::error()
                            .with_message("Expected a function")
                            .with_notes(vec![format!(
                                "Help: the type of the callee is {callee_type:?}"
                            )]),
                    );
                    return (Expr::Error, Type::Error);
                }
                _ => {
                    self.diagnostic(
                        callee.range,
                        Diagnostic::error()
                            .with_message("Called function with too many arguments")
                            .with_notes(vec![
                                format!(
                                    "Help: the function expects {arity} arguments, but received {}",
                                    args.len()
                                ),
                                format!("Help: the type of the callee is {callee_type:?}"),
                            ]),
                    );
                    return (Expr::Error, Type::Error);
                }
            }
        }

        (callee_expr, result_type)
    }

    fn synth_number(&mut self, text: Located<&str>) -> Expr<'core> {
        let range = text.range;
        let text = match text.data.contains('_') {
            false => Cow::Borrowed(text.data),
            true => Cow::Owned(text.data.replace('_', "")),
        };

        let res = match () {
            _ if text.starts_with("0b") || text.starts_with("0B") => {
                u32::from_str_radix(&text[2..], 16)
            }
            _ if text.starts_with("0o") || text.starts_with("0O") => {
                u32::from_str_radix(&text[2..], 16)
            }
            _ if text.starts_with("0x") || text.starts_with("0X") => {
                u32::from_str_radix(&text[2..], 16)
            }
            _ => u32::from_str(&text),
        };

        match res {
            Ok(n) => Expr::Int(n),
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

        // TODO: Handle escape sequences, check string is terminated, check for invalid
        // characters
        Expr::String(self.bump.alloc_str(text))
    }

    fn synth_char(&mut self, text: Located<&str>) -> Expr<'core> {
        let range = text.range;
        let text = text.data;

        // TODO: Handle escape sequences, check string is terminated, check for invalid
        // characters
        Expr::Char('\0')
    }
}
