use core::fmt;
use std::fmt::Write;

use pion_interner::InternedStr;

use crate::semantics::{Elim, Head, Value};
use crate::syntax::*;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Prec {
    Atom,
    Call,
    Fun,
    Let,
}

impl Prec {
    pub const MAX: Self = Self::Let;

    pub fn of_expr(expr: &Expr) -> Self {
        match expr {
            Expr::Error
            | Expr::Bool(_)
            | Expr::Int(_)
            | Expr::Char(_)
            | Expr::String(_)
            | Expr::PrimVar(_)
            | Expr::LocalVar(_)
            | Expr::MetaVar(_) => Self::Atom,
            Expr::Let(..) => Self::Let,
            Expr::FunType(..) | Expr::FunLit(..) => Self::Fun,
            Expr::FunApp(..) => Self::Call,
        }
    }

    pub fn of_value(value: &Value) -> Self {
        match value {
            Value::Bool(_) | Value::Int(_) | Value::Char(_) | Value::String(_) => Self::Atom,
            Value::Neutral(..) => Self::Call,
            Value::FunType(..) | Value::FunLit(..) => Self::Fun,
        }
    }
}

pub fn type_ann_expr(out: &mut impl Write, expr: &Expr, r#type: &Value) -> fmt::Result {
    expr_prec(out, expr, Prec::Call)?;
    write!(out, " : ")?;
    value_prec(out, r#type, Prec::Fun)?;
    Ok(())
}

pub fn expr_prec(out: &mut impl Write, expr: &Expr, prec: Prec) -> fmt::Result {
    let parens = Prec::of_expr(expr) > prec;
    if parens {
        write!(out, "(")?;
    }
    match expr {
        Expr::Error => write!(out, "#error")?,
        Expr::Bool(true) => write!(out, "true")?,
        Expr::Bool(false) => write!(out, "false")?,
        Expr::Int(n) => write!(out, "{n}")?,
        Expr::Char(c) => write!(out, "{c:?}")?,
        Expr::String(s) => write!(out, "{s:?}")?,
        Expr::PrimVar(var) => write!(out, "{var}")?,
        Expr::LocalVar(var) => write!(out, "_#{var}")?,
        Expr::MetaVar(var) => write!(out, "?{var}")?,
        Expr::Let(binding, body) => {
            write!(out, "let ")?;
            let_binding(out, binding)?;
            write!(out, "; ")?;
            expr_prec(out, body, Prec::MAX)?;
        }
        Expr::FunType(param, body) => {
            write!(out, "forall(")?;
            fun_param(out, param, |out, expr| expr_prec(out, expr, Prec::MAX))?;
            write!(out, ") -> ")?;
            expr_prec(out, body, Prec::MAX)?;
        }
        Expr::FunLit(param, body) => {
            write!(out, "fun(")?;
            fun_param(out, param, |out, expr| expr_prec(out, expr, Prec::MAX))?;
            write!(out, ") =>")?;
            expr_prec(out, body, Prec::MAX)?;
        }
        Expr::FunApp(fun, arg) => {
            expr_prec(out, fun, Prec::Call)?;
            write!(out, "(")?;
            fun_arg(out, arg, |out, expr| expr_prec(out, expr, Prec::MAX))?;
            write!(out, ")")?;
        }
    }
    if parens {
        write!(out, ")")?;
    }
    Ok(())
}

pub fn value_prec(out: &mut impl Write, value: &Value, prec: Prec) -> fmt::Result {
    let parens = Prec::of_value(value) > prec;
    if parens {
        write!(out, "(")?;
    }
    match value {
        Value::Bool(true) => write!(out, "true")?,
        Value::Bool(false) => write!(out, "false")?,
        Value::Int(n) => write!(out, "{n}")?,
        Value::Char(c) => write!(out, "{c:?}")?,
        Value::String(s) => write!(out, "{s:?}")?,
        Value::Neutral(head, spine) => {
            match head {
                Head::Error => write!(out, "#error")?,
                Head::LocalVar(var) => write!(out, "_#{var}")?,
                Head::MetaVar(var) => write!(out, "?{var}")?,
                Head::PrimVar(var) => write!(out, "{var}")?,
            }
            for elim in spine {
                match elim {
                    Elim::FunApp(arg) => {
                        write!(out, "(")?;
                        fun_arg(out, arg, |out, value| value_prec(out, value, Prec::MAX))?;
                        write!(out, ")")?;
                    }
                }
            }
        }
        Value::FunType(param, body) => {
            write!(out, "forall(")?;
            fun_param(out, param, |out, expr| expr_prec(out, expr, Prec::MAX))?;
            write!(out, ") ")?;
            expr_prec(out, body.body, Prec::MAX)?;
        }
        Value::FunLit(param, body) => {
            write!(out, "fun(")?;
            fun_param(out, param, |out, expr| expr_prec(out, expr, Prec::MAX))?;
            write!(out, ") ")?;
            expr_prec(out, body.body, Prec::MAX)?;
        }
    }
    if parens {
        write!(out, ")")?;
    }

    Ok(())
}

fn fun_param<W: Write, T>(
    out: &mut W,
    param: &FunParam<T>,
    mut on_expr: impl FnMut(&mut W, &T) -> fmt::Result,
) -> fmt::Result {
    let FunParam {
        plicity,
        name,
        r#type,
    } = param;

    match plicity {
        Plicity::Explicit => write!(out, "")?,
        Plicity::Implicit => write!(out, "@")?,
    }
    pat(out, name)?;
    write!(out, " : ")?;
    on_expr(out, r#type)?;
    Ok(())
}

fn fun_arg<W: Write, T>(
    out: &mut W,
    arg: &FunArg<T>,
    mut on_expr: impl FnMut(&mut W, &T) -> fmt::Result,
) -> fmt::Result {
    let FunArg { plicity, expr } = arg;
    match plicity {
        Plicity::Explicit => write!(out, "")?,
        Plicity::Implicit => write!(out, "@")?,
    }
    on_expr(out, expr)?;
    Ok(())
}

fn pat(out: &mut impl Write, name: &Option<InternedStr>) -> fmt::Result {
    match name {
        None => write!(out, "_"),
        Some(name) => write!(out, "{name}"),
    }
}

fn let_binding(out: &mut impl Write, binding: &LetBinding<&Expr>) -> fmt::Result {
    let LetBinding { name, r#type, rhs } = binding;
    pat(out, name)?;
    write!(out, " : ")?;
    expr_prec(out, r#type, Prec::MAX)?;
    write!(out, " = ")?;
    expr_prec(out, rhs, Prec::MAX)?;
    Ok(())
}

impl fmt::Debug for Expr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { expr_prec(f, self, Prec::MAX) }
}

impl fmt::Debug for Value<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { value_prec(f, self, Prec::MAX) }
}
