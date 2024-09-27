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
}

impl Prec {
    pub const MAX: Self = Self::Fun;

    pub fn of_expr(expr: &Expr) -> Self {
        match expr {
            Expr::Error
            | Expr::Bool(_)
            | Expr::Int(_)
            | Expr::Char(_)
            | Expr::String(_)
            | Expr::PrimVar(_)
            | Expr::LocalVar(_)
            | Expr::MetaVar(_)
            | Expr::Do(..) => Self::Atom,
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
        Expr::FunType(param, body) => {
            write!(out, "forall(")?;
            fun_param(out, param, |out, expr| expr_prec(out, expr, Prec::MAX))?;
            write!(out, ") -> ")?;
            expr_prec(out, body, Prec::MAX)?;
        }
        Expr::FunLit(param, body) => {
            write!(out, "fun(")?;
            fun_param(out, param, |out, expr| expr_prec(out, expr, Prec::MAX))?;
            write!(out, ") => ")?;
            expr_prec(out, body, Prec::MAX)?;
        }
        Expr::FunApp(fun, arg) => {
            expr_prec(out, fun, Prec::Call)?;
            write!(out, "(")?;
            fun_arg(out, arg, |out, expr| expr_prec(out, expr, Prec::MAX))?;
            write!(out, ")")?;
        }
        Expr::Do(stmts, trailing_expr) => {
            write!(out, "do {{")?;
            for s in *stmts {
                stmt(out, s)?;
                write!(out, " ")?;
            }
            if let Some(expr) = trailing_expr {
                expr_prec(out, expr, prec)?;
            }
            write!(out, "}}")?;
        }
    }
    if parens {
        write!(out, ")")?;
    }
    Ok(())
}

pub fn stmt(out: &mut impl Write, stmt: &Stmt) -> fmt::Result {
    match stmt {
        Stmt::Let(binding) => let_binding(out, binding),
        Stmt::Expr(expr) => {
            write!(out, "let ")?;
            expr_prec(out, expr, Prec::MAX)?;
            write!(out, ";")
        }
    }
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
            write!(out, ") -> ")?;
            expr_prec(out, body.body, Prec::MAX)?;
        }
        Value::FunLit(param, body) => {
            write!(out, "fun(")?;
            fun_param(out, param, |out, expr| expr_prec(out, expr, Prec::MAX))?;
            write!(out, ") => ")?;
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

fn let_binding(out: &mut impl Write, binding: &LetBinding<Expr>) -> fmt::Result {
    let LetBinding { name, r#type, init } = binding;
    pat(out, name)?;
    write!(out, " : ")?;
    expr_prec(out, r#type, Prec::Fun)?;
    write!(out, " = ")?;
    expr_prec(out, init, Prec::Fun)?;
    write!(out, ";")?;
    Ok(())
}

impl fmt::Display for Expr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { expr_prec(f, self, Prec::MAX) }
}

impl fmt::Display for Value<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { value_prec(f, self, Prec::MAX) }
}

#[cfg(test)]
mod tests {
    use ecow::eco_vec;
    use expect_test::*;

    use super::*;
    use crate::env::{AbsoluteVar, RelativeVar};
    use crate::semantics::Closure;

    #[track_caller]
    #[allow(clippy::needless_pass_by_value, reason = "It's only a test")]
    fn assert_print_expr(expr: &Expr, expected: Expect) {
        let mut actual = String::new();
        expr_prec(&mut actual, expr, Prec::MAX).unwrap();
        expected.assert_eq(&actual);
    }

    #[track_caller]
    #[allow(clippy::needless_pass_by_value, reason = "It's only a test")]
    fn assert_print_value(value: &Value, expected: Expect) {
        let mut actual = String::new();
        value_prec(&mut actual, value, Prec::MAX).unwrap();
        expected.assert_eq(&actual);
    }

    #[test]
    fn print_expr_bool() {
        assert_print_expr(&Expr::Bool(true), expect!["true"]);
        assert_print_expr(&Expr::Bool(false), expect!["false"]);
    }

    #[test]
    fn print_expr_int() { assert_print_expr(&Expr::Int(42), expect!["42"]); }

    #[test]
    fn print_expr_char() { assert_print_expr(&Expr::Char('a'), expect!["'a'"]); }

    #[test]
    fn print_expr_string() { assert_print_expr(&Expr::String("hello"), expect![[r#""hello""#]]); }

    #[test]
    fn print_expr_prim_var() {
        let expr = Expr::BOOL;
        assert_print_expr(&expr, expect!["Bool"]);
    }

    #[test]
    fn print_expr_local_var() {
        let expr = Expr::LocalVar(RelativeVar::new(0));
        assert_print_expr(&expr, expect!["_#0"]);
    }

    #[test]
    fn print_expr_meta_var() {
        let expr = Expr::MetaVar(AbsoluteVar::new(0));
        assert_print_expr(&expr, expect!["?0"]);
    }

    #[test]
    fn print_expr_fun_type() {
        let expr = Expr::FunType(FunParam::explicit(None, &Expr::INT), &Expr::BOOL);
        assert_print_expr(&expr, expect!["forall(_ : Int) -> Bool"]);

        let expr = Expr::FunType(FunParam::implicit(None, &Expr::INT), &Expr::BOOL);
        assert_print_expr(&expr, expect!["forall(@_ : Int) -> Bool"]);

        let expr = Expr::FunType(
            FunParam::explicit(None, &Expr::INT),
            &const { Expr::FunType(FunParam::explicit(None, &Expr::BOOL), &Expr::CHAR) },
        );
        assert_print_expr(
            &expr,
            expect!["forall(_ : Int) -> forall(_ : Bool) -> Char"],
        );

        let expr = Expr::FunType(
            FunParam::explicit(
                None,
                &const { Expr::FunType(FunParam::explicit(None, &Expr::INT), &Expr::BOOL) },
            ),
            &Expr::CHAR,
        );
        assert_print_expr(
            &expr,
            expect!["forall(_ : forall(_ : Int) -> Bool) -> Char"],
        );
    }

    #[test]
    fn print_expr_fun_lit() {
        let expr = Expr::FunLit(FunParam::explicit(None, &Expr::INT), &Expr::Int(5));
        assert_print_expr(&expr, expect!["fun(_ : Int) => 5"]);

        let expr = Expr::FunLit(FunParam::implicit(None, &Expr::INT), &Expr::Int(5));
        assert_print_expr(&expr, expect!["fun(@_ : Int) => 5"]);

        let expr = Expr::FunLit(
            FunParam::explicit(None, &Expr::INT),
            &const {
                Expr::FunLit(
                    FunParam::explicit(None, &Expr::BOOL),
                    &const { Expr::LocalVar(RelativeVar::new(0)) },
                )
            },
        );
        assert_print_expr(&expr, expect!["fun(_ : Int) => fun(_ : Bool) => _#0"]);
    }

    #[test]
    fn print_expr_fun_app() {
        let expr = Expr::FunApp(&Expr::INT, FunArg::explicit(&Expr::Int(1)));
        assert_print_expr(&expr, expect!["Int(1)"]);

        let expr = Expr::FunApp(&Expr::INT, FunArg::implicit(&Expr::Int(1)));
        assert_print_expr(&expr, expect!["Int(@1)"]);

        let fun = Expr::FunApp(&Expr::BOOL, FunArg::explicit(&Expr::Bool(true)));
        let expr = Expr::FunApp(&fun, FunArg::explicit(&Expr::Int(1)));
        assert_print_expr(&expr, expect!["Bool(true)(1)"]);

        let expr = Expr::FunApp(
            &const {
                Expr::FunLit(
                    FunParam::explicit(None, &Expr::INT),
                    &const { Expr::LocalVar(RelativeVar::new(0)) },
                )
            },
            FunArg::explicit(&Expr::Int(1)),
        );
        assert_print_expr(&expr, expect!["(fun(_ : Int) => _#0)(1)"]);
    }

    #[test]
    fn print_value_bool() {
        assert_print_value(&Value::Bool(true), expect!["true"]);
        assert_print_value(&Value::Bool(false), expect!["false"]);
    }

    #[test]
    fn print_value_int() { assert_print_value(&Value::Int(42), expect!["42"]); }

    #[test]
    fn print_value_char() { assert_print_value(&Value::Char('a'), expect!["'a'"]); }

    #[test]
    fn print_value_string() { assert_print_value(&Value::String("hello"), expect!["\"hello\""]); }

    #[test]
    fn print_value_local_var() {
        let value = Value::local_var(AbsoluteVar::new(0));
        assert_print_value(&value, expect!["_#0"]);
    }

    #[test]
    fn print_value_meta_var() {
        let value = Value::meta_var(AbsoluteVar::new(0));
        assert_print_value(&value, expect!["?0"]);
    }

    #[test]
    fn print_value_prim_var() {
        let value = Value::BOOL;
        assert_print_value(&value, expect!["Bool"]);
    }

    #[test]
    fn print_value_neutral() {
        let value = Value::Neutral(
            Head::LocalVar(AbsoluteVar::new(0)),
            eco_vec![Elim::FunApp(FunArg::explicit(Value::Int(1)))],
        );
        assert_print_value(&value, expect!["_#0(1)"]);

        let value = Value::Neutral(
            Head::LocalVar(AbsoluteVar::new(0)),
            eco_vec![Elim::FunApp(FunArg::implicit(Value::Int(1)))],
        );
        assert_print_value(&value, expect!["_#0(@1)"]);
    }

    #[test]
    fn print_value_fun_type() {
        let value = Value::FunType(
            FunParam::explicit(None, &Expr::Int(1)),
            Closure::empty(&Expr::Bool(true)),
        );
        assert_print_value(&value, expect!["forall(_ : 1) -> true"]);

        let value = Value::FunType(
            FunParam::implicit(None, &Expr::Int(1)),
            Closure::empty(&Expr::Bool(true)),
        );
        assert_print_value(&value, expect!["forall(@_ : 1) -> true"]);
    }

    #[test]
    fn print_value_fun_lit() {
        let value = Value::FunLit(
            FunParam::explicit(None, &Expr::Int(1)),
            Closure::empty(&Expr::Bool(true)),
        );
        assert_print_value(&value, expect!["fun(_ : 1) => true"]);

        let value = Value::FunLit(
            FunParam::implicit(None, &Expr::Int(1)),
            Closure::empty(&Expr::Bool(true)),
        );
        assert_print_value(&value, expect!["fun(@_ : 1) => true"]);
    }
}
