use core::fmt;
use std::fmt::Write;

use crate::env::RelativeVar;
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
            | Expr::Lit(_)
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
            Value::Lit(_) => Self::Atom,
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
        Expr::Lit(lit) => write!(out, "{lit}")?,
        Expr::PrimVar(var) => write!(out, "{var}")?,
        Expr::LocalVar(var) => write!(out, "#var({var})")?,
        Expr::MetaVar(var) => write!(out, "?{var}")?,
        Expr::FunType(param, body) if !body.binds_local(RelativeVar::new(0)) => {
            expr_prec(out, param.r#type, Prec::Call)?;
            write!(out, " -> ")?;
            expr_prec(out, body, Prec::MAX)?;
        }
        Expr::FunType(..) => {
            let mut expr = expr;
            let params = std::iter::from_fn(|| match expr {
                Expr::FunType(param, body) => {
                    expr = body;
                    Some(param)
                }
                body => {
                    expr = body;
                    None
                }
            });

            write!(out, "forall(")?;
            fun_params(out, params, |out, expr| expr_prec(out, expr, Prec::MAX))?;
            write!(out, ") -> ")?;
            expr_prec(out, expr, Prec::MAX)?;
        }
        Expr::FunLit(..) => {
            let mut expr = expr;
            let params = std::iter::from_fn(|| match expr {
                Expr::FunLit(param, body) => {
                    expr = body;
                    Some(param)
                }
                body => {
                    expr = body;
                    None
                }
            });

            write!(out, "fun(")?;
            fun_params(out, params, |out, expr| expr_prec(out, expr, Prec::MAX))?;
            write!(out, ") => ")?;
            expr_prec(out, expr, Prec::MAX)?;
        }
        Expr::FunApp(..) => {
            let mut args = Vec::new();
            let mut callee = expr;
            while let Expr::FunApp(head, arg) = callee {
                callee = head;
                args.push(arg);
            }
            expr_prec(out, callee, Prec::Call)?;
            write!(out, "(")?;
            fun_args(out, args.into_iter().rev(), |out, expr| {
                expr_prec(out, expr, Prec::MAX)
            })?;
            write!(out, ")")?;
        }
        Expr::Do([], None) => write!(out, "do {{}}")?,
        Expr::Do([], Some(trailing_expr)) => {
            write!(out, "do {{ ")?;
            expr_prec(out, trailing_expr, prec)?;
            write!(out, " }}")?;
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
        Stmt::Let(binding) => {
            write!(out, "let ")?;
            let_binding(out, binding)
        }
        Stmt::Expr(expr) => {
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
        Value::Lit(lit) => write!(out, "{lit}")?,
        Value::Neutral(head, spine) => {
            match head {
                Head::Error => write!(out, "#error")?,
                Head::LocalVar(var) => write!(out, "#var({var})")?,
                Head::MetaVar(var) => write!(out, "?{var}")?,
                Head::PrimVar(var) => write!(out, "{var}")?,
            }

            if spine.is_empty() {
                return Ok(());
            }

            let args = spine.into_iter().map(|elim| match elim {
                Elim::FunApp(arg) => arg,
            });
            write!(out, "(")?;
            fun_args(out, args, |out, value| value_prec(out, value, Prec::MAX))?;
            write!(out, ")")?;
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

fn fun_params<'a, W: Write, T: 'a>(
    out: &mut W,
    params: impl IntoIterator<Item = &'a FunParam<'a, T>>,
    on_expr: impl Copy + FnMut(&mut W, &T) -> fmt::Result,
) -> fmt::Result {
    let mut params = params.into_iter();

    if let Some(first) = params.next() {
        fun_param(out, first, on_expr)?;

        for param in params {
            write!(out, ", ")?;
            fun_param(out, param, on_expr)?;
        }
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
    pat(out, *name)?;
    write!(out, " : ")?;
    on_expr(out, r#type)?;
    Ok(())
}

fn fun_args<'a, W: Write, T: 'a>(
    out: &mut W,
    args: impl IntoIterator<Item = &'a FunArg<T>>,
    on_expr: impl Copy + FnMut(&mut W, &T) -> fmt::Result,
) -> fmt::Result {
    let mut args = args.into_iter();

    if let Some(first) = args.next() {
        fun_arg(out, first, on_expr)?;

        for arg in args {
            write!(out, ", ")?;
            fun_arg(out, arg, on_expr)?;
        }
    }

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

fn pat(out: &mut impl Write, name: Name) -> fmt::Result {
    match name {
        None => write!(out, "_"),
        Some(name) => write!(out, "{name}"),
    }
}

fn let_binding(out: &mut impl Write, binding: &LetBinding<Expr>) -> fmt::Result {
    let LetBinding { name, r#type, init } = binding;
    pat(out, *name)?;
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

impl fmt::Display for Lit<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lit::Bool(true) => write!(f, "true"),
            Lit::Bool(false) => write!(f, "false"),
            Lit::Int(n) => write!(f, "{n}"),
            Lit::Char(c) => write!(f, "{c:?}"),
            Lit::String(s) => write!(f, "{s:?}"),
        }
    }
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
        assert_print_expr(&Expr::bool(true), expect!["true"]);
        assert_print_expr(&Expr::bool(false), expect!["false"]);
    }

    #[test]
    fn print_expr_int() { assert_print_expr(&Expr::int(42), expect!["42"]); }

    #[test]
    fn print_expr_char() { assert_print_expr(&Expr::char('a'), expect!["'a'"]); }

    #[test]
    fn print_expr_string() { assert_print_expr(&Expr::string("hello"), expect![[r#""hello""#]]); }

    #[test]
    fn print_expr_prim_var() {
        let expr = Expr::BOOL;
        assert_print_expr(&expr, expect!["Bool"]);
    }

    #[test]
    fn print_expr_local_var() {
        let expr = Expr::LocalVar(RelativeVar::new(0));
        assert_print_expr(&expr, expect!["#var(0)"]);
    }

    #[test]
    fn print_expr_meta_var() {
        let expr = Expr::MetaVar(AbsoluteVar::new(0));
        assert_print_expr(&expr, expect!["?0"]);
    }

    #[test]
    fn print_expr_fun_type() {
        let expr = Expr::FunType(FunParam::explicit(None, &Expr::INT), &Expr::BOOL);
        assert_print_expr(&expr, expect!["Int -> Bool"]);

        let expr = Expr::FunType(FunParam::implicit(None, &Expr::INT), &Expr::BOOL);
        assert_print_expr(&expr, expect!["Int -> Bool"]);

        let expr = Expr::FunType(
            FunParam::explicit(None, &Expr::INT),
            &const { Expr::FunType(FunParam::explicit(None, &Expr::BOOL), &Expr::CHAR) },
        );
        assert_print_expr(&expr, expect!["Int -> Bool -> Char"]);

        let expr = Expr::FunType(
            FunParam::explicit(
                None,
                &const { Expr::FunType(FunParam::explicit(None, &Expr::INT), &Expr::BOOL) },
            ),
            &Expr::CHAR,
        );
        assert_print_expr(&expr, expect!["(Int -> Bool) -> Char"]);
    }

    #[test]
    fn print_expr_fun_lit() {
        let int = Expr::int(5);
        let expr = Expr::FunLit(FunParam::explicit(None, &Expr::INT), &int);
        assert_print_expr(&expr, expect!["fun(_ : Int) => 5"]);

        let expr = Expr::FunLit(FunParam::implicit(None, &Expr::INT), &int);
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
        assert_print_expr(&expr, expect!["fun(_ : Int, _ : Bool) => #var(0)"]);
    }

    #[test]
    fn print_expr_fun_app() {
        let int = Expr::int(1);
        let expr = Expr::FunApp(&Expr::INT, FunArg::explicit(&int));
        assert_print_expr(&expr, expect!["Int(1)"]);

        let expr = Expr::FunApp(&Expr::INT, FunArg::implicit(&int));
        assert_print_expr(&expr, expect!["Int(@1)"]);

        let b = Expr::bool(true);
        let fun = Expr::FunApp(&Expr::BOOL, FunArg::explicit(&b));
        let expr = Expr::FunApp(&fun, FunArg::explicit(&int));
        assert_print_expr(&expr, expect!["Bool(true, 1)"]);

        let expr = Expr::FunApp(
            &const {
                Expr::FunLit(
                    FunParam::explicit(None, &Expr::INT),
                    &const { Expr::LocalVar(RelativeVar::new(0)) },
                )
            },
            FunArg::explicit(&int),
        );
        assert_print_expr(&expr, expect!["(fun(_ : Int) => #var(0))(1)"]);
    }

    #[test]
    fn print_expr_do() {
        let expr = Expr::Do(
            &const {
                [
                    Stmt::Let(LetBinding::new(None, Expr::INT, Expr::int(1))),
                    Stmt::Let(LetBinding::new(None, Expr::BOOL, Expr::bool(true))),
                ]
            },
            Some(&const { Expr::LocalVar(RelativeVar::new(0)) }),
        );
        assert_print_expr(
            &expr,
            expect!["do {let _ : Int = 1; let _ : Bool = true; #var(0)}"],
        );
    }

    #[test]
    fn print_value_bool() {
        assert_print_value(&Value::bool(true), expect!["true"]);
        assert_print_value(&Value::bool(false), expect!["false"]);
    }

    #[test]
    fn print_value_int() { assert_print_value(&Value::int(42), expect!["42"]); }

    #[test]
    fn print_value_char() { assert_print_value(&Value::char('a'), expect!["'a'"]); }

    #[test]
    fn print_value_string() { assert_print_value(&Value::string("hello"), expect!["\"hello\""]); }

    #[test]
    fn print_value_local_var() {
        let value = Value::local_var(AbsoluteVar::new(0));
        assert_print_value(&value, expect!["#var(0)"]);
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
            eco_vec![Elim::FunApp(FunArg::explicit(Value::int(1)))],
        );
        assert_print_value(&value, expect!["#var(0)(1)"]);

        let value = Value::Neutral(
            Head::LocalVar(AbsoluteVar::new(0)),
            eco_vec![Elim::FunApp(FunArg::implicit(Value::int(1)))],
        );
        assert_print_value(&value, expect!["#var(0)(@1)"]);
    }

    #[test]
    fn print_value_fun_type() {
        let b = Expr::bool(true);
        let int = Expr::int(1);
        let value = Value::FunType(FunParam::explicit(None, &int), Closure::empty(&b));
        assert_print_value(&value, expect!["forall(_ : 1) -> true"]);

        let value = Value::FunType(FunParam::implicit(None, &int), Closure::empty(&b));
        assert_print_value(&value, expect!["forall(@_ : 1) -> true"]);
    }

    #[test]
    fn print_value_fun_lit() {
        let b = Expr::bool(true);
        let int = Expr::int(1);
        let value = Value::FunLit(FunParam::explicit(None, &int), Closure::empty(&b));
        assert_print_value(&value, expect!["fun(_ : 1) => true"]);

        let value = Value::FunLit(FunParam::implicit(None, &int), Closure::empty(&b));
        assert_print_value(&value, expect!["fun(@_ : 1) => true"]);
    }
}
