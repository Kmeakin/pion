use core::fmt;
use std::fmt::Write;

use crate::env::DeBruijnIndex;
use crate::syntax::*;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Prec {
    Atom,
    Call,
    If,
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
            Expr::If(..) => Self::If,
        }
    }
}

pub fn type_ann_expr(out: &mut impl Write, expr: &Expr, r#type: &Expr) -> fmt::Result {
    expr_prec(out, expr, Prec::Call)?;
    write!(out, " : ")?;
    expr_prec(out, r#type, Prec::Fun)?;
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
        Expr::LocalVar(var) => match var.name {
            Some(name) => write!(out, "{name}")?,
            None => write!(out, "#var({:?})", var.de_bruijn)?,
        },
        Expr::MetaVar(var) => write!(out, "?{}", var.de_bruijn)?,
        Expr::FunType(param, body) if !body.binds_local(DeBruijnIndex::new(0)) => {
            plicity(out, param.plicity)?;
            expr_prec(out, param.r#type, Prec::Call)?;
            write!(out, " -> ")?;
            expr_prec(out, body, Prec::MAX)?;
        }
        Expr::FunType(..) => {
            let mut expr = expr;
            let params = std::iter::from_fn(|| match expr {
                Expr::FunType(param, body) if body.binds_local(DeBruijnIndex::new(0)) => {
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
        Expr::If(cond, then, r#else) => {
            write!(out, "if ")?;
            expr_prec(out, cond, Prec::MAX)?;
            write!(out, " then ")?;
            expr_prec(out, then, Prec::MAX)?;
            write!(out, " else ")?;
            expr_prec(out, r#else, Prec::MAX)?;
        }
    }
    if parens {
        write!(out, ")")?;
    }
    Ok(())
}

pub fn stmt(out: &mut impl Write, stmt: &Stmt) -> fmt::Result {
    match stmt {
        Stmt::Let(binding) => let_stmt(out, binding),
        Stmt::Expr(expr) => {
            expr_prec(out, expr, Prec::MAX)?;
            write!(out, ";")
        }
    }
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
    plicity(out, param.plicity)?;
    pat(out, param.name)?;
    write!(out, " : ")?;
    on_expr(out, &param.r#type)?;
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
    plicity(out, arg.plicity)?;
    on_expr(out, &arg.expr)?;
    Ok(())
}

fn plicity<W: Write>(out: &mut W, plicity: Plicity) -> fmt::Result {
    match plicity {
        Plicity::Implicit => write!(out, "@"),
        Plicity::Explicit => Ok(()),
    }
}

fn pat(out: &mut impl Write, name: Name) -> fmt::Result {
    match name {
        None => write!(out, "_"),
        Some(name) => write!(out, "{name}"),
    }
}

pub fn let_stmt(out: &mut impl Write, binding: &LetBinding<Expr>) -> fmt::Result {
    let LetBinding { name, r#type, init } = binding;
    write!(out, "let ")?;
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
    use expect_test::*;

    use super::*;
    use crate::env::{DeBruijnIndex, DeBruijnLevel};

    #[track_caller]
    #[allow(clippy::needless_pass_by_value, reason = "It's only a test")]
    fn assert_print_expr(expr: &Expr, expected: Expect) {
        let mut actual = String::new();
        expr_prec(&mut actual, expr, Prec::MAX).unwrap();
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
        let expr = Expr::LocalVar(LocalVar::new(None, DeBruijnIndex::new(0)));
        assert_print_expr(&expr, expect!["#var(DeBruijnIndex(0))"]);
    }

    #[test]
    fn print_expr_meta_var() {
        let expr = Expr::MetaVar(MetaVar::new(DeBruijnLevel::new(0)));
        assert_print_expr(&expr, expect!["?0"]);
    }

    #[test]
    fn print_expr_fun_type() {
        let expr = Expr::FunType(FunParam::explicit(None, &Expr::INT), &Expr::BOOL);
        assert_print_expr(&expr, expect!["Int -> Bool"]);

        let expr = Expr::FunType(FunParam::implicit(None, &Expr::INT), &Expr::BOOL);
        assert_print_expr(&expr, expect!["@Int -> Bool"]);

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
                    &const { Expr::LocalVar(LocalVar::new(None, DeBruijnIndex::new(0))) },
                )
            },
        );
        assert_print_expr(
            &expr,
            expect!["fun(_ : Int, _ : Bool) => #var(DeBruijnIndex(0))"],
        );
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
                    &const { Expr::LocalVar(LocalVar::new(None, DeBruijnIndex::new(0))) },
                )
            },
            FunArg::explicit(&int),
        );
        assert_print_expr(
            &expr,
            expect!["(fun(_ : Int) => #var(DeBruijnIndex(0)))(1)"],
        );
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
            Some(&const { Expr::LocalVar(LocalVar::new(None, DeBruijnIndex::new(0))) }),
        );
        assert_print_expr(
            &expr,
            expect!["do {let _ : Int = 1; let _ : Bool = true; #var(DeBruijnIndex(0))}"],
        );
    }

    #[test]
    fn print_expr_if() {
        let expr = Expr::If(
            &const { Expr::bool(true) },
            &const { Expr::int(1) },
            &const { Expr::int(2) },
        );
        assert_print_expr(&expr, expect!["if true then 1 else 2"]);
    }
}
