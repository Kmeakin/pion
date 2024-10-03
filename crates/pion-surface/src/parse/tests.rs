use std::fmt::Write;

use expect_test::{expect, Expect};

use super::*;
use crate::lex;

#[track_caller]
#[allow(clippy::needless_pass_by_value, reason = "It's just a test")]
fn assert_parse_pat(text: &str, expected: Expect) {
    let tokens = lex::lex(text);
    let bump = bumpalo::Bump::new();
    let (pat, diagnostics) = parse_pat(0, tokens, &bump);

    let mut got = String::new();
    write!(got, "{pat}").unwrap();

    if !diagnostics.is_empty() {
        writeln!(got).unwrap();
        for diagnostic in diagnostics {
            writeln!(got, "{diagnostic:?}").unwrap();
        }
    }

    expected.assert_eq(&got);
}

#[track_caller]
#[allow(clippy::needless_pass_by_value, reason = "It's just a test")]
fn assert_parse_expr(text: &str, expected: Expect) {
    let tokens = lex::lex(text);
    let bump = bumpalo::Bump::new();
    let (expr, diagnostics) = parse_expr(0, tokens, &bump);

    let mut got = String::new();
    write!(got, "{expr}").unwrap();
    let mut got = String::from(got.trim_end());

    if !diagnostics.is_empty() {
        got.push('\n');
        for diagnostic in diagnostics {
            writeln!(got, "{diagnostic:?}").unwrap();
        }
    }
    expected.assert_eq(&got);
}

#[track_caller]
#[allow(clippy::needless_pass_by_value, reason = "It's just a test")]
fn assert_parse_file(text: &str, expected: Expect) {
    let tokens = lex::lex(text);
    let bump = bumpalo::Bump::new();
    let (file, diagnostics) = parse_file(0, tokens, &bump);

    let mut got = String::new();
    write!(got, "{file}").unwrap();
    let mut got = String::from(got.trim_end());

    if !diagnostics.is_empty() {
        got.push('\n');
        for diagnostic in diagnostics {
            writeln!(got, "{diagnostic:?}").unwrap();
        }
    }
    expected.assert_eq(&got);
}

#[test]
fn wildcard_pat() {
    assert_parse_pat(
        "_",
        expect![[r"
        0..1 @ Pat::Underscore
    "]],
    );
}

#[test]
fn var_pat() { assert_parse_expr("abc", expect![[r#"0..3 @ Expr::Var("abc")"#]]); }

#[test]
fn paren_pat() {
    assert_parse_pat(
        "(_)",
        expect![[r"
                0..3 @ Pat::Paren
                 1..2 @ Pat::Underscore
            "]],
    );
}

#[test]
fn var_expr() { assert_parse_expr("abc", expect![[r#"0..3 @ Expr::Var("abc")"#]]); }

#[test]
fn paren_expr() {
    assert_parse_expr(
        "(abc)",
        expect![[r#"
                0..5 @ Expr::Paren
                 1..4 @ Expr::Var("abc")"#]],
    );
    assert_parse_expr(
        "((abc))",
        expect![[r#"
                0..7 @ Expr::Paren
                 1..6 @ Expr::Paren
                  2..5 @ Expr::Var("abc")"#]],
    );
}

#[test]
fn call_expr() {
    assert_parse_expr(
        "f()",
        expect![[r#"
                0..3 @ Expr::FunCall
                 0..1 @ Expr::Var("f")"#]],
    );
    assert_parse_expr(
        "f(a)",
        expect![[r#"
                0..4 @ Expr::FunCall
                 0..1 @ Expr::Var("f")
                 2..4 @ FunArg
                  2..3 @ Expr::Var("a")"#]],
    );
    assert_parse_expr(
        "f(a,)",
        expect![[r#"
                0..5 @ Expr::FunCall
                 0..1 @ Expr::Var("f")
                 2..4 @ FunArg
                  2..3 @ Expr::Var("a")"#]],
    );
    assert_parse_expr(
        "f(a, b)",
        expect![[r#"
                0..7 @ Expr::FunCall
                 0..1 @ Expr::Var("f")
                 2..4 @ FunArg
                  2..3 @ Expr::Var("a")
                 5..7 @ FunArg
                  5..6 @ Expr::Var("b")"#]],
    );
    assert_parse_expr(
        "f(a)(b)",
        expect![[r#"
                0..7 @ Expr::FunCall
                 0..4 @ Expr::FunCall
                  0..1 @ Expr::Var("f")
                  2..4 @ FunArg
                   2..3 @ Expr::Var("a")
                 5..7 @ FunArg
                  5..6 @ Expr::Var("b")"#]],
    );
}

#[test]
fn arrow_expr() {
    assert_parse_expr(
        "a -> b",
        expect![[r#"
                0..6 @ Expr::FunArrow
                 0..1 @ Expr::Var("a")
                 5..6 @ Expr::Var("b")"#]],
    );
    assert_parse_expr(
        "a -> b -> c",
        expect![[r#"
                0..11 @ Expr::FunArrow
                 0..1 @ Expr::Var("a")
                 5..11 @ Expr::FunArrow
                  5..6 @ Expr::Var("b")
                  10..11 @ Expr::Var("c")"#]],
    );
}

#[test]
fn fun_expr() {
    assert_parse_expr(
        "fun() => a",
        expect![[r#"
                0..10 @ Expr::FunExpr
                 9..10 @ Expr::Var("a")"#]],
    );
    assert_parse_expr(
        "fun(a) => a",
        expect![[r#"
                0..11 @ Expr::FunExpr
                 4..6 @ FunParam
                  4..5 @ Pat::Var("a")
                 10..11 @ Expr::Var("a")"#]],
    );
    assert_parse_expr(
        "fun(a: A) => a",
        expect![[r#"
                0..14 @ Expr::FunExpr
                 4..9 @ FunParam
                  4..8 @ Pat::TypeAnnotation
                   4..5 @ Pat::Var("a")
                   7..8 @ Expr::Var("A")
                 13..14 @ Expr::Var("a")"#]],
    );
    assert_parse_expr(
        "fun(a, b) => a",
        expect![[r#"
                0..14 @ Expr::FunExpr
                 4..6 @ FunParam
                  4..5 @ Pat::Var("a")
                 7..9 @ FunParam
                  7..8 @ Pat::Var("b")
                 13..14 @ Expr::Var("a")"#]],
    );
}

#[test]
fn forall_expr() {
    assert_parse_expr(
        "forall() -> a",
        expect![[r#"
                0..13 @ Expr::FunType
                 12..13 @ Expr::Var("a")"#]],
    );
    assert_parse_expr(
        "forall(a) -> a",
        expect![[r#"
                0..14 @ Expr::FunType
                 7..9 @ FunParam
                  7..8 @ Pat::Var("a")
                 13..14 @ Expr::Var("a")"#]],
    );
    assert_parse_expr(
        "forall(a: A) -> a",
        expect![[r#"
                0..17 @ Expr::FunType
                 7..12 @ FunParam
                  7..11 @ Pat::TypeAnnotation
                   7..8 @ Pat::Var("a")
                   10..11 @ Expr::Var("A")
                 16..17 @ Expr::Var("a")"#]],
    );
    assert_parse_expr(
        "forall(a, b) -> a",
        expect![[r#"
                0..17 @ Expr::FunType
                 7..9 @ FunParam
                  7..8 @ Pat::Var("a")
                 10..12 @ FunParam
                  10..11 @ Pat::Var("b")
                 16..17 @ Expr::Var("a")"#]],
    );
}

#[test]
fn bool_expr() {
    assert_parse_expr("true", expect!["0..4 @ Expr::Bool(true)"]);
    assert_parse_expr("false", expect!["0..5 @ Expr::Bool(false)"]);
}

#[test]
fn int_expr() {
    assert_parse_expr("1234", expect![[r#"0..4 @ Expr::Number("1234")"#]]);
    assert_parse_expr("0x1234", expect![[r#"0..6 @ Expr::Number("0x1234")"#]]);
    assert_parse_expr("0x1010", expect![[r#"0..6 @ Expr::Number("0x1010")"#]]);
}

#[test]
fn char_expr() { assert_parse_expr("'a'", expect![[r#"0..3 @ Expr::Char("'a'")"#]]); }

#[test]
fn string_expr() { assert_parse_expr(r#""a""#, expect![[r#"0..3 @ Expr::String("\"a\"")"#]]); }

#[test]
fn do_expr() {
    assert_parse_expr("do {}", expect!["0..5 @ Expr::Do"]);
    assert_parse_expr(
        "do { let x = 5; }",
        expect![[r#"
                0..17 @ Expr::Do
                 Stmt::Let
                  5..15 @ LetBinding
                   9..10 @ Pat::Var("x")
                   13..14 @ Expr::Number("5")"#]],
    );
    assert_parse_expr(
        "do { let x = 5; x }",
        expect![[r#"
                0..19 @ Expr::Do
                 Stmt::Let
                  5..15 @ LetBinding
                   9..10 @ Pat::Var("x")
                   13..14 @ Expr::Number("5")
                 16..17 @ Expr::Var("x")"#]],
    );
    assert_parse_expr(
        "do { x }",
        expect![[r#"
                0..8 @ Expr::Do
                 5..6 @ Expr::Var("x")"#]],
    );
}

#[test]
fn commands() {
    assert_parse_expr(
        "do { #check 1; }",
        expect![[r#"
                0..16 @ Expr::Do
                 Stmt::Command
                  Stmt::Check
                   12..13 @ Expr::Number("1")"#]],
    );
    assert_parse_expr(
        "do { #eval 1; }",
        expect![[r#"
                0..15 @ Expr::Do
                 Stmt::Command
                  Stmt::Eval
                   11..12 @ Expr::Number("1")"#]],
    );
}

#[test]
fn file() {
    assert_parse_file("", expect!["File"]);
    assert_parse_file(
        "let x = 5;",
        expect![[r#"
                File
                 Stmt::Let
                  0..10 @ LetBinding
                   4..5 @ Pat::Var("x")
                   8..9 @ Expr::Number("5")"#]],
    );
    assert_parse_file(
        "10;",
        expect![[r#"
                File
                 Stmt::Expr
                  0..2 @ Expr::Number("10")"#]],
    );
    assert_parse_file(
        "#check 10; 45;",
        expect![[r#"
                File
                 Stmt::Command
                  Stmt::Check
                   7..9 @ Expr::Number("10")
                 Stmt::Expr
                  11..13 @ Expr::Number("45")"#]],
    );
}
