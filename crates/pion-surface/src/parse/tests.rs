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
fn bool_pat() {
    assert_parse_pat(
        "true",
        expect![[r"
        0..4 @ Pat::Lit(Bool(true))
    "]],
    );
    assert_parse_pat(
        "false",
        expect![[r"
        0..5 @ Pat::Lit(Bool(false))
    "]],
    );
}

#[test]
fn int_pat() {
    assert_parse_pat(
        "1234",
        expect![[r#"
        0..4 @ Pat::Lit(Int("1234"))
    "#]],
    );
    assert_parse_pat(
        "0x1234",
        expect![[r#"
        0..6 @ Pat::Lit(Int("0x1234"))
    "#]],
    );
    assert_parse_pat(
        "0x1010",
        expect![[r#"
        0..6 @ Pat::Lit(Int("0x1010"))
    "#]],
    );
}

#[test]
fn char_pat() {
    assert_parse_pat(
        "'a'",
        expect![[r#"
    0..3 @ Pat::Lit(Char("'a'"))
"#]],
    );
}

#[test]
fn string_pat() {
    assert_parse_pat(
        r#""a""#,
        expect![[r#"
    0..3 @ Pat::Lit(String("\"a\""))
"#]],
    );
}

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
             2..4 @ FunArg(Explicit)
              2..3 @ Expr::Var("a")"#]],
    );
    assert_parse_expr(
        "f(a,)",
        expect![[r#"
            0..5 @ Expr::FunCall
             0..1 @ Expr::Var("f")
             2..4 @ FunArg(Explicit)
              2..3 @ Expr::Var("a")"#]],
    );
    assert_parse_expr(
        "f(a, b)",
        expect![[r#"
            0..7 @ Expr::FunCall
             0..1 @ Expr::Var("f")
             2..4 @ FunArg(Explicit)
              2..3 @ Expr::Var("a")
             5..7 @ FunArg(Explicit)
              5..6 @ Expr::Var("b")"#]],
    );
    assert_parse_expr(
        "f(a)(b)",
        expect![[r#"
            0..7 @ Expr::FunCall
             0..4 @ Expr::FunCall
              0..1 @ Expr::Var("f")
              2..4 @ FunArg(Explicit)
               2..3 @ Expr::Var("a")
             5..7 @ FunArg(Explicit)
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
             4..6 @ FunParam(Explicit)
              4..5 @ Pat::Var("a")
             10..11 @ Expr::Var("a")"#]],
    );
    assert_parse_expr(
        "fun(a: A) => a",
        expect![[r#"
            0..14 @ Expr::FunExpr
             4..9 @ FunParam(Explicit)
              4..8 @ Pat::TypeAnnotation
               4..5 @ Pat::Var("a")
               7..8 @ Expr::Var("A")
             13..14 @ Expr::Var("a")"#]],
    );
    assert_parse_expr(
        "fun(a, b) => a",
        expect![[r#"
            0..14 @ Expr::FunExpr
             4..6 @ FunParam(Explicit)
              4..5 @ Pat::Var("a")
             7..9 @ FunParam(Explicit)
              7..8 @ Pat::Var("b")
             13..14 @ Expr::Var("a")"#]],
    );
    assert_parse_expr(
        "fun(@a: A) => a",
        expect![[r#"
            0..15 @ Expr::FunExpr
             4..10 @ FunParam(Implicit)
              5..9 @ Pat::TypeAnnotation
               5..6 @ Pat::Var("a")
               8..9 @ Expr::Var("A")
             14..15 @ Expr::Var("a")"#]],
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
             7..9 @ FunParam(Explicit)
              7..8 @ Pat::Var("a")
             13..14 @ Expr::Var("a")"#]],
    );
    assert_parse_expr(
        "forall(a: A) -> a",
        expect![[r#"
            0..17 @ Expr::FunType
             7..12 @ FunParam(Explicit)
              7..11 @ Pat::TypeAnnotation
               7..8 @ Pat::Var("a")
               10..11 @ Expr::Var("A")
             16..17 @ Expr::Var("a")"#]],
    );
    assert_parse_expr(
        "forall(a, b) -> a",
        expect![[r#"
            0..17 @ Expr::FunType
             7..9 @ FunParam(Explicit)
              7..8 @ Pat::Var("a")
             10..12 @ FunParam(Explicit)
              10..11 @ Pat::Var("b")
             16..17 @ Expr::Var("a")"#]],
    );
    assert_parse_expr(
        "forall(@a: A) -> a",
        expect![[r#"
            0..18 @ Expr::FunType
             7..13 @ FunParam(Implicit)
              8..12 @ Pat::TypeAnnotation
               8..9 @ Pat::Var("a")
               11..12 @ Expr::Var("A")
             17..18 @ Expr::Var("a")"#]],
    );
}

#[test]
fn bool_expr() {
    assert_parse_expr("true", expect!["0..4 @ Expr::Lit(Bool(true))"]);
    assert_parse_expr("false", expect!["0..5 @ Expr::Lit(Bool(false))"]);
}

#[test]
fn int_expr() {
    assert_parse_expr("1234", expect![[r#"0..4 @ Expr::Lit(Int("1234"))"#]]);
    assert_parse_expr("0x1234", expect![[r#"0..6 @ Expr::Lit(Int("0x1234"))"#]]);
    assert_parse_expr("0x1010", expect![[r#"0..6 @ Expr::Lit(Int("0x1010"))"#]]);
}

#[test]
fn char_expr() { assert_parse_expr("'a'", expect![[r#"0..3 @ Expr::Lit(Char("'a'"))"#]]); }

#[test]
fn string_expr() { assert_parse_expr(r#""a""#, expect![[r#"0..3 @ Expr::Lit(String("\"a\""))"#]]); }

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
               13..14 @ Expr::Lit(Int("5"))"#]],
    );
    assert_parse_expr(
        "do { let x = 5; x }",
        expect![[r#"
            0..19 @ Expr::Do
             Stmt::Let
              5..15 @ LetBinding
               9..10 @ Pat::Var("x")
               13..14 @ Expr::Lit(Int("5"))
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
fn if_expr() {
    assert_parse_expr(
        "if true then 1 else 0",
        expect![[r#"
            0..21 @ Expr::If
             3..7 @ Expr::Lit(Bool(true))
             13..14 @ Expr::Lit(Int("1"))
             20..21 @ Expr::Lit(Int("0"))"#]],
    );
    assert_parse_expr(
        "if if true then 1 else 0 then 'a' else 'b'",
        expect![[r#"
            0..42 @ Expr::If
             3..29 @ Expr::If
              6..10 @ Expr::Lit(Bool(true))
              16..17 @ Expr::Lit(Int("1"))
              23..24 @ Expr::Lit(Int("0"))
             30..33 @ Expr::Lit(Char("'a'"))
             39..42 @ Expr::Lit(Char("'b'"))"#]],
    );
    assert_parse_expr(
        "if true then if false then 1 else 0 else 'a'",
        expect![[r#"
            0..44 @ Expr::If
             3..7 @ Expr::Lit(Bool(true))
             13..40 @ Expr::If
              16..21 @ Expr::Lit(Bool(false))
              27..28 @ Expr::Lit(Int("1"))
              34..35 @ Expr::Lit(Int("0"))
             41..44 @ Expr::Lit(Char("'a'"))"#]],
    );
    assert_parse_expr(
        "if true then 'a' else if false then 1 else 0",
        expect![[r#"
            0..44 @ Expr::If
             3..7 @ Expr::Lit(Bool(true))
             13..16 @ Expr::Lit(Char("'a'"))
             22..44 @ Expr::If
              25..30 @ Expr::Lit(Bool(false))
              36..37 @ Expr::Lit(Int("1"))
              43..44 @ Expr::Lit(Int("0"))"#]],
    );
}

#[test]
fn match_expr() {
    assert_parse_expr(
        "match x {}",
        expect![[r#"
    0..10 @ Expr::Match
     6..7 @ Expr::Var("x")"#]],
    );

    assert_parse_expr(
        "match x {y => false,}",
        expect![[r#"
            0..21 @ Expr::Match
             6..7 @ Expr::Var("x")
             9..20 @ MatchCase
              9..10 @ Pat::Var("y")
              14..19 @ Expr::Lit(Bool(false))"#]],
    );
    assert_parse_expr(
        "match x {y => false,z => true,}",
        expect![[r#"
            0..31 @ Expr::Match
             6..7 @ Expr::Var("x")
             9..20 @ MatchCase
              9..10 @ Pat::Var("y")
              14..19 @ Expr::Lit(Bool(false))
             20..30 @ MatchCase
              20..21 @ Pat::Var("z")
              25..29 @ Expr::Lit(Bool(true))"#]],
    );
}

#[test]
fn record_expr() {
    assert_parse_expr("{}", expect!["0..2 @ Expr::Unit"]);
    assert_parse_expr(
        "{x=1}",
        expect![[r#"
            0..5 @ Expr::RecordLit
             RecordTypeField
              Located(1..2, "x")
              3..4 @ Expr::Lit(Int("1"))"#]],
    );
    assert_parse_expr(
        "{x=1,}",
        expect![[r#"
            0..6 @ Expr::RecordLit
             RecordTypeField
              Located(1..2, "x")
              3..4 @ Expr::Lit(Int("1"))"#]],
    );
    assert_parse_expr(
        "{x=1,y=2}",
        expect![[r#"
            0..9 @ Expr::RecordLit
             RecordTypeField
              Located(1..2, "x")
              3..4 @ Expr::Lit(Int("1"))
             RecordTypeField
              Located(5..6, "y")
              7..8 @ Expr::Lit(Int("2"))"#]],
    );

    assert_parse_expr(
        "{x:1}",
        expect![[r#"
            0..5 @ Expr::RecordType
             RecordTypeField
              Located(1..2, "x")
              3..4 @ Expr::Lit(Int("1"))"#]],
    );
    assert_parse_expr(
        "{x:1,}",
        expect![[r#"
            0..6 @ Expr::RecordType
             RecordTypeField
              Located(1..2, "x")
              3..4 @ Expr::Lit(Int("1"))"#]],
    );
    assert_parse_expr(
        "{x:1,y:2}",
        expect![[r#"
            0..9 @ Expr::RecordType
             RecordTypeField
              Located(1..2, "x")
              3..4 @ Expr::Lit(Int("1"))
             RecordTypeField
              Located(5..6, "y")
              7..8 @ Expr::Lit(Int("2"))"#]],
    );
}

#[test]
fn record_proj_expr() {
    assert_parse_expr(
        "a.b",
        expect![[r#"
    0..3 @ Expr::RecordProj
     0..1 @ Expr::Var("a")
     Located(2..3, "b")"#]],
    );
    assert_parse_expr(
        "a.b.c",
        expect![[r#"
            0..5 @ Expr::RecordProj
             0..3 @ Expr::RecordProj
              0..1 @ Expr::Var("a")
              Located(2..3, "b")
             Located(4..5, "c")"#]],
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
               12..13 @ Expr::Lit(Int("1"))"#]],
    );
    assert_parse_expr(
        "do { #eval 1; }",
        expect![[r#"
            0..15 @ Expr::Do
             Stmt::Command
              Stmt::Eval
               11..12 @ Expr::Lit(Int("1"))"#]],
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
               8..9 @ Expr::Lit(Int("5"))"#]],
    );
    assert_parse_file(
        "10;",
        expect![[r#"
            File
             Stmt::Expr
              0..2 @ Expr::Lit(Int("10"))"#]],
    );
    assert_parse_file(
        "#check 10; 45;",
        expect![[r#"
            File
             Stmt::Command
              Stmt::Check
               7..9 @ Expr::Lit(Int("10"))
             Stmt::Expr
              11..13 @ Expr::Lit(Int("45"))"#]],
    );
}
