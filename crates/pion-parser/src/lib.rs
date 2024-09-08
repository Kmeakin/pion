#![feature(allocator_api)]

//! ```text
//! <Expr> ::=
//!     | Ident
//!     | Literal
//!     | ( <Expr> )
//!     | <Expr> ( <FunArg>,* )
//!     | <Expr> -> <Expr>
//!     | forall ( <FunParam>,* ) <Expr>
//!     | fun ( <FunParam>,* ) <Expr>
//!     | let <Pat> (: <Expr>)? = <Expr> ; <Expr>
//!
//! <Pat> ::=
//!     | _
//!     | Ident
//!     | ( <Pat> )
//!
//! <FunArg> ::= <Expr>
//! <FunParam> ::= <Pat> (: <Expr>)?
//! ```

use core::fmt;

use codespan_reporting::diagnostic::{Diagnostic, Label};
use pion_lexer::{ReservedIdent, Token, TokenKind};
use text_size::TextRange;

#[derive(Copy, Clone)]
pub struct Located<T> {
    pub range: TextRange,
    pub data: T,
}

impl<T: fmt::Debug> fmt::Debug for Located<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Located")
            .field(&self.range)
            .field(&self.data)
            .finish()
    }
}

impl<T> Located<T> {
    pub fn new(range: TextRange, data: T) -> Self { Self { range, data } }

    pub fn map<V>(self, f: impl FnOnce(T) -> V) -> Located<V> {
        Located::new(self.range, f(self.data))
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Expr<'text, 'surface> {
    Error,
    Var(&'text str),
    Literal,
    Paren(Located<&'surface Self>),
    FunCall {
        callee: Located<&'surface Self>,
        args: &'surface [FunArg<'text, 'surface>],
    },
    FunExpr {
        params: &'surface [FunParam<'text, 'surface>],
        body: Located<&'surface Self>,
    },
    FunType {
        params: &'surface [FunParam<'text, 'surface>],
        body: Located<&'surface Self>,
    },
    FunArrow {
        domain: Located<&'surface Self>,
        codomain: Located<&'surface Self>,
    },
    Let {
        binding: &'surface LetBinding<'text, 'surface>,
        body: Located<&'surface Self>,
    },
}

#[derive(Debug, Copy, Clone)]
pub struct LetBinding<'text, 'surface> {
    pub pat: Located<Pat<'text, 'surface>>,
    pub r#type: Option<Located<Expr<'text, 'surface>>>,
    pub expr: Located<Expr<'text, 'surface>>,
}

#[derive(Debug, Copy, Clone)]
pub enum Pat<'text, 'surface> {
    Error,
    Underscore,
    Var(&'text str),
    Paren(Located<&'surface Self>),
}

#[derive(Debug, Copy, Clone)]
pub enum Literal {
    Int,
    String,
    Char,
}

#[derive(Debug, Copy, Clone)]
pub struct FunArg<'text, 'surface> {
    pub expr: Located<Expr<'text, 'surface>>,
}

#[derive(Debug, Copy, Clone)]
pub struct FunParam<'text, 'surface> {
    pub expr: Located<Expr<'text, 'surface>>,
    pub r#type: Option<Located<Expr<'text, 'surface>>>,
}

pub struct Parser<'text, 'surface, Tokens>
where
    Tokens: Clone + Iterator<Item = Token<'text>>,
{
    tokens: Tokens,
    bump: &'surface bumpalo::Bump,
    diagnostics: Vec<Diagnostic<usize>>,
    file: usize,
    range: TextRange,
}

impl<'text, 'surface, Tokens> Parser<'text, 'surface, Tokens>
where
    Tokens: Clone + Iterator<Item = Token<'text>>,
{
    pub fn new(file: usize, tokens: Tokens, bump: &'surface bumpalo::Bump) -> Self {
        Self {
            tokens,
            bump,
            diagnostics: Vec::new(),
            file,
            range: TextRange::default(),
        }
    }

    pub fn finish(self) -> Vec<Diagnostic<usize>> { self.diagnostics }

    fn diagnostic(&mut self, range: TextRange, diag: Diagnostic<usize>) {
        self.diagnostics
            .push(diag.with_labels(vec![Label::primary(self.file, range)]));
    }

    fn next_token(&mut self) -> Option<Token<'text>> {
        loop {
            match self.tokens.next() {
                None => return None,
                Some(token) if token.kind.is_trivia() => continue,
                Some(token) => {
                    self.range = token.range;
                    return Some(token);
                }
            }
        }
    }

    fn peek_token(&mut self) -> Option<Token<'text>> {
        loop {
            let mut tokens = self.tokens.clone();
            match tokens.next() {
                None => {
                    self.tokens = tokens;
                    return None;
                }
                Some(token) if token.kind.is_trivia() => {
                    self.tokens = tokens;
                    continue;
                }
                Some(token) => {
                    self.range = token.range;
                    return Some(token);
                }
            }
        }
    }

    fn expect_token(&mut self, expected: TokenKind) {
        match self.next_token() {
            Some(token) if token.kind == expected => {}
            Some(token) => {
                let got = token.kind;
                self.diagnostic(
                    token.range,
                    Diagnostic::error().with_message(format!(
                        "Syntax error: unexpected {got}, expected {expected}"
                    )),
                );
            }
            None => self.diagnostic(
                self.range,
                Diagnostic::error().with_message(format!(
                    "Syntax error: unexpected end of file, expected {expected}"
                )),
            ),
        }
    }

    pub fn pat(&mut self) -> Located<Pat<'text, 'surface>> {
        let Some(token) = self.next_token() else {
            self.diagnostic(
                self.range,
                Diagnostic::error()
                    .with_message("Syntax error: unexpected end of file while parsing pattern"),
            );
            return Located::new(self.range, Pat::Error);
        };

        match token.kind {
            TokenKind::Punct('_') => Located::new(token.range, Pat::Underscore),
            TokenKind::Ident => Located::new(token.range, Pat::Var(token.text)),
            TokenKind::LParen => {
                let start_range = token.range;
                let pat = self.pat();
                let pat = pat.map(|pat| &*self.bump.alloc(pat));
                self.expect_token(TokenKind::RParen);
                let end_range = self.range;
                Located::new(
                    TextRange::new(start_range.start(), end_range.end()),
                    Pat::Paren(pat),
                )
            }
            got => {
                self.diagnostic(
                    token.range,
                    Diagnostic::error().with_message(format!(
                        "Syntax error: unexpected {got} while parsing pattern"
                    )),
                );
                Located::new(token.range, Pat::Error)
            }
        }
    }

    pub fn expr(&mut self) -> Located<Expr<'text, 'surface>> {
        let Some(token) = self.peek_token() else {
            self.diagnostic(
                self.range,
                Diagnostic::error()
                    .with_message("Syntax error: unexpected end of file while parsing expression"),
            );
            return Located::new(self.range, Expr::Error);
        };

        match token.kind {
            TokenKind::Reserved(ReservedIdent::Forall) => {
                self.next_token();
                self.expect_token(TokenKind::LParen);
                let params = self.fun_params();
                self.expect_token(TokenKind::RParen);
                let body = self.expr();
                let end_range = self.range;
                Located::new(
                    TextRange::new(token.range.start(), end_range.end()),
                    Expr::FunType {
                        params,
                        body: body.map(|expr| &*self.bump.alloc(expr)),
                    },
                )
            }
            TokenKind::Reserved(ReservedIdent::Fun) => {
                self.next_token();
                self.expect_token(TokenKind::LParen);
                let params = self.fun_params();
                self.expect_token(TokenKind::RParen);
                let body = self.expr();
                let end_range = self.range;
                Located::new(
                    TextRange::new(token.range.start(), end_range.end()),
                    Expr::FunType {
                        params,
                        body: body.map(|expr| &*self.bump.alloc(expr)),
                    },
                )
            }
            TokenKind::Reserved(ReservedIdent::Let) => self.let_expr(),
            _ => {
                let mut expr = self.atom_expr();

                while let Some(token) = self.peek_token() {
                    match token.kind {
                        TokenKind::LParen => {
                            let start_range = expr.range;
                            self.next_token();
                            let args = self.fun_args();
                            self.expect_token(TokenKind::RParen);
                            let end_range = self.range;
                            expr = Located::new(
                                TextRange::new(start_range.start(), end_range.end()),
                                Expr::FunCall {
                                    callee: expr.map(|expr| &*self.bump.alloc(expr)),
                                    args,
                                },
                            );
                        }
                        _ => break,
                    }
                }

                while let Some(token) = self.peek_token() {
                    match token.kind {
                        TokenKind::Arrow => {
                            let start_range = expr.range;
                            self.next_token();
                            let codomain = self.expr();
                            let end_range = self.range;
                            expr = Located::new(
                                TextRange::new(start_range.start(), end_range.end()),
                                Expr::FunArrow {
                                    domain: expr.map(|expr| &*self.bump.alloc(expr)),
                                    codomain: codomain.map(|expr| &*self.bump.alloc(expr)),
                                },
                            );
                        }
                        _ => break,
                    }
                }

                expr
            }
        }
    }

    fn let_expr(&mut self) -> Located<Expr<'text, 'surface>> {
        let start_range = self.range;
        self.expect_token(TokenKind::Reserved(ReservedIdent::Let));

        let pat = self.pat();
        let r#type = self.type_annotation_opt();

        self.expect_token(TokenKind::Punct('='));
        let expr = self.expr();

        self.expect_token(TokenKind::Punct(';'));
        let body = self.expr();
        let end_range = self.range;

        let binding = LetBinding { pat, r#type, expr };
        let binding = self.bump.alloc(binding);

        Located::new(
            TextRange::new(start_range.start(), end_range.end()),
            Expr::Let {
                binding: self.bump.alloc(binding),
                body: body.map(|expr| &*self.bump.alloc(expr)),
            },
        )
    }

    fn atom_expr(&mut self) -> Located<Expr<'text, 'surface>> {
        let Some(token) = self.next_token() else {
            self.diagnostic(
                self.range,
                Diagnostic::error()
                    .with_message("Syntax error: unexpected end of file while parsing expression"),
            );
            return Located::new(self.range, Expr::Error);
        };

        match token.kind {
            TokenKind::LParen => {
                let start_range = token.range;
                let expr = self.expr();
                let expr = expr.map(|pat| &*self.bump.alloc(pat));
                self.expect_token(TokenKind::RParen);
                let end_range = self.range;
                Located::new(
                    TextRange::new(start_range.start(), end_range.end()),
                    Expr::Paren(expr),
                )
            }
            TokenKind::Ident => Located::new(token.range, Expr::Var(token.text)),
            got => {
                self.diagnostic(
                    token.range,
                    Diagnostic::error().with_message(format!(
                        "Syntax error: unexpected {got} while parsing expression"
                    )),
                );
                Located::new(token.range, Expr::Error)
            }
        }
    }

    fn fun_args(&mut self) -> &'surface [FunArg<'text, 'surface>] {
        let mut args = Vec::new_in(self.bump);
        while let Some(token) = self.peek_token() {
            if token.kind == TokenKind::RParen {
                break;
            }

            let expr = self.expr();
            args.push(FunArg { expr });

            if let Some(token) = self.peek_token() {
                if token.kind == TokenKind::Punct(',') {
                    self.next_token();
                    continue;
                }
            }
        }

        args.leak()
    }

    fn fun_params(&mut self) -> &'surface [FunParam<'text, 'surface>] {
        let mut params = Vec::new_in(self.bump);
        while let Some(token) = self.peek_token() {
            if token.kind == TokenKind::RParen {
                break;
            }

            let expr = self.expr();
            let r#type = self.type_annotation_opt();
            params.push(FunParam { expr, r#type });

            if let Some(token) = self.peek_token() {
                if token.kind == TokenKind::Punct(',') {
                    self.next_token();
                    continue;
                }
            }
        }

        params.leak()
    }

    fn type_annotation_opt(&mut self) -> Option<Located<Expr<'text, 'surface>>> {
        if let Some(Token {
            kind: TokenKind::Punct(':'),
            ..
        }) = self.peek_token()
        {
            self.next_token();
            Some(self.expr())
        } else {
            None
        }
    }
}

pub fn parse_expr<'text, 'surface>(
    file: usize,
    tokens: impl Clone + Iterator<Item = Token<'text>>,
    bump: &'surface bumpalo::Bump,
) -> (Located<Expr<'text, 'surface>>, Vec<Diagnostic<usize>>) {
    let mut parser = Parser::new(file, tokens, bump);
    let expr = parser.expr();
    let diagnostics = parser.finish();
    (expr, diagnostics)
}

pub fn parse_pat<'text, 'surface>(
    file: usize,
    tokens: impl Clone + Iterator<Item = Token<'text>>,
    bump: &'surface bumpalo::Bump,
) -> (Located<Pat<'text, 'surface>>, Vec<Diagnostic<usize>>) {
    let mut parser = Parser::new(file, tokens, bump);
    let pat = parser.pat();
    let diagnostics = parser.finish();
    (pat, diagnostics)
}

#[cfg(test)]
mod tests {
    use std::fmt::Write;

    use expect_test::{expect, Expect};

    use super::*;

    #[track_caller]
    #[allow(clippy::needless_pass_by_value, reason = "It's just a test")]
    fn check_pat(text: &str, expected: Expect) {
        let tokens = pion_lexer::lex(text);
        let bump = bumpalo::Bump::new();
        let (pat, diagnostics) = parse_pat(0, tokens, &bump);

        let mut got = String::new();
        write!(got, "{pat:?}").unwrap();

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
    fn check_expr(text: &str, expected: Expect) {
        let tokens = pion_lexer::lex(text);
        let bump = bumpalo::Bump::new();
        let (expr, diagnostics) = parse_expr(0, tokens, &bump);

        let mut got = String::new();
        write!(got, "{expr:?}").unwrap();

        if !diagnostics.is_empty() {
            writeln!(got).unwrap();
            for diagnostic in diagnostics {
                writeln!(got, "{diagnostic:?}").unwrap();
            }
        }
        expected.assert_eq(&got);
    }

    #[test]
    fn wildcard_pat() { check_pat("_", expect![[r"Located(0..1, Underscore)"]]); }

    #[test]
    fn var_pat() { check_expr("abc", expect![[r#"Located(0..3, Var("abc"))"#]]); }

    #[test]
    fn paren_pat() {
        check_pat(
            "(_)",
            expect![[r"Located(0..3, Paren(Located(1..2, Underscore)))"]],
        );
    }

    #[test]
    fn var_expr() { check_expr("abc", expect![[r#"Located(0..3, Var("abc"))"#]]); }

    #[test]
    fn paren_expr() {
        check_expr(
            "(abc)",
            expect![[r#"Located(0..5, Paren(Located(1..4, Var("abc"))))"#]],
        );
        check_expr(
            "((abc))",
            expect![[r#"Located(0..7, Paren(Located(1..6, Paren(Located(2..5, Var("abc"))))))"#]],
        );
    }

    #[test]
    fn let_expr() {
        check_expr(
            "let x = y; z",
            expect![[
                r#"Located(0..12, Let { binding: LetBinding { pat: Located(4..5, Var("x")), type: None, expr: Located(8..9, Var("y")) }, body: Located(11..12, Var("z")) })"#
            ]],
        );
        check_expr(
            "let x: T = y; z",
            expect![[
                r#"Located(0..15, Let { binding: LetBinding { pat: Located(4..5, Var("x")), type: Some(Located(7..8, Var("T"))), expr: Located(11..12, Var("y")) }, body: Located(14..15, Var("z")) })"#
            ]],
        );
        check_expr(
            "let x = y; let y = z; w",
            expect![[
                r#"Located(0..23, Let { binding: LetBinding { pat: Located(4..5, Var("x")), type: None, expr: Located(8..9, Var("y")) }, body: Located(11..23, Let { binding: LetBinding { pat: Located(15..16, Var("y")), type: None, expr: Located(19..20, Var("z")) }, body: Located(22..23, Var("w")) }) })"#
            ]],
        );
    }

    #[test]
    fn call_expr() {
        check_expr(
            "f()",
            expect![[r#"Located(0..3, FunCall { callee: Located(0..1, Var("f")), args: [] })"#]],
        );
        check_expr(
            "f(a)",
            expect![[
                r#"Located(0..4, FunCall { callee: Located(0..1, Var("f")), args: [FunArg { expr: Located(2..3, Var("a")) }] })"#
            ]],
        );
        check_expr(
            "f(a,)",
            expect![[
                r#"Located(0..5, FunCall { callee: Located(0..1, Var("f")), args: [FunArg { expr: Located(2..3, Var("a")) }] })"#
            ]],
        );
        check_expr(
            "f(a, b)",
            expect![[
                r#"Located(0..7, FunCall { callee: Located(0..1, Var("f")), args: [FunArg { expr: Located(2..3, Var("a")) }, FunArg { expr: Located(5..6, Var("b")) }] })"#
            ]],
        );
    }

    #[test]
    fn arrow_expr() {
        check_expr(
            "a -> b",
            expect![[
                r#"Located(0..6, FunArrow { domain: Located(0..1, Var("a")), codomain: Located(5..6, Var("b")) })"#
            ]],
        );
        check_expr(
            "a -> b -> c",
            expect![[
                r#"Located(0..11, FunArrow { domain: Located(0..1, Var("a")), codomain: Located(5..11, FunArrow { domain: Located(5..6, Var("b")), codomain: Located(10..11, Var("c")) }) })"#
            ]],
        );
    }

    #[test]
    fn fun_expr() {
        check_expr(
            "fun() a",
            expect![[r#"Located(0..7, FunType { params: [], body: Located(6..7, Var("a")) })"#]],
        );
        check_expr(
            "fun(a) a",
            expect![[
                r#"Located(0..8, FunType { params: [FunParam { expr: Located(4..5, Var("a")), type: None }], body: Located(7..8, Var("a")) })"#
            ]],
        );
        check_expr(
            "fun(a: A) a",
            expect![[
                r#"Located(0..11, FunType { params: [FunParam { expr: Located(4..5, Var("a")), type: Some(Located(7..8, Var("A"))) }], body: Located(10..11, Var("a")) })"#
            ]],
        );
        check_expr(
            "fun(a, b) a",
            expect![[
                r#"Located(0..11, FunType { params: [FunParam { expr: Located(4..5, Var("a")), type: None }, FunParam { expr: Located(7..8, Var("b")), type: None }], body: Located(10..11, Var("a")) })"#
            ]],
        );
    }

    #[test]
    fn forall_expr() {
        check_expr(
            "forall() a",
            expect![[r#"Located(0..10, FunType { params: [], body: Located(9..10, Var("a")) })"#]],
        );
        check_expr(
            "forall(a) a",
            expect![[
                r#"Located(0..11, FunType { params: [FunParam { expr: Located(7..8, Var("a")), type: None }], body: Located(10..11, Var("a")) })"#
            ]],
        );
        check_expr(
            "forall(a: A) a",
            expect![[
                r#"Located(0..14, FunType { params: [FunParam { expr: Located(7..8, Var("a")), type: Some(Located(10..11, Var("A"))) }], body: Located(13..14, Var("a")) })"#
            ]],
        );
        check_expr(
            "forall(a, b) a",
            expect![[
                r#"Located(0..14, FunType { params: [FunParam { expr: Located(7..8, Var("a")), type: None }, FunParam { expr: Located(10..11, Var("b")), type: None }], body: Located(13..14, Var("a")) })"#
            ]],
        );
    }
}
