//! See `context-free-syntax.md`

#![feature(allocator_api)]

use codespan_reporting::diagnostic::{Diagnostic, Label};
pub use pion_lexer::lex;
use pion_lexer::{LiteralKind, ReservedIdent, Token, TokenKind};
use pion_surface::syntax::*;
use text_size::TextRange;

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

type Binop<'text, 'surface> = fn(
    Located<&'surface Expr<'text, 'surface>>,
    Located<&'surface Expr<'text, 'surface>>,
) -> Expr<'text, 'surface>;

fn infix_binding_power<'text, 'surface>(
    token: TokenKind,
) -> Option<(u8, u8, Binop<'text, 'surface>)> {
    match token {
        TokenKind::SingleArrow => Some((3, 2, |domain, codomain| Expr::FunArrow(domain, codomain))),
        TokenKind::Punct(':') => Some((1, 2, |expr, r#type| Expr::TypeAnnotation(expr, r#type))),
        _ => None,
    }
}

fn postfix_binding_power(token: TokenKind) -> Option<u8> {
    match token {
        TokenKind::LParen => Some(11),
        _ => None,
    }
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

    fn atom_pat(&mut self) -> Located<Pat<'text, 'surface>> {
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

    fn pat(&mut self) -> Located<Pat<'text, 'surface>> {
        let mut pat = self.atom_pat();

        loop {
            match self.peek_token() {
                Some(token) if token.kind == TokenKind::Punct(':') => {
                    self.next_token();
                    let r#type = self.expr_bp(2);
                    pat = Located::new(
                        TextRange::new(pat.range.start(), r#type.range.end()),
                        Pat::TypeAnnotation {
                            pat: pat.map(|pat| &*self.bump.alloc(pat)),
                            r#type: r#type.map(|ty| &*self.bump.alloc(ty)),
                        },
                    );
                }
                _ => break,
            }
        }

        pat
    }

    fn expr(&mut self) -> Located<Expr<'text, 'surface>> { self.expr_bp(0) }

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
            TokenKind::Reserved(ReservedIdent::False) => {
                Located::new(token.range, Expr::Bool(false))
            }
            TokenKind::Reserved(ReservedIdent::True) => Located::new(token.range, Expr::Bool(true)),
            TokenKind::Literal(LiteralKind::Number) => {
                Located::new(token.range, Expr::Number(token.text))
            }
            TokenKind::Literal(LiteralKind::Char) => {
                Located::new(token.range, Expr::Char(token.text))
            }
            TokenKind::Literal(LiteralKind::String) => {
                Located::new(token.range, Expr::String(token.text))
            }
            TokenKind::Ident => Located::new(token.range, Expr::Var(token.text)),
            TokenKind::Reserved(ReservedIdent::Do) => self.do_expr(),
            TokenKind::Reserved(ReservedIdent::Forall) => self.forall_expr(),
            TokenKind::Reserved(ReservedIdent::Fun) => self.fun_expr(),
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

    fn expr_bp(&mut self, min_bp: u8) -> Located<Expr<'text, 'surface>> {
        let mut expr = self.atom_expr();

        loop {
            let Some(token) = self.peek_token() else {
                break;
            };

            if let Some(l_bp) = postfix_binding_power(token.kind) {
                if l_bp < min_bp {
                    break;
                }

                self.next_token();
                expr = match token.kind {
                    TokenKind::LParen => {
                        self.fun_call_expr(expr.map(|expr| &*self.bump.alloc(expr)))
                    }
                    _ => unreachable!(),
                };

                continue;
            }

            match infix_binding_power(token.kind) {
                Some((l_bp, r_bp, op)) => {
                    if l_bp < min_bp {
                        break;
                    }

                    self.next_token();
                    let rhs = self.expr_bp(r_bp);
                    let lhs = expr.map(|expr| &*self.bump.alloc(expr));
                    let rhs = rhs.map(|expr| &*self.bump.alloc(expr));

                    expr = Located::new(
                        TextRange::new(lhs.range.start(), rhs.range.end()),
                        op(lhs, rhs),
                    );
                    continue;
                }
                None => break,
            }
        }

        expr
    }

    fn let_binding(&mut self) -> Located<LetBinding<'text, 'surface>> {
        let start_range = self.range;
        let pat = self.pat();
        self.expect_token(TokenKind::Punct('='));
        let expr = self.expr();
        self.expect_token(TokenKind::Punct(';'));
        let end_range = self.range;
        Located::new(
            TextRange::new(start_range.start(), end_range.end()),
            LetBinding { pat, init: expr },
        )
    }

    fn file(&mut self) -> File<'text, 'surface> {
        let mut stmts = Vec::new_in(self.bump);

        while let Some(token) = self.peek_token() {
            match token.kind {
                TokenKind::Reserved(ReservedIdent::Let) => {
                    self.next_token();
                    let binding = self.let_binding();
                    stmts.push(Stmt::Let(binding));
                }
                TokenKind::Punct('#') => {
                    self.next_token();
                    match self.peek_token() {
                        None => {
                            self.diagnostic(
                                token.range,
                                Diagnostic::error()
                                    .with_message(
                                        "Syntax error: expected name of command after `#`",
                                    )
                                    .with_notes(vec![String::from(
                                        "Help: supported commands are `check` or `eval`",
                                    )]),
                            );
                        }
                        Some(token) => match token.kind {
                            TokenKind::Ident if token.text == "check" => {
                                self.next_token();
                                let expr = self.expr();
                                self.expect_token(TokenKind::Punct(';'));
                                stmts.push(Stmt::Command(Command::Check(
                                    expr.map(|expr| &*self.bump.alloc(expr)),
                                )));
                            }
                            TokenKind::Ident if token.text == "eval" => {
                                self.next_token();
                                let expr = self.expr();
                                self.expect_token(TokenKind::Punct(';'));
                                stmts.push(Stmt::Command(Command::Eval(
                                    expr.map(|expr| &*self.bump.alloc(expr)),
                                )));
                            }
                            _ => {
                                self.diagnostic(
                                    token.range,
                                    Diagnostic::error()
                                        .with_message(
                                            "Syntax error: expected name of command after `#`",
                                        )
                                        .with_notes(vec![String::from(
                                            "Help: supported commands are `check` or `eval`",
                                        )]),
                                );
                                self.next_token();
                                continue;
                            }
                        },
                    }
                }
                _ => {
                    let expr = self.expr();
                    match self.peek_token() {
                        Some(token) if token.kind == TokenKind::Punct(';') => {
                            self.next_token();
                            stmts.push(Stmt::Expr(expr.map(|expr| &*self.bump.alloc(expr))));
                        }
                        _ => continue,
                    }
                }
            }
        }

        let stmts = stmts.leak();
        File { stmts }
    }

    fn do_expr(&mut self) -> Located<Expr<'text, 'surface>> {
        let start_range = self.range;
        self.expect_token(TokenKind::LCurly);

        let mut stmts = Vec::new_in(self.bump);
        let mut tail_expr = None;

        while let Some(token) = self.peek_token() {
            if token.kind == TokenKind::RCurly {
                break;
            }
            tail_expr = None;

            match token.kind {
                TokenKind::Reserved(ReservedIdent::Let) => {
                    self.next_token();
                    let binding = self.let_binding();
                    stmts.push(Stmt::Let(binding));
                }
                TokenKind::Punct('#') => {
                    self.next_token();
                    match self.peek_token() {
                        None => {
                            self.diagnostic(
                                token.range,
                                Diagnostic::error()
                                    .with_message(
                                        "Syntax error: expected name of command after `#`",
                                    )
                                    .with_notes(vec![String::from(
                                        "Help: supported commands are `check` or `eval`",
                                    )]),
                            );
                        }
                        Some(token) => match token.kind {
                            TokenKind::Ident if token.text == "check" => {
                                self.next_token();
                                let expr = self.expr();
                                self.expect_token(TokenKind::Punct(';'));
                                stmts.push(Stmt::Command(Command::Check(
                                    expr.map(|expr| &*self.bump.alloc(expr)),
                                )));
                            }
                            TokenKind::Ident if token.text == "eval" => {
                                self.next_token();
                                let expr = self.expr();
                                self.expect_token(TokenKind::Punct(';'));
                                stmts.push(Stmt::Command(Command::Eval(
                                    expr.map(|expr| &*self.bump.alloc(expr)),
                                )));
                            }
                            _ => {
                                self.diagnostic(
                                    token.range,
                                    Diagnostic::error()
                                        .with_message(
                                            "Syntax error: expected name of command after `#`",
                                        )
                                        .with_notes(vec![String::from(
                                            "Help: supported commands are `check` or `eval`",
                                        )]),
                                );
                                self.next_token();
                                continue;
                            }
                        },
                    }
                }
                _ => {
                    let expr = self.expr();
                    match self.peek_token() {
                        Some(token) if token.kind == TokenKind::Punct(';') => {
                            self.next_token();
                            stmts.push(Stmt::Expr(expr.map(|expr| &*self.bump.alloc(expr))));
                        }
                        _ => tail_expr = Some(expr),
                    }
                }
            }
        }

        self.expect_token(TokenKind::RCurly);

        let end_range = self.range;

        Located::new(
            TextRange::new(start_range.start(), end_range.end()),
            Expr::Do(
                stmts.leak(),
                tail_expr.map(|loc| loc.map(|expr| &*self.bump.alloc(expr))),
            ),
        )
    }

    fn forall_expr(&mut self) -> Located<Expr<'text, 'surface>> {
        let start_range = self.range;
        self.expect_token(TokenKind::LParen);
        let params = self.fun_params();
        self.expect_token(TokenKind::RParen);
        self.expect_token(TokenKind::SingleArrow);
        let body = self.expr();
        let end_range = self.range;
        Located::new(
            TextRange::new(start_range.start(), end_range.end()),
            Expr::FunType(params, body.map(|expr| &*self.bump.alloc(expr))),
        )
    }

    fn fun_expr(&mut self) -> Located<Expr<'text, 'surface>> {
        let start_range = self.range;
        self.expect_token(TokenKind::LParen);
        let params = self.fun_params();
        self.expect_token(TokenKind::RParen);
        self.expect_token(TokenKind::DoubleArrow);
        let body = self.expr();
        let end_range = self.range;
        Located::new(
            TextRange::new(start_range.start(), end_range.end()),
            Expr::FunExpr(params, body.map(|expr| &*self.bump.alloc(expr))),
        )
    }

    fn fun_call_expr(
        &mut self,
        callee: Located<&'surface Expr<'text, 'surface>>,
    ) -> Located<Expr<'text, 'surface>> {
        let start_range = callee.range;
        let args = self.fun_args();
        let end_range = self.range;
        Located::new(
            TextRange::new(start_range.start(), end_range.end()),
            Expr::FunCall(callee, args),
        )
    }

    fn fun_args(&mut self) -> &'surface [Located<FunArg<'text, 'surface>>] {
        let mut args = Vec::new_in(self.bump);
        while let Some(token) = self.peek_token() {
            if token.kind == TokenKind::RParen {
                self.next_token();
                break;
            }

            let start_range = self.range;
            let expr = self.expr();
            let end_range = self.range;
            args.push(Located::new(
                TextRange::new(start_range.start(), end_range.end()),
                FunArg { expr },
            ));

            if let Some(token) = self.peek_token() {
                if token.kind == TokenKind::Punct(',') {
                    self.next_token();
                    continue;
                }
            }
        }

        args.leak()
    }

    fn fun_params(&mut self) -> &'surface [Located<FunParam<'text, 'surface>>] {
        let mut params = Vec::new_in(self.bump);
        while let Some(token) = self.peek_token() {
            if token.kind == TokenKind::RParen {
                break;
            }

            let start_range = self.range;
            let pat = self.pat();
            let end_range = self.range;
            params.push(Located::new(
                TextRange::new(start_range.start(), end_range.end()),
                FunParam { pat },
            ));

            if let Some(token) = self.peek_token() {
                if token.kind == TokenKind::Punct(',') {
                    self.next_token();
                    continue;
                }
            }
        }

        params.leak()
    }
}

pub fn parse_file<'text, 'surface>(
    file: usize,
    tokens: impl Clone + Iterator<Item = Token<'text>>,
    bump: &'surface bumpalo::Bump,
) -> (File<'text, 'surface>, Vec<Diagnostic<usize>>) {
    let mut parser = Parser::new(file, tokens, bump);
    let expr = parser.file();
    let diagnostics = parser.finish();
    (expr, diagnostics)
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
    fn assert_parse_pat(text: &str, expected: Expect) {
        let tokens = lex(text);
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
        let tokens = lex(text);
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
        let tokens = lex(text);
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
}
