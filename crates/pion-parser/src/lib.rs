//! ```text
//! <Expr> ::=
//!     | Ident
//!     | Literal
//!     | ( <Expr> )
//!     | <Expr> ( <FunArg>,* )
//!     | fun ( <FunParam>,* ) <Expr>
//!     | forall ( <FunParam>,* ) <Expr>
//!     | <Expr> -> <Expr>
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
use pion_lexer::{Token, TokenKind};
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
    FunCall,
    FunExpr,
    FunType,
    FunArrow,
    Let,
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
    pub expr: Expr<'text, 'surface>,
    pub r#type: Option<Expr<'text, 'surface>>,
}

#[derive(Debug, Copy, Clone)]
pub struct FunParam<'text, 'surface> {
    pub expr: Expr<'text, 'surface>,
    pub r#type: Option<Expr<'text, 'surface>>,
}

pub struct Parser<'text, 'surface, Tokens>
where
    Tokens: Iterator<Item = Token<'text>>,
{
    tokens: Tokens,
    bump: &'surface bumpalo::Bump,
    diagnostics: Vec<Diagnostic<usize>>,
    file: usize,
    range: TextRange,
}

impl<'text, 'surface, Tokens> Parser<'text, 'surface, Tokens>
where
    Tokens: Iterator<Item = Token<'text>>,
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

    pub fn expr(&mut self) -> Located<Expr<'text, 'surface>> { self.atom_expr() }

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
                        "Syntax error: unexpected {got} while parsing pattern"
                    )),
                );
                Located::new(token.range, Expr::Error)
            }
        }
    }
}

pub fn parse_expr<'text, 'surface>(
    file: usize,
    tokens: impl Iterator<Item = Token<'text>>,
    bump: &'surface bumpalo::Bump,
) -> (Located<Expr<'text, 'surface>>, Vec<Diagnostic<usize>>) {
    let mut parser = Parser::new(file, tokens, bump);
    let expr = parser.expr();
    let diagnostics = parser.finish();
    (expr, diagnostics)
}

pub fn parse_pat<'text, 'surface>(
    file: usize,
    tokens: impl Iterator<Item = Token<'text>>,
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
        let mut tokens = pion_lexer::lex(text);
        let bump = bumpalo::Bump::new();
        let (pat, diagnostics) = parse_pat(0, &mut tokens, &bump);

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
        let mut tokens = pion_lexer::lex(text);
        let bump = bumpalo::Bump::new();
        let (expr, diagnostics) = parse_expr(0, &mut tokens, &bump);

        let mut got = String::new();
        write!(got, "{expr:?}").unwrap();
        for diagnostic in diagnostics {
            writeln!(got, "{diagnostic:?}").unwrap();
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
}
