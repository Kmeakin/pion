use codespan_reporting::diagnostic::Diagnostic;
use text_size::TextRange;

use super::Parser;
use crate::lex::{Token, TokenKind};
use crate::syntax::*;

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

    pub fn pat(&mut self) -> Located<Pat<'text, 'surface>> {
        let mut pat = self.atom_pat();

        loop {
            match self.peek_token() {
                Some(token) if token.kind == TokenKind::Punct(':') => {
                    self.next_token();
                    let r#type = self.expr_bp(2);
                    pat = Located::new(
                        TextRange::new(pat.range.start(), r#type.range.end()),
                        Pat::TypeAnnotation(
                            pat.map(|pat| &*self.bump.alloc(pat)),
                            r#type.map(|ty| &*self.bump.alloc(ty)),
                        ),
                    );
                }
                _ => break,
            }
        }

        pat
    }

    pub fn expr(&mut self) -> Located<Expr<'text, 'surface>> { self.expr_bp(0) }

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
            TokenKind::Punct('_') => Located::new(token.range, Expr::Hole),
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
            TokenKind::KwFalse => Located::new(token.range, Expr::Bool(false)),
            TokenKind::KwTrue => Located::new(token.range, Expr::Bool(true)),
            TokenKind::Int => Located::new(token.range, Expr::Number(token.text)),
            TokenKind::Char => Located::new(token.range, Expr::Char(token.text)),
            TokenKind::String => Located::new(token.range, Expr::String(token.text)),
            TokenKind::Ident => Located::new(token.range, Expr::Var(token.text)),
            TokenKind::KwDo => self.do_expr(),
            TokenKind::KwForall => self.forall_expr(),
            TokenKind::KwFun => self.fun_expr(),
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

    pub fn file(&mut self) -> File<'text, 'surface> {
        let mut stmts = Vec::new_in(self.bump);

        while let Some(token) = self.peek_token() {
            match token.kind {
                TokenKind::KwLet => {
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
                TokenKind::KwLet => {
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
