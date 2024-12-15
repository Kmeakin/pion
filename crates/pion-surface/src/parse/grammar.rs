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
        TokenKind::LParen | TokenKind::Punct('.') => Some(11),
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
            TokenKind::Ident => Located::new(token.range, Pat::Var(token.text())),
            TokenKind::KwFalse => Located::new(token.range, Pat::Lit(Lit::Bool(false))),
            TokenKind::KwTrue => Located::new(token.range, Pat::Lit(Lit::Bool(true))),
            TokenKind::Int => Located::new(token.range, Pat::Lit(Lit::Int(token.text()))),
            TokenKind::Char => Located::new(token.range, Pat::Lit(Lit::Char(token.text()))),
            TokenKind::String => Located::new(token.range, Pat::Lit(Lit::String(token.text()))),
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
            TokenKind::LCurly => self.record_expr(),
            TokenKind::KwFalse => Located::new(token.range, Expr::Lit(Lit::Bool(false))),
            TokenKind::KwTrue => Located::new(token.range, Expr::Lit(Lit::Bool(true))),
            TokenKind::Int => Located::new(token.range, Expr::Lit(Lit::Int(token.text()))),
            TokenKind::Char => Located::new(token.range, Expr::Lit(Lit::Char(token.text()))),
            TokenKind::String => Located::new(token.range, Expr::Lit(Lit::String(token.text()))),
            TokenKind::Ident => Located::new(token.range, Expr::Var(token.text())),
            TokenKind::KwDo => self.do_expr(),
            TokenKind::KwForall => self.forall_expr(),
            TokenKind::KwFun => self.fun_expr(),
            TokenKind::KwIf => self.if_expr(),
            TokenKind::KwMatch => self.match_expr(),
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
                    TokenKind::Punct('.') => {
                        self.record_proj_expr(expr.map(|expr| &*self.bump.alloc(expr)))
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

    fn stmt(&mut self) -> Option<Stmt<'text, 'surface>> {
        let Some(token) = self.peek_token() else {
            unreachable!()
        };
        match token.kind {
            TokenKind::KwLet => {
                self.next_token();
                let binding = self.let_binding();
                Some(Stmt::Let(binding))
            }
            TokenKind::Punct('#') => {
                self.next_token();
                match self.peek_token() {
                    None => {
                        self.diagnostic(
                            token.range,
                            Diagnostic::error()
                                .with_message("Syntax error: expected name of command after `#`")
                                .with_notes(vec![String::from(
                                    "Help: supported commands are `check` or `eval`",
                                )]),
                        );
                        None
                    }
                    Some(token) => match token.kind {
                        TokenKind::Ident if token.text() == "check" => {
                            self.next_token();
                            let expr = self.expr();
                            self.expect_token(TokenKind::Punct(';'));
                            Some(Stmt::Command(Command::Check(
                                expr.map(|expr| &*self.bump.alloc(expr)),
                            )))
                        }
                        TokenKind::Ident if token.text() == "eval" => {
                            self.next_token();
                            let expr = self.expr();
                            self.expect_token(TokenKind::Punct(';'));
                            Some(Stmt::Command(Command::Eval(
                                expr.map(|expr| &*self.bump.alloc(expr)),
                            )))
                        }
                        TokenKind::Ident if token.text() == "show" => {
                            self.next_token();
                            let expr = self.expr();
                            self.expect_token(TokenKind::Punct(';'));
                            Some(Stmt::Command(Command::Show(
                                expr.map(|expr| &*self.bump.alloc(expr)),
                            )))
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
                            None
                        }
                    },
                }
            }
            _ => unreachable!(),
        }
    }

    pub fn file(&mut self) -> File<'text, 'surface> {
        let mut stmts = Vec::new_in(self.bump);

        while let Some(token) = self.peek_token() {
            match token.kind {
                TokenKind::KwLet | TokenKind::Punct('#') => stmts.extend(self.stmt()),
                _ => {
                    let expr = self.expr();
                    self.expect_token(TokenKind::Punct(';'));
                    stmts.push(Stmt::Expr(expr.map(|expr| &*self.bump.alloc(expr))));
                }
            }
        }

        let stmts = stmts.leak();
        File { stmts }
    }

    fn record_expr(&mut self) -> Located<Expr<'text, 'surface>> {
        let start_range = self.range;

        let first_label = match self.next_token() {
            Some(token) if token.kind == TokenKind::RCurly => {
                let end_range = self.range;
                return Located::new(
                    TextRange::new(start_range.start(), end_range.end()),
                    Expr::Unit,
                );
            }
            Some(token) if token.kind == TokenKind::Ident => {
                let text = token.text();
                Located::new(token.range, text)
            }
            _ => {
                self.diagnostic(
                    self.range,
                    Diagnostic::error().with_message(
                        "Syntax error: expected `}` or field name while parsing record",
                    ),
                );
                return Located::new(self.range, Expr::Error);
            }
        };

        match self.next_token() {
            Some(token) if token.kind == TokenKind::Punct('=') => {
                let expr = self.record_lit_expr(first_label);
                let end_range = self.range;
                Located::new(TextRange::new(start_range.start(), end_range.end()), expr)
            }
            Some(token) if token.kind == TokenKind::Punct(':') => {
                let expr = self.record_type_expr(first_label);
                let end_range = self.range;
                Located::new(TextRange::new(start_range.start(), end_range.end()), expr)
            }
            _ => {
                self.diagnostic(
                    self.range,
                    Diagnostic::error().with_message(
                        "Syntax error: expected `=` or `:` while parsing record field",
                    ),
                );
                Located::new(self.range, Expr::Error)
            }
        }
    }

    fn record_lit_expr(&mut self, first_label: Located<&'text str>) -> Expr<'text, 'surface> {
        let mut fields = Vec::new_in(self.bump);
        let expr = self.expr();
        fields.push(RecordLitField::new(first_label, expr));

        loop {
            match self.next_token() {
                Some(token) if token.kind == TokenKind::RCurly => break,
                Some(token) if token.kind == TokenKind::Punct(',') => {}
                _ => {
                    self.diagnostic(
                        self.range,
                        Diagnostic::error().with_message(
                            "Syntax error: expected ',' or '}' while parsing record literal",
                        ),
                    );
                    break;
                }
            }

            let label = match self.next_token() {
                Some(token) if token.kind == TokenKind::RCurly => break,
                Some(token) if token.kind == TokenKind::Ident => {
                    let text = token.text();
                    Located::new(token.range, text)
                }
                _ => {
                    self.diagnostic(
                        self.range,
                        Diagnostic::error().with_message(
                            "Syntax error: expected field name while parsing record literal",
                        ),
                    );
                    break;
                }
            };

            self.expect_token(TokenKind::Punct('='));
            let expr = self.expr();
            fields.push(RecordLitField::new(label, expr));
        }

        Expr::RecordLit(fields.leak())
    }

    fn record_type_expr(&mut self, first_label: Located<&'text str>) -> Expr<'text, 'surface> {
        let mut fields = Vec::new_in(self.bump);
        let expr = self.expr();
        fields.push(RecordTypeField::new(first_label, expr));

        loop {
            match self.next_token() {
                Some(token) if token.kind == TokenKind::RCurly => break,
                Some(token) if token.kind == TokenKind::Punct(',') => {}
                _ => {
                    self.diagnostic(
                        self.range,
                        Diagnostic::error().with_message(
                            "Syntax error: expected ',' or '}' while parsing record type",
                        ),
                    );
                    break;
                }
            }

            let label = match self.next_token() {
                Some(token) if token.kind == TokenKind::RCurly => break,
                Some(token) if token.kind == TokenKind::Ident => {
                    let text = token.text();
                    Located::new(token.range, text)
                }
                _ => {
                    self.diagnostic(
                        self.range,
                        Diagnostic::error().with_message(
                            "Syntax error: expected field name while parsing record type",
                        ),
                    );
                    break;
                }
            };

            self.expect_token(TokenKind::Punct(':'));
            let expr = self.expr();
            fields.push(RecordTypeField::new(label, expr));
        }

        Expr::RecordType(fields.leak())
    }

    fn do_expr(&mut self) -> Located<Expr<'text, 'surface>> {
        let start_range = self.range;
        self.expect_token(TokenKind::LCurly);

        let mut stmts = Vec::new_in(self.bump);
        let mut tail_expr = None;

        while let Some(token) = self.peek_token() {
            match token.kind {
                TokenKind::RCurly => break,
                TokenKind::KwLet | TokenKind::Punct('#') => stmts.extend(self.stmt()),
                _ => {
                    let expr = self.expr();
                    match self.peek_token() {
                        Some(token) if token.kind == TokenKind::Punct(';') => {
                            self.next_token();
                            stmts.push(Stmt::Expr(expr.map(|expr| &*self.bump.alloc(expr))));
                        }
                        _ => {
                            tail_expr = Some(expr);
                            break;
                        }
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

    fn if_expr(&mut self) -> Located<Expr<'text, 'surface>> {
        let start_range = self.range;
        let cond = self.expr().map(|expr| &*self.bump.alloc(expr));
        self.expect_token(TokenKind::KwThen);
        let then = self.expr().map(|expr| &*self.bump.alloc(expr));
        self.expect_token(TokenKind::KwElse);
        let r#else = self.expr().map(|expr| &*self.bump.alloc(expr));
        let end_range = self.range;
        Located::new(
            TextRange::new(start_range.start(), end_range.end()),
            Expr::If(cond, then, r#else),
        )
    }

    fn match_expr(&mut self) -> Located<Expr<'text, 'surface>> {
        let start_range = self.range;
        let scrut = self.expr().map(|expr| &*self.bump.alloc(expr));
        self.expect_token(TokenKind::LCurly);

        let mut cases = Vec::new_in(self.bump);
        while let Some(token) = self.peek_token() {
            if token.kind == TokenKind::RCurly {
                break;
            }

            let start_range = self.range;
            let pat = self.pat();
            self.expect_token(TokenKind::DoubleArrow);
            let expr = self.expr();
            let end_range = self.range;
            cases.push(Located::new(
                TextRange::new(start_range.start(), end_range.end()),
                MatchCase { pat, expr },
            ));
            self.expect_token(TokenKind::Punct(','));
        }

        self.expect_token(TokenKind::RCurly);
        let end_range = self.range;
        Located::new(
            TextRange::new(start_range.start(), end_range.end()),
            Expr::Match(scrut, cases.leak()),
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

    fn record_proj_expr(
        &mut self,
        scrut: Located<&'surface Expr<'text, 'surface>>,
    ) -> Located<Expr<'text, 'surface>> {
        let start_range = scrut.range;
        let label = match self.next_token() {
            Some(token) if token.kind == TokenKind::Ident => token,
            _ => {
                let end_range = self.range;
                self.diagnostic(
                    end_range,
                    Diagnostic::error().with_message("Expected identifier"),
                );
                return Located::new(
                    TextRange::new(start_range.start(), end_range.end()),
                    Expr::Error,
                );
            }
        };
        let end_range = self.range;
        Located::new(
            TextRange::new(start_range.start(), end_range.end()),
            Expr::RecordProj(scrut, Located::new(label.range, label.text())),
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
            let plicity = self.plicity();
            let expr = self.expr();
            let end_range = self.range;
            args.push(Located::new(
                TextRange::new(start_range.start(), end_range.end()),
                FunArg { plicity, expr },
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
            let plicity = self.plicity();
            let pat = self.pat();
            let end_range = self.range;
            params.push(Located::new(
                TextRange::new(start_range.start(), end_range.end()),
                FunParam { plicity, pat },
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

    fn plicity(&mut self) -> Plicity {
        match self.peek_token() {
            Some(token) if token.kind == TokenKind::Punct('@') => {
                self.next_token();
                Plicity::Implicit
            }
            _ => Plicity::Explicit,
        }
    }
}
