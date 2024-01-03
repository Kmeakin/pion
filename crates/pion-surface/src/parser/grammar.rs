use pion_lexer::token::TokenKind;
use pion_lexer::T;
use rowan::Checkpoint;

use super::Parser;
use crate::syntax::NodeKind;

// Module = Def*
pub fn module(p: &mut Parser) {
    p.start(NodeKind::Module);

    while !p.at_eof() {
        if p.at(T![def]) {
            def(p);
        } else {
            p.advance_with_error("expected a definition");
        }
    }

    p.close();
}

// Def = "def" "name" TypeAnn? = Expr ";"
fn def(p: &mut Parser) {
    p.start(NodeKind::DefItem);
    p.assert_advance(T![def]);

    p.expect(T![ident]);
    type_ann_opt(p);
    p.expect(T![=]);
    expr(p);
    p.expect(T![;]);

    p.close();
}

// TypeAnnOpt = TypeAnn?
fn type_ann_opt(p: &mut Parser) {
    if p.at(T![:]) {
        type_ann(p);
    }
}

// TypeAnn = ":" Expr
fn type_ann(p: &mut Parser) {
    p.start(NodeKind::TypeAnn);
    p.assert_advance(T![:]);
    expr(p);
    p.close();
}

pub fn expr(p: &mut Parser) {
    match p.peek() {
        Some(T![let]) => return let_expr(p),
        Some(T![if]) => return if_expr(p),
        Some(T![fun]) => return fun_expr(p),
        _ => {}
    }

    let lhs = p.checkpoint();
    atom_expr(p);

    loop {
        match p.peek() {
            // FunCallExpr = Expr ArgList
            Some(T!['(']) => {
                p.start_before(lhs, NodeKind::FunCallExpr);
                fun_arg_list(p);
                p.close();
            }
            // FieldProjExpr = Expr "." "Ident"
            // MethodCallExpr = Expr "." "Ident" ArgList
            Some(T![.]) => {
                p.assert_advance(T![.]);
                p.expect(T![ident]);

                let kind = if p.at(T!['(']) {
                    fun_arg_list(p);
                    NodeKind::MethodCallExpr
                } else {
                    NodeKind::FieldProjExpr
                };
                p.start_before(lhs, kind);
                p.close();
            }
            _ => break,
        }
    }

    loop {
        match p.peek() {
            Some(T![->]) => {
                p.start_before(lhs, NodeKind::FunArrowExpr);
                {
                    p.start(NodeKind::RetType);
                    p.assert_advance(T![->]);
                    expr(p);
                    p.close();
                }
                p.close();
            }
            Some(T![:]) => {
                p.start_before(lhs, NodeKind::AnnExpr);
                type_ann(p);
                p.close();
            }
            _ => break,
        }
    }
}

// FunArgList = "(" FunArg* ")"
fn fun_arg_list(p: &mut Parser) {
    p.start(NodeKind::FunArgList);
    p.assert_advance(T!['(']);
    list(p, T![')'], T![,], fun_arg);
    p.close();
}

// FunArg = "@"? Expr
fn fun_arg(p: &mut Parser) {
    p.start(NodeKind::FunArg);
    p.advance_if_at(T![@]);
    expr(p);
    p.close();
}

fn atom_expr(p: &mut Parser) {
    match p.peek() {
        Some(T![true] | T![false]) => {
            p.start(NodeKind::LitExpr);
            {
                p.start(NodeKind::BoolLit);
                p.advance();
                p.close();
            }
            p.close();
        }
        Some(T![dec_int] | T![bin_int] | T![hex_int]) => {
            p.start(NodeKind::LitExpr);
            {
                p.start(NodeKind::IntLit);
                p.advance();
                p.close();
            }
            p.close();
        }
        Some(T![_]) => {
            p.start(NodeKind::UnderscoreExpr);
            p.advance();
            p.close();
        }
        Some(T![ident]) => {
            p.start(NodeKind::IdentExpr);
            p.advance();
            p.close();
        }
        Some(T![match]) => match_expr(p),
        Some(T!['[']) => array_expr(p),
        Some(T!['(']) => paren_or_tuple_expr(p),
        Some(T!['{']) => record_expr(p),
        _ => {
            p.start(NodeKind::Error);
            p.advance_with_error("expected expression");
            p.close();
        }
    }
}

// LetExpr = "let" Pat TypeAnn? "=" Expr ";" Expr
fn let_expr(p: &mut Parser) {
    p.start(NodeKind::LetExpr);

    {
        p.assert_advance(T![let]);
        pat(p);
    }

    {
        type_ann_opt(p);
    }

    {
        p.start(NodeKind::LetInit);
        p.expect(T![=]);
        expr(p);
        p.close();
    }

    {
        p.expect(T![;]);
        expr(p);
    }

    p.close();
}

// IfExpr = "if" Expr "then" Expr "else" Expr
fn if_expr(p: &mut Parser) {
    p.start(NodeKind::IfExpr);

    {
        p.assert_advance(T![if]);
        expr(p);
    }

    {
        p.start(NodeKind::ThenExpr);
        p.expect(T![then]);
        expr(p);
        p.close();
    }
    {
        p.start(NodeKind::ElseExpr);
        p.expect(T![else]);
        expr(p);
        p.close();
    }

    p.close();
}

// FunLitExpr = "fun" FunParamList "=>" Expr
// FunTypeExpr = "fun" FunParamList "->" Expr
fn fun_expr(p: &mut Parser) {
    let c = p.checkpoint();

    {
        p.assert_advance(T![fun]);
        fun_param_list(p);
    }

    {
        let kind = match p.peek() {
            Some(T![=>]) => {
                p.advance();
                NodeKind::FunLitExpr
            }
            Some(T![->]) => {
                p.advance();
                NodeKind::FunTypeExpr
            }
            _ => {
                p.advance_with_error("expected arrow");
                NodeKind::FunLitExpr
            }
        };
        expr(p);
        p.start_before(c, kind);
        p.close();
    }
}

// FunParamList = "(" FunParam ")"
fn fun_param_list(p: &mut Parser) {
    p.start(NodeKind::FunParamList);
    p.expect(T!['(']);
    list(p, T![')'], T![,], fun_param);
    p.close();
}

// FunParam = "@"? Pat TypeAnn?
fn fun_param(p: &mut Parser) {
    p.start(NodeKind::FunParam);
    p.advance_if_at(T![@]);
    pat(p);
    type_ann_opt(p);
    p.close();
}

// MatchExpr = "match" Expr "{" MatchCase "}"
fn match_expr(p: &mut Parser) {
    p.start(NodeKind::MatchExpr);

    {
        p.assert_advance(T![match]);
        expr(p);
    }

    {
        p.expect(T!['{']);
        list(p, T!['}'], T![,], match_case);
    }

    p.close();
}

// MatchCase = Pat ("if" Expr) "=>" Expr
fn match_case(p: &mut Parser) {
    p.start(NodeKind::MatchCase);

    pat(p);

    if p.at(T![if]) {
        p.start(NodeKind::MatchGuard);
        p.assert_advance(T![if]);
        expr(p);
        p.close();
    }

    {
        p.expect(T![=>]);
        expr(p);
    }

    p.close();
}

// ArrayExpr = "[" Expr* "]"
fn array_expr(p: &mut Parser) {
    p.start(NodeKind::ArrayLitExpr);
    p.assert_advance(T!['[']);
    list(p, T![']'], T![,], expr);
    p.close();
}

// ParenExpr = "(" Expr ")"
// TupleExpr = "(" ")"
//          | "(" Expr ("," Expr)+ ","? ")"
fn paren_or_tuple_expr(p: &mut Parser) {
    let c = p.checkpoint();
    p.assert_advance(T!['(']);

    let mut seen_comma = false;
    let mut seen_expr = false;

    loop {
        match p.peek() {
            None | Some(T![')']) => break,
            Some(T![,]) => {
                p.assert_advance(T![,]);
                seen_comma = true;
                continue;
            }
            _ => {
                expr(p);
                seen_expr = true;
                if !p.at(T![')']) {
                    seen_comma |= p.expect(T![,]);
                }
            }
        }
    }
    p.expect(T![')']);

    p.start_before(
        c,
        if seen_expr && !seen_comma {
            NodeKind::ParenExpr
        } else {
            NodeKind::TupleLitExpr
        },
    );
    p.close();
}

// RecordExpr = "{" ExprField* "}"
fn record_expr(p: &mut Parser) {
    p.start(NodeKind::RecordExpr);
    p.assert_advance(T!['{']);
    list(p, T!['}'], T![,], record_expr_field);
    p.close();
}

// RecordExprField = "Ident"
//           | "Ident" "=" Expr
//           | "Ident" ":" Expr
fn record_expr_field(p: &mut Parser) {
    p.start(NodeKind::RecordExprField);
    p.expect(T![ident]);

    match p.peek() {
        Some(T![=]) => {
            p.assert_advance(T![=]);
            expr(p);
        }
        Some(T![:]) => {
            p.assert_advance(T![:]);
            expr(p);
        }
        _ => {}
    };

    p.close();
}

// OrPat = AtomPat ("|" AtomPat)+
pub fn pat(p: &mut Parser) {
    let c = p.checkpoint();
    atom_pat(p);

    if !p.at(T![|]) {
        return;
    }

    p.start_before(c, NodeKind::OrPat);
    while p.at(T![|]) {
        p.assert_advance(T![|]);
        atom_pat(p);
    }
    p.close();
}

// AtomPat = LitPat
//         | IdentPat
//         | UnderscorePat
//         | ParenPat
//         | TuplePat
//         | RecordPat
fn atom_pat(p: &mut Parser) -> Checkpoint {
    let c = p.checkpoint();
    match p.peek() {
        Some(T![true] | T![false]) => {
            p.start(NodeKind::LitPat);
            {
                p.start(NodeKind::BoolLit);
                p.advance();
                p.close();
            }
            p.close();
        }
        Some(T![dec_int] | T![bin_int] | T![hex_int]) => {
            p.start(NodeKind::LitPat);
            {
                p.start(NodeKind::IntLit);
                p.advance();
                p.close();
            }
            p.close();
        }
        Some(T![_]) => {
            p.start(NodeKind::UnderscorePat);
            p.advance();
            p.close();
        }
        Some(T![ident]) => {
            p.start(NodeKind::IdentPat);
            p.advance();
            p.close();
        }
        Some(T!['(']) => paren_or_tuple_pat(p),
        Some(T!['{']) => record_pat(p),
        _ => {
            p.start(NodeKind::Error);
            p.advance_with_error("expected pattern");
            p.close();
        }
    }
    c
}

// ParenPat = "(" Pat ")"
// TuplePat = "(" ")"
//          | "(" Pat ("," Pat)+ ","? ")"
fn paren_or_tuple_pat(p: &mut Parser) {
    let c = p.checkpoint();
    p.assert_advance(T!['(']);

    let mut seen_comma = false;
    let mut seen_pat = false;

    loop {
        match p.peek() {
            None | Some(T![')']) => break,
            Some(T![,]) => {
                p.assert_advance(T![,]);
                seen_comma = true;
                continue;
            }
            _ => {
                pat(p);
                seen_pat = true;
                if !p.at(T![')']) {
                    seen_comma |= p.expect(T![,]);
                }
            }
        }
    }
    p.expect(T![')']);

    p.start_before(
        c,
        if seen_pat && !seen_comma {
            NodeKind::ParenPat
        } else {
            NodeKind::TupleLitPat
        },
    );
    p.close();
}

// RecordPat = "{" "}"
//           | "{" PatField ("," PatField)* ","? "}"
fn record_pat(p: &mut Parser) {
    p.start(NodeKind::RecordLitPat);
    p.assert_advance(T!['{']);
    list(p, T!['}'], T![,], pat_field);
    p.close();
}

// PatField = "ident" ("=" Pat)?
fn pat_field(p: &mut Parser) {
    p.start(NodeKind::RecordPatField);
    p.expect(T![ident]);
    if p.advance_if_at(T![=]) {
        pat(p);
    }
    p.close();
}

fn list(p: &mut Parser, end: TokenKind, sep: TokenKind, elem: impl Fn(&mut Parser)) {
    loop {
        match p.peek() {
            None => break,
            Some(kind) if kind == end => break,
            Some(kind) if kind == sep => p.assert_advance(sep),
            _ => {
                elem(p);
                if !p.at(end) {
                    p.expect(sep);
                }
            }
        }
    }
    p.expect(end);
}
