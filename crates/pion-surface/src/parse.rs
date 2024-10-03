use codespan_reporting::diagnostic::Diagnostic;
use text_size::TextRange;

use crate::lex::Token;
use crate::syntax::*;

mod grammar;

#[cfg(test)]
mod tests;

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
