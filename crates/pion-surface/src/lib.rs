pub mod reporting;
pub mod syntax;

mod parser;

#[cfg(test)]
mod tests;

use parser::Parser;
use reporting::SyntaxError;
use syntax::{AstNode, Root};

pub fn parse_expr(src: &str) -> (Root, Vec<SyntaxError>) {
    parse(src, crate::parser::grammar::expr)
}

pub fn parse_pat(src: &str) -> (Root, Vec<SyntaxError>) { parse(src, crate::parser::grammar::pat) }

pub fn parse_module(src: &str) -> (Root, Vec<SyntaxError>) {
    parse(src, crate::parser::grammar::module)
}

pub fn parse(src: &str, entrypoint: impl Fn(&mut Parser)) -> (Root, Vec<SyntaxError>) {
    let mut tokens = Vec::new();
    let mut token_errors = Vec::new();

    pion_lexer::lex(src, &mut tokens, &mut token_errors);

    let (node, errors) = {
        let mut p = crate::parser::Parser::new(src, &tokens);
        entrypoint(&mut p);
        p.finish()
    };

    (AstNode::cast(node).unwrap(), errors)
}
