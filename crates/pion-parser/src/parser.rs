use pion_lexer::token::{Token, TokenKind};
use pion_utils::location::ByteSpan;

use crate::reporting::SyntaxError;
use crate::syntax::NodeKind;
use crate::tree::{ParseEvent, SyntaxTree};

#[derive(Debug, Copy, Clone)]
pub struct OpenNode {
    pos: u32,
}

pub struct Parser<'tokens> {
    tokens: &'tokens [Token],
    span: ByteSpan,

    pending_trivia: Vec<ParseEvent>,
    events: Vec<ParseEvent>,
    errors: Vec<SyntaxError>,

    #[cfg(debug_assertions)]
    fuel: u8,
}

/// Construction and destruction
impl<'tokens> Parser<'tokens> {
    pub fn new(tokens: &'tokens [Token]) -> Self {
        Self {
            tokens,
            span: ByteSpan::default(),

            pending_trivia: Vec::new(),
            events: Vec::new(),
            errors: Vec::new(),

            #[cfg(debug_assertions)]
            fuel: u8::MAX,
        }
    }

    pub fn finish(mut self, text: String) -> (SyntaxTree, Vec<SyntaxError>) {
        self.end_node(NodeKind::Root, OpenNode { pos: 0 });
        let tree = SyntaxTree::from_postorder(text, &self.events);
        (tree, self.errors)
    }
}

/// Inspecting token stream
impl<'tokens> Parser<'tokens> {
    pub fn peek(&mut self) -> Option<TokenKind> {
        #[cfg(debug_assertions)]
        {
            assert_ne!(self.fuel, 0, "Parser stuck");
            self.fuel -= 1;
        }

        loop {
            match self.tokens.split_first() {
                Some((token, tokens)) if token.kind.is_trivia() => {
                    self.tokens = tokens;
                    self.pending_trivia.push(ParseEvent::Token {
                        kind: token.kind,
                        span_len: token.span().len(),
                    });
                }
                Some((token, _)) => return Some(token.kind),
                None => return None,
            }
        }
    }

    pub fn at(&mut self, kind: TokenKind) -> bool { self.peek() == Some(kind) }

    pub fn at_eof(&mut self) -> bool { self.peek().is_none() }
}

// Advancing through tokens
impl<'tokens> Parser<'tokens> {
    pub fn advance(&mut self) -> Option<TokenKind> {
        #[cfg(debug_assertions)]
        {
            self.fuel = u8::MAX;
        }

        self.flush_pending_trivia();
        match self.tokens.split_first() {
            None => None,
            Some((token, tokens)) => {
                debug_assert!(!token.kind.is_trivia());
                self.tokens = tokens;
                self.span = token.span;
                self.events.push(ParseEvent::Token {
                    kind: token.kind,
                    span_len: token.span.len(),
                });
                Some(token.kind)
            }
        }
    }

    pub fn advance_if_at(&mut self, kind: TokenKind) -> bool {
        if self.at(kind) {
            self.advance();
            true
        } else {
            false
        }
    }

    pub fn assert_advance(&mut self, kind: TokenKind) {
        let got = self.advance();
        debug_assert_eq!(got, Some(kind));
    }

    pub fn expect(&mut self, expected: TokenKind) -> bool {
        match self.peek() {
            Some(got) if got == expected => {
                self.advance();
                true
            }
            got => {
                self.errors.push(SyntaxError::Expected {
                    span: self.span,
                    expected,
                    got,
                });
                false
            }
        }
    }

    pub fn advance_with_error(&mut self, msg: &'static str) {
        self.advance();
        self.errors.push(SyntaxError::Custom {
            span: self.span,
            msg,
        });
    }
}

/// Emitting events
impl<'tokens> Parser<'tokens> {
    // REASON: `elems.len()` cannot be more than `u32::MAX` because of limit on file
    // size
    #[allow(clippy::cast_possible_truncation)]
    pub fn start_node(&mut self) -> OpenNode {
        self.flush_pending_trivia();
        OpenNode {
            pos: self.events.len() as u32,
        }
    }

    #[allow(clippy::cast_possible_truncation)]
    pub fn end_node(&mut self, kind: NodeKind, start: OpenNode) {
        let start = start.pos;
        let end = self.events.len() as u32;
        debug_assert!(start <= end);
        self.events.push(ParseEvent::Node {
            kind,
            num_descendents: end - start,
        });
        self.flush_pending_trivia();
    }

    pub fn flush_pending_trivia(&mut self) { self.events.append(&mut self.pending_trivia); }
}
