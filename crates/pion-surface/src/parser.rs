use pion_lexer::token::{Token, TokenKind};
use pion_utils::location::ByteSpan;
use rowan::{Checkpoint, GreenNodeBuilder};

pub mod grammar;

use crate::reporting::SyntaxError;
use crate::syntax::{NodeKind, SyntaxKind, SyntaxNode};

pub struct Parser<'text, 'tokens> {
    /// Original program text
    text: &'text str,

    /// Tokens, including trivia
    tokens: &'tokens [Token],

    /// Index into `tokens`
    pos: usize,

    /// Span of most recent (non trivia) span
    span: ByteSpan,

    errors: Vec<SyntaxError>,
    builder: GreenNodeBuilder<'static>,
    pending_trivia: Vec<Token>,

    #[cfg(debug_assertions)]
    fuel: u8,
}

// Constructors
impl<'text, 'tokens> Parser<'text, 'tokens> {
    pub fn new(text: &'text str, tokens: &'tokens [Token]) -> Self {
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(NodeKind::Root.into());

        Self {
            text,
            tokens,
            pos: 0,
            span: ByteSpan::default(),
            errors: Vec::new(),
            pending_trivia: Vec::new(),
            builder,

            #[cfg(debug_assertions)]
            fuel: u8::MAX,
        }
    }

    pub fn finish(mut self) -> (SyntaxNode, Vec<SyntaxError>) {
        self.builder.finish_node();
        (SyntaxNode::new_root(self.builder.finish()), self.errors)
    }
}

// Creating nodes
impl<'text, 'tokens> Parser<'text, 'tokens> {
    fn start(&mut self, kind: NodeKind) {
        self.drain_trivia();
        self.builder.start_node(kind.into());
    }

    fn start_before(&mut self, checkpoint: Checkpoint, kind: NodeKind) {
        self.builder.start_node_at(checkpoint, kind.into());
    }

    fn close(&mut self) { self.builder.finish_node(); }

    fn checkpoint(&mut self) -> Checkpoint {
        self.drain_trivia();
        self.builder.checkpoint()
    }
}

// Reporting errors
impl<'text, 'tokens> Parser<'text, 'tokens> {
    fn error(&mut self, err: SyntaxError) { self.errors.push(err); }

    fn advance_with_error(&mut self, msg: &'static str) {
        self.advance();
        self.error(SyntaxError::Custom {
            span: self.span,
            msg,
        });
    }

    fn expect(&mut self, expected: TokenKind) -> bool {
        match self.peek_token() {
            Some(token) if token.kind() == expected => {
                self.do_token(token);
                true
            }
            got => {
                self.error(SyntaxError::Expected {
                    span: self.span,
                    expected,
                    got: got.map(|token| token.kind()),
                });
                false
            }
        }
    }
}

// Inspecting tokens
impl<'text, 'tokens> Parser<'text, 'tokens> {
    fn peek_token(&mut self) -> Option<Token> {
        #[cfg(debug_assertions)]
        {
            assert_ne!(self.fuel, 0, "parser is stuck");
            self.fuel -= 1;
        }
        self.skip_trivia();
        self.tokens.get(self.pos).copied()
    }

    fn peek(&mut self) -> Option<TokenKind> { self.peek_token().map(|token| token.kind()) }

    fn at(&mut self, kind: TokenKind) -> bool { self.peek() == Some(kind) }

    fn at_eof(&mut self) -> bool { self.peek().is_none() }
}

// Advancing through tokens
impl<'text, 'tokens> Parser<'text, 'tokens> {
    fn skip_trivia(&mut self) {
        loop {
            match self.tokens.get(self.pos) {
                Some(token) if token.kind().is_trivia() => {
                    self.pending_trivia.push(*token);
                    self.pos += 1;
                }
                _ => break,
            }
        }
    }

    fn drain_trivia(&mut self) {
        for token in self.pending_trivia.drain(..) {
            let span = token.span();
            let text = &self.text[span];
            self.builder
                .token(SyntaxKind::Token(token.kind()).into(), text);
        }
    }

    fn do_token(&mut self, token: Token) {
        #[cfg(debug_assertions)]
        {
            self.fuel = u8::MAX;
        }

        self.drain_trivia();

        self.pos += 1;
        let span = token.span();
        self.span = span;
        let text = &self.text[span];
        self.builder
            .token(SyntaxKind::Token(token.kind()).into(), text);
    }

    fn advance(&mut self) -> bool {
        match self.peek_token() {
            None => false,
            Some(token) => {
                self.do_token(token);
                true
            }
        }
    }

    fn advance_if(&mut self, mut f: impl FnMut(TokenKind) -> bool) -> bool {
        match self.peek_token() {
            Some(kind) if f(kind.kind()) => {
                self.do_token(kind);
                true
            }
            _ => false,
        }
    }

    fn advance_if_at(&mut self, kind: TokenKind) -> bool { self.advance_if(|k| k == kind) }

    fn assert_advance(&mut self, kind: TokenKind) {
        if cfg!(debug_assertions) {
            match self.peek_token() {
                None => panic!("expected {kind:?}, got EOF"),
                Some(token) => assert_eq!(token.kind(), kind),
            }
        }

        self.advance();
    }
}
