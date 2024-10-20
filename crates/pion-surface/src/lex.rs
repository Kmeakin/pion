//! See `lexical-syntax.md`

use core::fmt;
use std::marker::PhantomData;
use std::ptr::NonNull;
use std::str::{Chars, FromStr};

use text_size::{TextRange, TextSize};

#[cfg(test)]
mod tests;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    // Trivia
    Unknown,
    Whitespace,
    LineComment,

    // Delimiters
    LParen,
    RParen,
    LSquare,
    RSquare,
    LCurly,
    RCurly,

    // Punctuation
    SingleArrow,
    DoubleArrow,
    Punct(char),

    // Identifiers / keywords
    Ident,
    KwDo,
    KwElse,
    KwFalse,
    KwForall,
    KwFun,
    KwIf,
    KwLet,
    KwMatch,
    KwThen,
    KwTrue,

    // Literals
    Int,
    Char,
    String,
}

impl TokenKind {
    pub fn is_trivia(&self) -> bool {
        matches!(self, Self::Unknown | Self::Whitespace | Self::LineComment)
    }

    pub fn from_reserved(reserved: ReservedIdent) -> Self {
        match reserved {
            ReservedIdent::Do => Self::KwDo,
            ReservedIdent::Else => Self::KwElse,
            ReservedIdent::False => Self::KwFalse,
            ReservedIdent::Forall => Self::KwForall,
            ReservedIdent::Fun => Self::KwFun,
            ReservedIdent::If => Self::KwIf,
            ReservedIdent::Let => Self::KwLet,
            ReservedIdent::Match => Self::KwMatch,
            ReservedIdent::Then => Self::KwThen,
            ReservedIdent::True => Self::KwTrue,
        }
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unknown => write!(f, "unknown character"),
            Self::Whitespace => write!(f, "whitespace"),
            Self::LineComment => write!(f, "line comment"),

            Self::LParen => write!(f, "`(`"),
            Self::RParen => write!(f, "`)`"),
            Self::LSquare => write!(f, "`[`"),
            Self::RSquare => write!(f, "`]`"),
            Self::LCurly => write!(f, "`{{`"),
            Self::RCurly => write!(f, "`}}`"),

            Self::SingleArrow => write!(f, "`->`"),
            Self::DoubleArrow => write!(f, "`=>`"),
            Self::Punct(c) => write!(f, "`{c}`"),

            Self::Ident => write!(f, "identifier"),
            Self::KwDo => write!(f, "`do`"),
            Self::KwElse => write!(f, "`else`"),
            Self::KwFalse => write!(f, "`false`"),
            Self::KwForall => write!(f, "`forall`"),
            Self::KwFun => write!(f, "`fun`"),
            Self::KwIf => write!(f, "`if`"),
            Self::KwLet => write!(f, "`let`"),
            Self::KwMatch => write!(f, "`match`"),
            Self::KwThen => write!(f, "`then`"),
            Self::KwTrue => write!(f, "`true`"),

            Self::Int => write!(f, "integer"),
            Self::Char => write!(f, "character"),
            Self::String => write!(f, "string"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReservedIdent {
    Do,
    Else,
    False,
    Forall,
    Fun,
    If,
    Let,
    Match,
    Then,
    True,
}

impl FromStr for ReservedIdent {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "do" => Ok(Self::Do),
            "else" => Ok(Self::Else),
            "false" => Ok(Self::False),
            "forall" => Ok(Self::Forall),
            "fun" => Ok(Self::Fun),
            "if" => Ok(Self::If),
            "let" => Ok(Self::Let),
            "match" => Ok(Self::Match),
            "then" => Ok(Self::Then),
            "true" => Ok(Self::True),
            _ => Err(()),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Token<'text> {
    text: NonNull<u8>,
    pub kind: TokenKind,
    pub range: TextRange,

    phantom: PhantomData<&'text str>,
}

impl<'text> Token<'text> {
    pub fn new(text: &'text str, kind: TokenKind, range: TextRange) -> Self {
        debug_assert_eq!(text.len(), range.len().into());

        Self {
            // SAFETY: `text` is a valid reference to a valid string
            text: unsafe { NonNull::new_unchecked(text.as_ptr().cast_mut()) },
            kind,
            range,
            phantom: PhantomData,
        }
    }

    pub fn text(&self) -> &'text str {
        // SAFETY: `text` is a valid reference to a valid string, and `range` encodes
        // the length of the string
        unsafe { std::str::from_raw_parts(self.text.as_ptr(), self.range.len().into()) }
    }
}

impl fmt::Debug for Token<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Token")
            .field("text", &self.text())
            .field("kind", &self.kind)
            .field("range", &self.range)
            .finish()
    }
}

mod classify {
    pub fn whitespace(c: char) -> bool {
        matches!(
            c,
            '\u{0009}'
                | '\u{000A}'
                | '\u{000B}'
                | '\u{000C}'
                | '\u{000D}'
                | '\u{0020}'
                | '\u{0085}'
                | '\u{200E}'
                | '\u{200F}'
                | '\u{2028}'
                | '\u{2029}'
        )
    }

    pub fn line_terminator(c: char) -> bool {
        matches!(
            c,
            '\u{000A}'
                | '\u{000B}'
                | '\u{000C}'
                | '\u{000D}'
                | '\u{0085}'
                | '\u{2028}'
                | '\u{2029}'
        )
    }

    #[rustfmt::skip]
    pub fn punct(c: char) -> bool {
      matches!(c,
        | '!' | '#' | '$' | '%' | '&' | '*' | '+' | ',' | '-' | '.' | '/' | ':'
        | ';' | '<' | '=' | '>' | '?' | '@' | '\\' | '^' | '_' | '`' | '|' | '~'
      )
    }

    pub fn ident_start(c: char) -> bool { c.is_alphabetic() || c == '_' }

    pub fn ident_continue(c: char) -> bool { ident_start(c) || c.is_ascii_digit() || c == '-' }
}

fn skip_while(chars: &mut Chars, mut predicate: impl Copy + FnMut(char) -> bool) {
    loop {
        let mut iter = chars.clone();
        match iter.next() {
            None => break,
            Some(c) => match predicate(c) {
                true => *chars = iter,
                false => break,
            },
        }
    }
}

pub fn next_token(source: &str) -> Option<(&str, TokenKind, &str)> {
    let mut chars = source.chars();
    let c = chars.next()?;
    let peek = || chars.clone().next();

    let kind = match c {
        c if classify::whitespace(c) => {
            skip_while(&mut chars, classify::whitespace);
            TokenKind::Whitespace
        }

        '/' if peek() == Some('/') => {
            skip_while(&mut chars, |c| !classify::line_terminator(c));
            TokenKind::LineComment
        }

        '0'..='9' => {
            skip_while(&mut chars, classify::ident_continue);
            TokenKind::Int
        }
        '-' if peek() == Some('>') => {
            chars.next();
            TokenKind::SingleArrow
        }
        '=' if peek() == Some('>') => {
            chars.next();
            TokenKind::DoubleArrow
        }
        '_' if peek() == Some('-') => TokenKind::Punct(c),
        '_' if peek().is_some_and(classify::ident_continue) => {
            skip_while(&mut chars, classify::ident_continue);
            TokenKind::Ident
        }

        c if classify::punct(c) => TokenKind::Punct(c),

        c if classify::ident_start(c) => {
            skip_while(&mut chars, classify::ident_continue);
            let remainder = chars.as_str();
            let len = source.len() - remainder.len();
            let (text, remainder) = source.split_at(len);

            let kind = match ReservedIdent::from_str(text) {
                Ok(reserved) => TokenKind::from_reserved(reserved),
                Err(()) => TokenKind::Ident,
            };
            return Some((text, kind, remainder));
        }

        '(' => TokenKind::LParen,
        ')' => TokenKind::RParen,
        '[' => TokenKind::LSquare,
        ']' => TokenKind::RSquare,
        '{' => TokenKind::LCurly,
        '}' => TokenKind::RCurly,

        '\'' => {
            while let Some(c) = chars.next() {
                match c {
                    '\'' => break,
                    '\\' => match chars.next() {
                        Some(_) => continue,
                        None => break,
                    },
                    _ => continue,
                }
            }
            TokenKind::Char
        }
        '\"' => {
            while let Some(c) = chars.next() {
                match c {
                    '\"' => break,
                    '\\' => match chars.next() {
                        Some(_) => continue,
                        None => break,
                    },
                    _ => continue,
                }
            }
            TokenKind::String
        }

        _ => TokenKind::Unknown,
    };

    let remainder = chars.as_str();
    let len = source.len() - remainder.len();
    let (text, remainder) = source.split_at(len);
    Some((text, kind, remainder))
}

pub fn lex(mut source: &str) -> impl Clone + Iterator<Item = Token<'_>> + '_ {
    let mut pos = 0;
    std::iter::from_fn(move || {
        let (text, kind, remainder) = next_token(source)?;
        let start = pos;
        let end = start + text.len();
        pos = end;
        source = remainder;

        #[allow(
            clippy::as_conversions,
            clippy::cast_possible_truncation,
            reason = "Source files cannot be more than u32::MAX bytes long"
        )]
        let range = TextRange::new(TextSize::new(start as u32), TextSize::new(end as u32));
        Some(Token::new(text, kind, range))
    })
}

#[test]
#[cfg(target_pointer_width = "64")]
fn type_sizes() {
    assert_eq!(size_of::<TokenKind>(), 4);
    assert_eq!(size_of::<Token>(), 24);
}
