//! Lexical syntax
//! ```text
//! Token ::= Trivia | Delimiter | Atom
//!
//! Trivia ::= Whitespace | LineComment
//! Whitespace ::= WhitespaceChar+
//! WhitespaceChar ::=
//!     | U+0009 (horizontal tab, '\t')
//!     | U+000A (line feed, '\n')
//!     | U+000B (vertical tab)
//!     | U+000C (form feed)
//!     | U+000D (carriage return, '\r')
//!     | U+0020 (space, ' ')
//!     | U+0085 (next line)
//!     | U+200E (left-to-right mark)
//!     | U+200F (right-to-left mark)
//!     | U+2028 (line separator)
//!     | U+2029 (paragraph separator)
//!
//! LineComment ::= "//" (not LineTerminator)*
//! LineTerminator ::=
//!     | U+000A (line feed, '\n')
//!     | U+000B (vertical tab)
//!     | U+000C (form feed)
//!     | U+000D (carriage return, '\r')
//!     | U+0085 (next line)
//!     | U+2028 (line separator)
//!     | U+2029 (paragraph separator)
//!
//! Delimiter ::= '(' | ')' | '{' | '}' | '[' | ']'
//!
//! Atom ::= Punct | Ident | Literal
//!
//! Punct ::=
//!      | '!' | '#' | '$' | '%' | '&' | '*' | '+' | ',' | '-' | '.' | '/' | ':'
//!      | ';' | '<' | '=' | '>' | '?' | '@' | '\' | '^' | '_' | '`' | '|' | '~'
//!
//! Ident ::=
//!     | XID_Start (XID_Continue | '-')*
//!     | '_' XID_Continue (XID_Continue | '-')*
//!
//! Literal ::= Number | Char | String
//!
//! Number ::= ('+' | '-')? DecimalDigit XID_Continue*
//! ```

use std::str::Chars;

use text_size::{TextRange, TextSize};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum TokenKind {
    // Trivia
    Unknown = 1,
    Whitespace,
    LineComment,

    // Delimiters
    LParen,
    RParen,
    LSquare,
    RSquare,
    LCurly,
    RCurly,

    // Atoms
    Ident,
    Punct(char),
    Literal(LiteralKind),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LiteralKind {
    Number,
    Char,
    String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntBase {
    Dec,
    Bin,
    Hex,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Token<'text> {
    pub text: &'text str,
    pub kind: TokenKind,
    pub range: TextRange,
}

impl<'text> Token<'text> {
    pub fn new(text: &'text str, kind: TokenKind, range: TextRange) -> Self {
        Self { text, kind, range }
    }
}

mod classify {
    pub fn whitespace(c: &char) -> bool {
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

    pub fn line_terminator(c: &char) -> bool {
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
    pub fn punct(c: &char) -> bool {
      matches!(c,
        | '!' | '#' | '$' | '%' | '&' | '*' | '+' | ',' | '-' | '.' | '/' | ':'
        | ';' | '<' | '=' | '>' | '?' | '@' | '\\' | '^' | '_' | '`' | '|' | '~'
      )
    }

    pub fn ident_start(c: &char) -> bool { c.is_alphabetic() || *c == '_' }

    pub fn ident_continue(c: &char) -> bool { ident_start(c) || c.is_ascii_digit() || *c == '-' }
}

fn skip_while(chars: &mut Chars, mut predicate: impl Copy + FnMut(&char) -> bool) {
    loop {
        let mut iter = chars.clone();
        match iter.next() {
            None => break,
            Some(c) => match predicate(&c) {
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
        c if classify::whitespace(&c) => {
            skip_while(&mut chars, classify::whitespace);
            TokenKind::Whitespace
        }

        '/' if peek() == Some('/') => {
            skip_while(&mut chars, |c| !classify::line_terminator(c));
            TokenKind::LineComment
        }

        '0'..='9' => {
            skip_while(&mut chars, classify::ident_continue);
            TokenKind::Literal(LiteralKind::Number)
        }
        '-' | '+' if peek().is_some_and(|c| char::is_ascii_digit(&c)) => {
            skip_while(&mut chars, classify::ident_continue);
            TokenKind::Literal(LiteralKind::Number)
        }
        '_' if peek() == Some('-') => TokenKind::Punct(c),
        '_' if peek().is_some_and(|c| classify::ident_continue(&c)) => {
            skip_while(&mut chars, classify::ident_continue);
            TokenKind::Ident
        }

        c if classify::punct(&c) => TokenKind::Punct(c),

        c if classify::ident_start(&c) => {
            skip_while(&mut chars, classify::ident_continue);
            TokenKind::Ident
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
            TokenKind::Literal(LiteralKind::Char)
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
            TokenKind::Literal(LiteralKind::String)
        }

        _ => TokenKind::Unknown,
    };

    let remainder = chars.as_str();
    let text = source.strip_suffix(remainder).unwrap();

    Some((text, kind, remainder))
}

pub fn lex(mut source: &str) -> impl Iterator<Item = Token<'_>> + '_ {
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

#[cfg(test)]
mod tests {
    use std::fmt::Write;

    use expect_test::{expect, Expect};

    use super::*;

    #[track_caller]
    fn assert_lex(text: &str, expected: &Expect) {
        let mut got = String::with_capacity(text.len());
        for token in lex(text) {
            writeln!(got, "{:?} {:?} {:?}", token.kind, token.range, token.text).unwrap();
        }
        expected.assert_eq(got.trim_end());
    }

    macro_rules! assert_lex {
        ($text:literal => $expected:expr) => {
            assert_lex($text, &$expected)
        };
    }

    #[test]
    fn empty() {
        assert_lex!("" => expect![""]);
    }

    #[test]
    fn unknown() {
        assert_lex!("\u{00}\u{7F}\u{80}" => expect![[r#"
            Unknown 0..1 "\0"
            Unknown 1..2 "\u{7f}"
            Unknown 2..4 "\u{80}""#]]);
    }

    #[test]
    fn whitespace() {
        assert_lex!("\t\n\x0B\x0C\r "=> expect![[r#"Whitespace 0..6 "\t\n\u{b}\u{c}\r ""#]]);
        assert_lex!("\t\n\x0B\x0C\r\u{0085}\u{200E}\u{200F}\u{2028}\u{2029}"=> expect![[r#"Whitespace 0..19 "\t\n\u{b}\u{c}\r\u{85}\u{200e}\u{200f}\u{2028}\u{2029}""#]]);
    }

    #[test]
    fn line_comment() {
        assert_lex!("// line comment"          => expect![[r#"LineComment 0..15 "// line comment""#]]);
        assert_lex!("// line comment\u{000A}"  => expect![[r#"
            LineComment 0..15 "// line comment"
            Whitespace 15..16 "\n""#]]);
        assert_lex!("// line comment\u{000B}"  => expect![[r#"
            LineComment 0..15 "// line comment"
            Whitespace 15..16 "\u{b}""#]]);
        assert_lex!("// line comment\u{000C}"  => expect![[r#"
            LineComment 0..15 "// line comment"
            Whitespace 15..16 "\u{c}""#]]);
        assert_lex!("// line comment\u{000D}"  => expect![[r#"
            LineComment 0..15 "// line comment"
            Whitespace 15..16 "\r""#]]);
        assert_lex!("// line comment\u{00085}" => expect![[r#"
            LineComment 0..15 "// line comment"
            Whitespace 15..17 "\u{85}""#]]);
        assert_lex!("// line comment\u{2028}"  => expect![[r#"
            LineComment 0..15 "// line comment"
            Whitespace 15..18 "\u{2028}""#]]);
        assert_lex!("// line comment\u{2029}"  => expect![[r#"
            LineComment 0..15 "// line comment"
            Whitespace 15..18 "\u{2029}""#]]);
    }

    #[test]
    fn delimiter() {
        assert_lex!("()[]{}" => expect![[r#"
            LParen 0..1 "("
            RParen 1..2 ")"
            LSquare 2..3 "["
            RSquare 3..4 "]"
            LCurly 4..5 "{"
            RCurly 5..6 "}""#]]
        );
    }

    #[test]
    fn punct() {
        assert_lex!("!#$%&*+,-./:;<=>?@\\^_`|~" => expect![[r##"
            Punct('!') 0..1 "!"
            Punct('#') 1..2 "#"
            Punct('$') 2..3 "$"
            Punct('%') 3..4 "%"
            Punct('&') 4..5 "&"
            Punct('*') 5..6 "*"
            Punct('+') 6..7 "+"
            Punct(',') 7..8 ","
            Punct('-') 8..9 "-"
            Punct('.') 9..10 "."
            Punct('/') 10..11 "/"
            Punct(':') 11..12 ":"
            Punct(';') 12..13 ";"
            Punct('<') 13..14 "<"
            Punct('=') 14..15 "="
            Punct('>') 15..16 ">"
            Punct('?') 16..17 "?"
            Punct('@') 17..18 "@"
            Punct('\\') 18..19 "\\"
            Punct('^') 19..20 "^"
            Punct('_') 20..21 "_"
            Punct('`') 21..22 "`"
            Punct('|') 22..23 "|"
            Punct('~') 23..24 "~""##]]
        );
        assert_lex!("_-" => expect![[r#"
            Punct('_') 0..1 "_"
            Punct('-') 1..2 "-""#]]);
    }

    #[test]
    fn ident() {
        assert_lex!("abcd1234" => expect![[r#"Ident 0..8 "abcd1234""#]]
        );

        // Leading '-' at start of ident is interpreted as Punct
        assert_lex!("-abcd1234" => expect![[r#"
            Punct('-') 0..1 "-"
            Ident 1..9 "abcd1234""#]]
        );

        assert_lex!("a-" => expect![[r#"Ident 0..2 "a-""#]]);
        assert_lex!("a-b" => expect![[r#"Ident 0..3 "a-b""#]]);
        assert_lex!("_a" => expect![[r#"Ident 0..2 "_a""#]]);

        assert_lex!("_-" => expect![[r#"
            Punct('_') 0..1 "_"
            Punct('-') 1..2 "-""#]]
        );

        assert_lex!("-_" => expect![[r#"
            Punct('-') 0..1 "-"
            Punct('_') 1..2 "_""#]]
        );

        assert_lex!("__" => expect![[r#"Ident 0..2 "__""#]]);
        assert_lex!("λ" => expect![[r#"Ident 0..2 "λ""#]]);
    }

    #[test]
    fn number() {
        assert_lex!("123_456 0x123_456 0b123_456 -123 +123" => expect![[r#"
            Literal(Number) 0..7 "123_456"
            Whitespace 7..8 " "
            Literal(Number) 8..17 "0x123_456"
            Whitespace 17..18 " "
            Literal(Number) 18..27 "0b123_456"
            Whitespace 27..28 " "
            Literal(Number) 28..32 "-123"
            Whitespace 32..33 " "
            Literal(Number) 33..37 "+123""#]]);
    }

    #[test]
    fn char() {
        assert_lex!("'a'" => expect![[r#"Literal(Char) 0..3 "'a'""#]]);
        assert_lex!("'abc'" => expect![[r#"Literal(Char) 0..5 "'abc'""#]]);
        assert_lex!("'abc" => expect![[r#"Literal(Char) 0..4 "'abc""#]]);
        assert_lex!(r"'abc\'def'" => expect![[r#"Literal(Char) 0..10 "'abc\\'def'""#]]);
        assert_lex!(
            r"'abc\\'def'" => expect![[r#"
                Literal(Char) 0..7 "'abc\\\\'"
                Ident 7..10 "def"
                Literal(Char) 10..11 "'""#]]
        );
    }

    #[test]
    fn string() {
        assert_lex!(r#""""# => expect![[r#"Literal(String) 0..2 "\"\"""#]]);
        assert_lex!(r#""a""# => expect![[r#"Literal(String) 0..3 "\"a\"""#]]);
        assert_lex!(r#""abc""# => expect![[r#"Literal(String) 0..5 "\"abc\"""#]]);
        assert_lex!(r#""abc"# => expect![[r#"Literal(String) 0..4 "\"abc""#]]);
        assert_lex!(r#""abc\"def"# => expect![[r#"Literal(String) 0..9 "\"abc\\\"def""#]]);
        assert_lex!(r#""abc\\"def""# => expect![[r#"
            Literal(String) 0..7 "\"abc\\\\\""
            Ident 7..10 "def"
            Literal(String) 10..11 "\"""#]]
        );
    }
}
