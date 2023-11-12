#![allow(clippy::cast_possible_truncation)]

use pion_utils::location::{BytePos, ByteSpan};

use crate::token::{Token, TokenKind};
use crate::LexError;

type LexerFn = fn(BytePos, &[u8], &mut Vec<Token>, &mut Vec<LexError>);
type LexerTable = [LexerFn; 256];

macro_rules! try_dispatch {
    ($pos:expr, $bytes:expr, $tokens:expr, $errors:expr) => {
        match $bytes.get(usize::from($pos)) {
            Some(c) => return DISPATCH_TABLE[*c as usize]($pos, $bytes, $tokens, $errors),
            None => return,
        }
    };
}

macro_rules! emit_token {
    ($token:expr, $pos:expr, $bytes:expr, $tokens:expr, $errors:expr) => {
        match $tokens.push_within_capacity($token) {
            Ok(()) => {}
            Err(_) => return resize_vectors($pos, $bytes, $tokens, $errors),
        }
    };
}

fn do_unknown_ascii_byte(
    pos: BytePos,
    bytes: &[u8],
    tokens: &mut Vec<Token>,
    errors: &mut Vec<LexError>,
) {
    let span = ByteSpan::new(pos, pos + 1);
    let token = Token::new(TokenKind::Error, span);
    emit_token!(token, pos, bytes, tokens, errors);
    // tokens.push(token);
    errors.push_within_capacity(LexError::UnknownChar { span });
    try_dispatch!(pos + 1, bytes, tokens, errors);
}

fn do_unknown_2byte_char(
    pos: BytePos,
    bytes: &[u8],
    tokens: &mut Vec<Token>,
    errors: &mut Vec<LexError>,
) {
    let span = ByteSpan::new(pos, pos + 2);
    let token = Token::new(TokenKind::Error, span);
    emit_token!(token, pos, bytes, tokens, errors);
    // tokens.push(Token::new(TokenKind::Error, span));
    errors.push_within_capacity(LexError::UnknownChar { span });
    try_dispatch!(pos + 2, bytes, tokens, errors);
}

fn do_unknown_3byte_char(
    pos: BytePos,
    bytes: &[u8],
    tokens: &mut Vec<Token>,
    errors: &mut Vec<LexError>,
) {
    let span = ByteSpan::new(pos, pos + 3);
    let token = Token::new(TokenKind::Error, span);
    emit_token!(token, pos, bytes, tokens, errors);
    // tokens.push(Token::new(TokenKind::Error, span));
    errors.push_within_capacity(LexError::UnknownChar { span });
    try_dispatch!(pos + 3, bytes, tokens, errors);
}

fn do_unknown_4byte_char(
    pos: BytePos,
    bytes: &[u8],
    tokens: &mut Vec<Token>,
    errors: &mut Vec<LexError>,
) {
    let span = ByteSpan::new(pos, pos + 4);
    let token = Token::new(TokenKind::Error, span);
    emit_token!(token, pos, bytes, tokens, errors);
    // tokens.push(Token::new(TokenKind::Error, span));
    errors.push_within_capacity(LexError::UnknownChar { span });
    try_dispatch!(pos + 4, bytes, tokens, errors);
}

fn do_ascii_whitespace(
    pos: BytePos,
    bytes: &[u8],
    tokens: &mut Vec<Token>,
    errors: &mut Vec<LexError>,
) {
    let span = ByteSpan::new(pos, pos + 1);
    let token = Token::new(TokenKind::Whitespace, span);
    emit_token!(token, pos, bytes, tokens, errors);
    // tokens.push(token);
    try_dispatch!(pos + 1, bytes, tokens, errors);
}

fn do_line_comment_or_block_comment(
    pos: BytePos,
    bytes: &[u8],
    tokens: &mut Vec<Token>,
    errors: &mut Vec<LexError>,
) {
    let mut len = 1_u32;
    match bytes.get(usize::from(pos + len)) {
        None => {
            let span = ByteSpan::new(pos, pos + len);
            let token = Token::new(TokenKind::Error, span);
            emit_token!(token, pos, bytes, tokens, errors);
            // tokens.push(token);
            errors.push_within_capacity(LexError::UnknownChar { span });
            try_dispatch!(pos + len, bytes, tokens, errors);
        }
        Some(b'/') => {
            len += 1;

            let remainder = unsafe { bytes.get_unchecked(usize::from(pos + len)..) };
            match memchr::memchr(b'\n', remainder) {
                None => {
                    len += remainder.len() as u32;
                    let span = ByteSpan::new(pos, pos + len);
                    let token = Token::new(TokenKind::LineComment, span);
                    emit_token!(token, pos, bytes, tokens, errors);
                    // tokens.push(token);
                }
                Some(extra) => {
                    len += extra as u32 + 1;
                    let span = ByteSpan::new(pos, pos + len);
                    let token = Token::new(TokenKind::LineComment, span);
                    emit_token!(token, pos, bytes, tokens, errors);
                    // tokens.push(token);
                    try_dispatch!(pos + len, bytes, tokens, errors);
                }
            }
        }
        Some(b'*') => {
            len += 1;
            let mut nesting = 1_u32;
            loop {
                let remainder = unsafe { bytes.get_unchecked(usize::from(pos + len)..) };
                match memchr::memchr(b'/', remainder) {
                    // unclosed block comment
                    None => {
                        len += remainder.len() as u32;
                        let span = ByteSpan::new(pos, pos + len);
                        let token = Token::new(TokenKind::BlockComment, span);
                        emit_token!(token, pos, bytes, tokens, errors);
                        // tokens.push(token);
                        errors.push_within_capacity(LexError::BlockComment { span });
                        return;
                    }
                    // closing
                    Some(extra)
                        if remainder.get(extra.saturating_sub(1)).copied() == Some(b'*') =>
                    {
                        nesting -= 1;
                        len += extra as u32 + 1;

                        if nesting == 0 {
                            let span = ByteSpan::new(pos, pos + len);
                            let token = Token::new(TokenKind::BlockComment, span);
                            emit_token!(token, pos, bytes, tokens, errors);
                            // tokens.push(token);
                            try_dispatch!(pos + len, bytes, tokens, errors);
                        }
                    }
                    // opening
                    Some(extra) if remainder.get(extra + 1).copied() == Some(b'*') => {
                        nesting += 1;
                        len += extra as u32 + 2;
                    }
                    // lone `/`
                    Some(extra) => len += extra as u32 + 1,
                }
            }
        }
        Some(_) => {
            let span = ByteSpan::new(pos, pos + len);
            let token = Token::new(TokenKind::Error, span);
            emit_token!(token, pos, bytes, tokens, errors);
            // tokens.push(token);
            errors.push_within_capacity(LexError::UnknownChar { span });
        }
    }
}

macro_rules! single_char_lexer_fn {
    ($name:ident, $kind:expr) => {
        fn $name(pos: BytePos, bytes: &[u8], tokens: &mut Vec<Token>, errors: &mut Vec<LexError>) {
            let span = ByteSpan::new(pos, pos + 1);
            let token = Token::new($kind, span);
            emit_token!(token, pos, bytes, tokens, errors);
            // tokens.push(token);
            try_dispatch!(pos + 1, bytes, tokens, errors);
        }
    };
}

single_char_lexer_fn!(do_lparen, TokenKind::LParen);
single_char_lexer_fn!(do_rparen, TokenKind::RParen);
single_char_lexer_fn!(do_lsquare, TokenKind::LSquare);
single_char_lexer_fn!(do_rsquare, TokenKind::RSquare);
single_char_lexer_fn!(do_lcurly, TokenKind::LCurly);
single_char_lexer_fn!(do_rcurly, TokenKind::RCurly);
single_char_lexer_fn!(do_comma, TokenKind::Comma);
single_char_lexer_fn!(do_semicolon, TokenKind::Semicolon);
single_char_lexer_fn!(do_colon, TokenKind::Colon);
single_char_lexer_fn!(do_dot, TokenKind::Dot);
single_char_lexer_fn!(do_at, TokenKind::At);
single_char_lexer_fn!(do_pipe, TokenKind::Pipe);

fn do_dash_or_thin_arrow(
    pos: BytePos,
    bytes: &[u8],
    tokens: &mut Vec<Token>,
    errors: &mut Vec<LexError>,
) {
    match bytes.get(usize::from(pos + 1)) {
        Some(b'>') => {
            let span = ByteSpan::new(pos, pos + 2);
            let token = Token::new(TokenKind::ThinArrow, span);
            emit_token!(token, pos, bytes, tokens, errors);
            // tokens.push(token);
            try_dispatch!(pos + 2, bytes, tokens, errors);
        }
        Some(_) => {
            let span = ByteSpan::new(pos, pos + 1);
            let token = Token::new(TokenKind::Error, span);
            emit_token!(token, pos, bytes, tokens, errors);
            // tokens.push(token);
            errors.push_within_capacity(LexError::UnknownChar { span });
            try_dispatch!(pos + 1, bytes, tokens, errors);
        }
        None => {
            let span = ByteSpan::new(pos, pos + 1);
            let token = Token::new(TokenKind::Error, span);
            emit_token!(token, pos, bytes, tokens, errors);
            // tokens.push(token);
            errors.push_within_capacity(LexError::UnknownChar { span });
        }
    }
}

fn do_eq_or_fat_arrow(
    pos: BytePos,
    bytes: &[u8],
    tokens: &mut Vec<Token>,
    errors: &mut Vec<LexError>,
) {
    let mut len = 1_u32;
    match bytes.get(usize::from(pos + len)) {
        Some(b'>') => {
            len += 1;
            let span = ByteSpan::new(pos, pos + len);
            let token = Token::new(TokenKind::FatArrow, span);
            emit_token!(token, pos, bytes, tokens, errors);
            // tokens.push(token);
            try_dispatch!(pos + len, bytes, tokens, errors);
        }
        Some(_) => {
            let span = ByteSpan::new(pos, pos + len);
            let token = Token::new(TokenKind::Eq, span);
            emit_token!(token, pos, bytes, tokens, errors);
            // tokens.push(token);
            try_dispatch!(pos + len, bytes, tokens, errors);
        }
        None => {
            let span = ByteSpan::new(pos, pos + len);
            let token = Token::new(TokenKind::Eq, span);
            emit_token!(token, pos, bytes, tokens, errors);
            // tokens.push(token);
        }
    }
}

fn do_ident_or_keyword(
    pos: BytePos,
    bytes: &[u8],
    tokens: &mut Vec<Token>,
    errors: &mut Vec<LexError>,
) {
    #[inline(always)]
    fn classify_identifier(_pos: BytePos, bytes: &[u8]) -> TokenKind {
        match bytes {
            b"def" => TokenKind::KwDef,
            b"else" => TokenKind::KwElse,
            b"false" => TokenKind::KwFalse,
            b"fun" => TokenKind::KwFun,
            b"if" => TokenKind::KwIf,
            b"let" => TokenKind::KwLet,
            b"match" => TokenKind::KwMatch,
            b"then" => TokenKind::KwThen,
            b"true" => TokenKind::KwTrue,
            b"_" => TokenKind::Underscore,
            _ => TokenKind::Ident,
        }
    }

    let mut len = 1_u32;
    loop {
        match bytes.get(usize::from(pos + len)) {
            Some(b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_' | b'-') => len += 1,
            Some(_) => {
                let span = ByteSpan::new(pos, pos + len);
                let str = unsafe { bytes.get_unchecked(std::ops::Range::from(span)) };
                let kind = classify_identifier(pos, str);
                let token = Token::new(kind, span);
                emit_token!(token, pos, bytes, tokens, errors);
                // tokens.push(token);
                try_dispatch!(pos + len, bytes, tokens, errors);
            }
            None => {
                let span = ByteSpan::new(pos, pos + len);
                let str = unsafe { bytes.get_unchecked(std::ops::Range::from(span)) };
                let kind = classify_identifier(pos, str);
                let token = Token::new(kind, span);
                emit_token!(token, pos, bytes, tokens, errors);
                // tokens.push(token);
                return;
            }
        }
    }
}

fn do_ident_or_raw_ident(
    pos: BytePos,
    bytes: &[u8],
    tokens: &mut Vec<Token>,
    errors: &mut Vec<LexError>,
) {
    let mut len = 1_u32;
    let mut kind = TokenKind::Ident;
    match bytes.get(usize::from(pos + len)) {
        Some(b'#') => {
            len += 1;
            kind = TokenKind::RawIdent;
        }
        Some(b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_' | b'-') => len += 1,
        Some(_) => {
            let span = ByteSpan::new(pos, pos + len);
            let token = Token::new(TokenKind::Ident, span);
            emit_token!(token, pos, bytes, tokens, errors);
            // tokens.push(token);
            try_dispatch!(pos + len, bytes, tokens, errors);
        }
        None => {
            let span = ByteSpan::new(pos, pos + len);
            let token = Token::new(TokenKind::Ident, span);
            emit_token!(token, pos, bytes, tokens, errors);
            // tokens.push(token);
            return;
        }
    }
    loop {
        match bytes.get(usize::from(pos + len)) {
            Some(b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_' | b'-') => len += 1,
            Some(_) => {
                let span = ByteSpan::new(pos, pos + len);
                let token = Token::new(kind, span);
                emit_token!(token, pos, bytes, tokens, errors);
                // tokens.push(token);
                try_dispatch!(pos + len, bytes, tokens, errors);
            }
            None => {
                let span = ByteSpan::new(pos, pos + len);
                let token = Token::new(kind, span);
                emit_token!(token, pos, bytes, tokens, errors);
                // tokens.push(token);
                return;
            }
        }
    }
}

fn do_dec_int(pos: BytePos, bytes: &[u8], tokens: &mut Vec<Token>, errors: &mut Vec<LexError>) {
    let mut len = 1_u32;
    loop {
        match bytes.get(usize::from(pos + len)) {
            Some(b'0'..=b'9' | b'a'..=b'f' | b'A'..=b'F' | b'_') => len += 1,
            Some(_) => {
                let span = ByteSpan::new(pos, pos + len);
                let token = Token::new(TokenKind::DecInt, span);
                emit_token!(token, pos, bytes, tokens, errors);
                // tokens.push(token);
                try_dispatch!(pos + len, bytes, tokens, errors);
            }
            None => {
                let span = ByteSpan::new(pos, pos + len);
                let token = Token::new(TokenKind::DecInt, span);
                emit_token!(token, pos, bytes, tokens, errors);
                // tokens.push(token);
                return;
            }
        }
    }
}

fn do_int(pos: BytePos, bytes: &[u8], tokens: &mut Vec<Token>, errors: &mut Vec<LexError>) {
    let mut len = 1_u32;
    let mut kind = TokenKind::DecInt;
    match bytes.get(usize::from(pos + len)) {
        Some(b'b' | b'B') => {
            kind = TokenKind::BinInt;
            len += 1;
        }
        Some(b'x' | b'X') => {
            kind = TokenKind::HexInt;
            len += 1;
        }
        Some(b'0'..=b'9' | b'a'..=b'f' | b'A'..=b'F' | b'_') => len += 1,
        Some(_) => {
            let span = ByteSpan::new(pos, pos + len);
            let token = Token::new(kind, span);
            emit_token!(token, pos, bytes, tokens, errors);
            // tokens.push(token);
            try_dispatch!(pos + len, bytes, tokens, errors);
        }
        None => {
            let span = ByteSpan::new(pos, pos + len);
            let token = Token::new(TokenKind::DecInt, span);
            emit_token!(token, pos, bytes, tokens, errors);
            // tokens.push(token);
            return;
        }
    }
    loop {
        match bytes.get(usize::from(pos + len)) {
            Some(b'0'..=b'9' | b'a'..=b'f' | b'A'..=b'F' | b'_') => len += 1,
            Some(_) => {
                let span = ByteSpan::new(pos, pos + len);
                let token = Token::new(kind, span);
                emit_token!(token, pos, bytes, tokens, errors);
                // tokens.push(token);
                try_dispatch!(pos + len, bytes, tokens, errors);
            }
            None => {
                let span = ByteSpan::new(pos, pos + len);
                let token = Token::new(kind, span);
                emit_token!(token, pos, bytes, tokens, errors);
                // tokens.push(token);
                return;
            }
        }
    }
}

const DISPATCH_TABLE: [LexerFn; 256] = {
    const fn set_range(mut table: LexerTable, start: u8, end: u8, value: LexerFn) -> LexerTable {
        let mut c = start;
        while c <= end {
            table[c as usize] = value;
            c += 1;
        }
        table
    }

    const fn set_table(mut table: LexerTable, at: u8, value: LexerFn) -> LexerTable {
        table[at as usize] = value;
        table
    }

    let table = [do_unknown_ascii_byte as LexerFn; 256];
    let table = set_range(table, 0b1100_0000, 0b1101_1111, do_unknown_2byte_char);
    let table = set_range(table, 0b1110_0000, 0b1110_1111, do_unknown_3byte_char);
    let table = set_range(table, 0b1111_0000, 0b1111_0111, do_unknown_4byte_char);

    let table = set_table(table, b' ', do_ascii_whitespace);
    let table = set_table(table, b'\t', do_ascii_whitespace);
    let table = set_table(table, b'\n', do_ascii_whitespace);

    let table = set_table(table, b'/', do_line_comment_or_block_comment);

    let table = set_table(table, b'(', do_lparen);
    let table = set_table(table, b')', do_rparen);
    let table = set_table(table, b'[', do_lsquare);
    let table = set_table(table, b']', do_rsquare);
    let table = set_table(table, b'{', do_lcurly);
    let table = set_table(table, b'}', do_rcurly);
    let table = set_table(table, b',', do_comma);
    let table = set_table(table, b';', do_semicolon);
    let table = set_table(table, b':', do_colon);
    let table = set_table(table, b'.', do_dot);
    let table = set_table(table, b'@', do_at);
    let table = set_table(table, b'|', do_pipe);

    let table = set_table(table, b'-', do_dash_or_thin_arrow);
    let table = set_table(table, b'=', do_eq_or_fat_arrow);

    let table = set_range(table, b'a', b'z', do_ident_or_keyword);
    let table = set_range(table, b'A', b'Z', do_ident_or_keyword);
    let table = set_table(table, b'_', do_ident_or_keyword);
    let table = set_table(table, b'r', do_ident_or_raw_ident);

    let table = set_range(table, b'0', b'9', do_dec_int);
    let table = set_table(table, b'0', do_int);

    table
};

pub fn lex(src: &string32::Str32, tokens: &mut Vec<Token>, errors: &mut Vec<LexError>) {
    let bytes = src.as_bytes();
    let pos = BytePos::new(0);
    try_dispatch!(pos, bytes, tokens, errors);
}

#[cold]
fn resize_vectors(pos: BytePos, bytes: &[u8], tokens: &mut Vec<Token>, errors: &mut Vec<LexError>) {
    tokens.reserve(1);
    errors.reserve(1);
    try_dispatch!(pos, bytes, tokens, errors);
}
