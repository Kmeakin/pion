use std::fmt::Write;

use expect_test::{expect, Expect};

use super::*;

#[track_caller]
#[allow(clippy::needless_pass_by_value, reason = "It's only a test")]
fn assert_lex(text: &str, expected: Expect) {
    let mut got = String::with_capacity(text.len());
    for token in lex(text) {
        writeln!(got, "{:?} {:?} {:?}", token.kind, token.range, token.text()).unwrap();
    }
    expected.assert_eq(got.trim_end());
}

#[test]
fn empty() { assert_lex("", expect![""]); }

#[test]
fn unknown() {
    assert_lex(
        "\u{00}\u{7F}\u{80}",
        expect![[r#"
            Unknown 0..1 "\0"
            Unknown 1..2 "\u{7f}"
            Unknown 2..4 "\u{80}""#]],
    );
}

#[test]
fn whitespace() {
    assert_lex(
        "\t\n\x0B\x0C\r ",
        expect![[r#"Whitespace 0..6 "\t\n\u{b}\u{c}\r ""#]],
    );
    assert_lex(
        "\t\n\x0B\x0C\r\u{0085}\u{200E}\u{200F}\u{2028}\u{2029}",
        expect![[r#"Whitespace 0..19 "\t\n\u{b}\u{c}\r\u{85}\u{200e}\u{200f}\u{2028}\u{2029}""#]],
    );
}

#[test]
fn line_comment() {
    assert_lex(
        "// line comment",
        expect![[r#"LineComment 0..15 "// line comment""#]],
    );
    assert_lex(
        "// line comment\u{000A}",
        expect![[r#"
            LineComment 0..15 "// line comment"
            Whitespace 15..16 "\n""#]],
    );
    assert_lex(
        "// line comment\u{000B}",
        expect![[r#"
            LineComment 0..15 "// line comment"
            Whitespace 15..16 "\u{b}""#]],
    );
    assert_lex(
        "// line comment\u{000C}",
        expect![[r#"
            LineComment 0..15 "// line comment"
            Whitespace 15..16 "\u{c}""#]],
    );
    assert_lex(
        "// line comment\u{000D}",
        expect![[r#"
            LineComment 0..15 "// line comment"
            Whitespace 15..16 "\r""#]],
    );
    assert_lex(
        "// line comment\u{00085}",
        expect![[r#"
            LineComment 0..15 "// line comment"
            Whitespace 15..17 "\u{85}""#]],
    );
    assert_lex(
        "// line comment\u{2028}",
        expect![[r#"
            LineComment 0..15 "// line comment"
            Whitespace 15..18 "\u{2028}""#]],
    );
    assert_lex(
        "// line comment\u{2029}",
        expect![[r#"
            LineComment 0..15 "// line comment"
            Whitespace 15..18 "\u{2029}""#]],
    );
}

#[test]
fn delimiter() {
    assert_lex(
        "()[]{}",
        expect![[r#"
            LParen 0..1 "("
            RParen 1..2 ")"
            LSquare 2..3 "["
            RSquare 3..4 "]"
            LCurly 4..5 "{"
            RCurly 5..6 "}""#]],
    );
}

#[test]
fn punct() {
    assert_lex(
        "!#$%&*+,-./:;<=>?@\\^_`|~",
        expect![[r##"
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
            DoubleArrow 14..16 "=>"
            Punct('?') 16..17 "?"
            Punct('@') 17..18 "@"
            Punct('\\') 18..19 "\\"
            Punct('^') 19..20 "^"
            Punct('_') 20..21 "_"
            Punct('`') 21..22 "`"
            Punct('|') 22..23 "|"
            Punct('~') 23..24 "~""##]],
    );
    assert_lex(
        "_-",
        expect![[r#"
            Punct('_') 0..1 "_"
            Punct('-') 1..2 "-""#]],
    );
    assert_lex("->", expect![[r#"SingleArrow 0..2 "->""#]]);
    assert_lex("=>", expect![[r#"DoubleArrow 0..2 "=>""#]]);
}

#[test]
fn ident() {
    assert_lex("abcd1234", expect![[r#"Ident 0..8 "abcd1234""#]]);

    // Leading '-' at start of ident is interpreted as Punct
    assert_lex(
        "-abcd1234",
        expect![[r#"
            Punct('-') 0..1 "-"
            Ident 1..9 "abcd1234""#]],
    );

    assert_lex("a-", expect![[r#"Ident 0..2 "a-""#]]);
    assert_lex("a-b", expect![[r#"Ident 0..3 "a-b""#]]);
    assert_lex("_a", expect![[r#"Ident 0..2 "_a""#]]);

    assert_lex(
        "_-",
        expect![[r#"
            Punct('_') 0..1 "_"
            Punct('-') 1..2 "-""#]],
    );

    assert_lex(
        "-_",
        expect![[r#"
            Punct('-') 0..1 "-"
            Punct('_') 1..2 "_""#]],
    );

    assert_lex("__", expect![[r#"Ident 0..2 "__""#]]);
    assert_lex("λ", expect![[r#"Ident 0..2 "λ""#]]);
}

#[test]
fn reserved_ident() {
    assert_lex(
        "do else false forall fun if let match motive then true",
        expect![[r#"
            KwDo 0..2 "do"
            Whitespace 2..3 " "
            KwElse 3..7 "else"
            Whitespace 7..8 " "
            KwFalse 8..13 "false"
            Whitespace 13..14 " "
            KwForall 14..20 "forall"
            Whitespace 20..21 " "
            KwFun 21..24 "fun"
            Whitespace 24..25 " "
            KwIf 25..27 "if"
            Whitespace 27..28 " "
            KwLet 28..31 "let"
            Whitespace 31..32 " "
            KwMatch 32..37 "match"
            Whitespace 37..38 " "
            KwMotive 38..44 "motive"
            Whitespace 44..45 " "
            KwThen 45..49 "then"
            Whitespace 49..50 " "
            KwTrue 50..54 "true""#]],
    );
}

#[test]
fn number() {
    assert_lex(
        "123_456 0x123_456 0b123_456 -123 +123",
        expect![[r#"
            Int 0..7 "123_456"
            Whitespace 7..8 " "
            Int 8..17 "0x123_456"
            Whitespace 17..18 " "
            Int 18..27 "0b123_456"
            Whitespace 27..28 " "
            Punct('-') 28..29 "-"
            Int 29..32 "123"
            Whitespace 32..33 " "
            Punct('+') 33..34 "+"
            Int 34..37 "123""#]],
    );
}

#[test]
fn char() {
    assert_lex("'a'", expect![[r#"Char 0..3 "'a'""#]]);
    assert_lex("'abc'", expect![[r#"Char 0..5 "'abc'""#]]);
    assert_lex("'abc", expect![[r#"Char 0..4 "'abc""#]]);
    assert_lex(r"'abc\'def'", expect![[r#"Char 0..10 "'abc\\'def'""#]]);
    assert_lex(r"'abc\'", expect![[r#"Char 0..6 "'abc\\'""#]]);
    assert_lex(r"'abc\", expect![[r#"Char 0..5 "'abc\\""#]]);
    assert_lex(
        r"'abc\\'def'",
        expect![[r#"
            Char 0..7 "'abc\\\\'"
            Ident 7..10 "def"
            Char 10..11 "'""#]],
    );
}

#[test]
fn string() {
    assert_lex(r#""""#, expect![[r#"String 0..2 "\"\"""#]]);
    assert_lex(r#""a""#, expect![[r#"String 0..3 "\"a\"""#]]);
    assert_lex(r#""abc""#, expect![[r#"String 0..5 "\"abc\"""#]]);
    assert_lex(r#""abc"#, expect![[r#"String 0..4 "\"abc""#]]);
    assert_lex(r#""abc\"def"#, expect![[r#"String 0..9 "\"abc\\\"def""#]]);
    assert_lex(r#""abc\""#, expect![[r#"String 0..6 "\"abc\\\"""#]]);
    assert_lex(r#""abc\"#, expect![[r#"String 0..5 "\"abc\\""#]]);
    assert_lex(
        r#""abc\\"def""#,
        expect![[r#"
            String 0..7 "\"abc\\\\\""
            Ident 7..10 "def"
            String 10..11 "\"""#]],
    );
}
