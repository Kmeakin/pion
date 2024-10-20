## Lexical syntax

```text
<Token> ::= <Trivia> | <Delimiter> | <Atom>

<Trivia> ::= <Whitespace> | <LineComment>
<Whitespace> ::= <WhitespaceChar>+
<WhitespaceChar> ::=
    | U+0009 (horizontal tab, '\t')
    | U+000A (line feed, '\n')
    | U+000B (vertical tab)
    | U+000C (form feed)
    | U+000D (carriage return, '\r')
    | U+0020 (space, ' ')
    | U+0085 (next line)
    | U+200E (left-to-right mark)
    | U+200F (right-to-left mark)
    | U+2028 (line separator)
    | U+2029 (paragraph separator)

<LineComment> ::= "//" (not <LineTerminator>)*
<LineTerminator> ::=
    | U+000A (line feed, '\n')
    | U+000B (vertical tab)
    | U+000C (form feed)
    | U+000D (carriage return, '\r')
    | U+0085 (next line)
    | U+2028 (line separator)
    | U+2029 (paragraph separator)

<Delimiter> ::= '(' | ')' | '{' | '}' | '[' | ']'

<Atom> ::= <Punct> | <Ident> | <Literal>

<Punct> ::=
    | '!' | '#' | '$' | '%' | '&' | '*' | '+' | ',' | '-' | '.' | '/' | ':'
    | ';' | '<' | '=' | '>' | '?' | '@' | '\' | '^' | '_' | '`' | '|' | '~'

<Ident> ::=
    | <XID_Start> (<XID_Continue> | '-')*
    | '_' <XID_Continue> (<XID_Continue> | '-')*

<Literal> ::= <Int> | <Char> | <String>

<Int> ::= <BinInt> | <OctInt> | <DecInt> | <HexInt>
<BinInt> ::= "0b" | "0B" ('0' ..= '1' | '_')+
<OctInt> ::= "0o" | "0O" ('0' ..= '7' | '_')+
<DecInt> ::=             ('0' ..= '9' | '_')+
<HexInt> ::= "0x" | "0X" ('0' ..= '9' | 'a' ..= 'f' | 'A' ..= 'F' | '_')+

<Char> ::= ''' <CharContent> '''
<CharContent> ::= <SingleCharElement> | <AsciiEscape>
<SingleCharElement> ::= Any character other than `\t`, `\n`, `\r` ''' or '\'

<String> ::= '"' <StringContent> '"'
<StringContent> ::= <SingleStringElement> | <AsciiEscape>
<SingleStringElement> ::= Any character other than '"' or '\'
```
