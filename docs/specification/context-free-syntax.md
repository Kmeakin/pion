## Context free syntax

```text
<File> ::= <Stmt>*

<Expr> ::=
    | "_"
    | <Ident>
    | <Literal>
    | "(" <Expr> ")"
    | <Expr> "(" <FunArg>,* ")"
    | <Expr> "->" <Expr>
    | "forall" ( <FunParam>","* ")" "->" <Expr>
    | "fun" "(" <FunParam>","* ")" "=>" <Expr>
    | "do" "{" <Stmt>* <Expr>? "}"
    | "if" <Expr> "then" <Expr> "else" <Expr>
    | "match" <Expr> "{" <MatchCase>,* "}"
    | <Expr> ":" <Expr>

MatchCase ::=
    | <Pat> "=>" <Expr>

<Stmt> ::=
    | "let" <Pat> "=" <Expr> ";"
    | <Expr> ";"
    | <Command> ";"

<Command> ::=
    | "#check" <Expr>
    | "#eval" <Expr>

<Pat> ::=
    | "_"
    | <Ident>
    | <Literal>
    | "(" <Pat> ")"
    | <Pat> ":" <Expr>

<Literal> ::=
    | <Bool>
    | <Int>
    | <Char>
    | <String>

<FunArg> ::= <Plicity> <Expr>
<FunParam> ::= <Plicity> <Pat>
<Plicity> ::= "@"?
```
