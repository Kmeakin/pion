## Context free syntax

```text
<File> ::= <Stmt>*

<Expr> ::=
    | "_"
    | <Ident>
    | "true" | "false"
    | <Number>
    | <Char>
    | <String>
    | "(" <Expr> ")"
    | <Expr> "(" <FunArg>,* ")"
    | <Expr> "->" <Expr>
    | "forall" ( <FunParam>","* ")" "->" <Expr>
    | "fun" "(" <FunParam>","* ")" "=>" <Expr>
    | "do" "{" <Stmt>* <Expr>? "}"
    | <Expr> ":" <Expr>

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
    | "(" <Pat> ")"
    | <Pat> ":" <Expr>

<FunArg> ::= <Plicity> <Expr>
<FunParam> ::= <Plicity> <Pat>
<Plicity> ::= "@"?
```
