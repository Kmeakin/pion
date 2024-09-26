## Context free syntax

```text
<Expr> ::=
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
    | "let" <Pat> "=" <Expr> ";" <Expr>
    | <Expr> ":" <Expr>

<Pat> ::=
    | "_"
    | <Ident>
    | "(" <Pat> ")"
    | <Pat> ":" <Expr>

<FunArg> ::= <Plicity> <Expr>
<FunParam> ::= <Plicity> <Pat>
<Plicity> ::= "@"?
```
