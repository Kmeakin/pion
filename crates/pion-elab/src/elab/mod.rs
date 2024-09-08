use pion_core::semantics::Type;

mod expr;
mod pat;

pub type Synth<'core, T> = (T, Type<'core>);
pub type Check<T> = T;

#[cfg(test)]
mod tests {
    use std::fmt::Write;

    use expect_test::{expect, Expect};

    use crate::Elaborator;

    #[allow(clippy::needless_pass_by_value, reason = "It's only a test")]
    #[track_caller]
    fn expr(src: &str, expected: Expect) {
        let file_id = 0;
        let bump = bumpalo::Bump::new();
        let mut interner = pion_interner::Interner::default();

        let tokens = pion_parser::lex(src);

        let (surface, _diagnostics) = pion_parser::parse_expr(file_id, tokens, &bump);
        let mut elaborator = Elaborator::new(&bump, &mut interner, file_id);
        let (expr, r#type) = elaborator.synth_expr(surface.as_ref());
        let diagnostics = elaborator.finish();

        let mut got = format!("{expr:?} : {type:?}");
        if !diagnostics.is_empty() {
            got.push('\n');
            for diagnostic in diagnostics {
                writeln!(got, "{diagnostic:?}").unwrap();
            }
        }

        expected.assert_eq(&got);
    }

    #[test]
    fn bool_expr() {
        expr("true", expect!["true : PrimVar(Bool)"]);
        expr("false", expect!["false : PrimVar(Bool)"]);
    }

    #[test]
    fn int_expr() {
        expr("123", expect!["123 : PrimVar(Int)"]);

        expr(
            "123-",
            expect![[r#"
                Error : PrimVar(Int)
                Diagnostic { severity: Error, code: None, message: "Invalid integer literal: invalid digit found in string", labels: [Label { style: Primary, file_id: 0, range: 0..4, message: "" }], notes: [] }
            "#]],
        );

        expr(
            "999999999999999999999999999",
            expect![[r#"
                Error : PrimVar(Int)
                Diagnostic { severity: Error, code: None, message: "Invalid integer literal: number too large to fit in target type", labels: [Label { style: Primary, file_id: 0, range: 0..27, message: "" }], notes: [] }
            "#]],
        );
    }

    #[test]
    fn char_expr() { expr(r"'a'", expect![[r"'\0' : PrimVar(Char)"]]); }

    #[test]
    fn string_expr() {
        expr(
            r#""hello world""#,
            expect![[r#""\"hello world\"" : PrimVar(String)"#]],
        );
    }

    #[test]
    fn prim_var() {
        expr("Type", expect!["PrimVar(Type) : PrimVar(Type)"]);
        expr("Bool", expect!["PrimVar(Bool) : PrimVar(Type)"]);
        expr("Int", expect!["PrimVar(Int) : PrimVar(Type)"]);
        expr("Char", expect!["PrimVar(Char) : PrimVar(Type)"]);
        expr("String", expect!["PrimVar(String) : PrimVar(Type)"]);
    }

    #[test]
    fn local_var() {
        expr(
            "hello-world",
            expect![[r#"
        Error : Error
        Diagnostic { severity: Error, code: None, message: "Unbound variable: `hello-world`", labels: [Label { style: Primary, file_id: 0, range: 0..11, message: "" }], notes: [] }
    "#]],
        );
    }

    #[test]
    fn let_expr() {
        expr(
            "let x: Int = 5; x",
            expect![[
                r#"Let { binding: LetBinding { name: Some("x"), type: PrimVar(Int), rhs: 5 }, body: LocalVar(0) } : PrimVar(Int)"#
            ]],
        );
    }

    #[test]
    fn fun_expr() {
        expr("fun() 5", expect!["5 : PrimVar(Int)"]);
        expr(
            "fun(_: Int) 5",
            expect![
                "fun(FunParam { plicity: Explicit, name: None, type: PrimVar(Int) }) 5 : \
                 forall(FunParam { plicity: Explicit, name: None, type: PrimVar(Int) }) Closure { \
                 local_values: SharedEnv { elems: [] }, body: PrimVar(Int) }"
            ],
        );
        expr(
            "fun(x: Int) x",
            expect![[
                r#"fun(FunParam { plicity: Explicit, name: Some("x"), type: PrimVar(Int) }) LocalVar(0) : forall(FunParam { plicity: Explicit, name: Some("x"), type: PrimVar(Int) }) Closure { local_values: SharedEnv { elems: [] }, body: PrimVar(Int) }"#
            ]],
        );
        expr(
            "fun(x: Int, _: Bool) x",
            expect![[
                r#"fun(FunParam { plicity: Explicit, name: Some("x"), type: PrimVar(Int) }) fun(FunParam { plicity: Explicit, name: None, type: PrimVar(Bool) }) LocalVar(1) : forall(FunParam { plicity: Explicit, name: Some("x"), type: PrimVar(Int) }) Closure { local_values: SharedEnv { elems: [] }, body: forall(FunParam { plicity: Explicit, name: None, type: PrimVar(Bool) }) PrimVar(Int) }"#
            ]],
        );
    }

    #[test]
    fn fun_type() {
        expr("forall() Type", expect!["PrimVar(Type) : PrimVar(Type)"]);
        expr(
            "forall(A: Type, a: A) A",
            expect![[
                r#"forall(FunParam { plicity: Explicit, name: Some("A"), type: PrimVar(Type) }) forall(FunParam { plicity: Explicit, name: Some("a"), type: LocalVar(0) }) LocalVar(1) : PrimVar(Type)"#
            ]],
        );
    }

    #[test]
    fn fun_arrow() {
        expr(
            "Int -> Bool",
            expect![
                "forall(FunParam { plicity: Explicit, name: None, type: PrimVar(Int) }) \
                 PrimVar(Bool) : PrimVar(Type)"
            ],
        );
        expr(
            "Int -> Bool -> Type",
            expect![
                "forall(FunParam { plicity: Explicit, name: None, type: PrimVar(Int) }) \
                 forall(FunParam { plicity: Explicit, name: None, type: PrimVar(Bool) }) \
                 PrimVar(Type) : PrimVar(Type)"
            ],
        );
    }

    #[test]
    fn fun_call() {
        expr(
            "let f: Int -> Int = fun(x: Int) x; f(1)",
            expect![[
                r#"Let { binding: LetBinding { name: Some("f"), type: forall(FunParam { plicity: Explicit, name: None, type: PrimVar(Int) }) PrimVar(Int), rhs: fun(FunParam { plicity: Explicit, name: Some("x"), type: PrimVar(Int) }) LocalVar(0) }, body: LocalVar(0) } : PrimVar(Int)"#
            ]],
        );
        expr(
            "let f: Int = 5; f(1)",
            expect![[r#"
                Let { binding: LetBinding { name: Some("f"), type: PrimVar(Int), rhs: 5 }, body: Error } : Error
                Diagnostic { severity: Error, code: None, message: "Expected a function", labels: [Label { style: Primary, file_id: 0, range: 16..17, message: "" }], notes: ["Help: the type of the callee is PrimVar(Int)"] }
            "#]],
        );
        expr(
            "let f: Int -> Int = fun(x) x; f(1, 2)",
            expect![[r#"
                Let { binding: LetBinding { name: Some("f"), type: forall(FunParam { plicity: Explicit, name: None, type: PrimVar(Int) }) PrimVar(Int), rhs: fun(FunParam { plicity: Explicit, name: Some("x"), type: PrimVar(Int) }) LocalVar(0) }, body: Error } : Error
                Diagnostic { severity: Error, code: None, message: "Called function with too many arguments", labels: [Label { style: Primary, file_id: 0, range: 30..31, message: "" }], notes: ["Help: the function expects 1 arguments, but received 2", "Help: the type of the callee is forall(FunParam { plicity: Explicit, name: None, type: PrimVar(Int) }) Closure { local_values: SharedEnv { elems: [] }, body: PrimVar(Int) }"] }
            "#]],
        );
    }
}
