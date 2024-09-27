use pion_core::semantics::Type;

mod expr;
mod pat;
mod stmt;

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

        let mut got = String::new();
        pion_core::print::type_ann_expr(&mut got, &expr, &r#type).unwrap();
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
        expr("true", expect!["true : Bool"]);
        expr("false", expect!["false : Bool"]);
    }

    #[test]
    fn int_expr() {
        expr("123", expect!["123 : Int"]);

        expr(
            "123-",
            expect![[r#"
                #error : Int
                Diagnostic { severity: Error, code: None, message: "Invalid integer literal: invalid digit found in string", labels: [Label { style: Primary, file_id: 0, range: 0..4, message: "" }], notes: [] }
            "#]],
        );

        expr(
            "999999999999999999999999999",
            expect![[r#"
                #error : Int
                Diagnostic { severity: Error, code: None, message: "Invalid integer literal: number too large to fit in target type", labels: [Label { style: Primary, file_id: 0, range: 0..27, message: "" }], notes: [] }
            "#]],
        );
    }

    #[test]
    fn char_expr() { expr(r"'a'", expect![[r"'\0' : Char"]]); }

    #[test]
    fn string_expr() {
        expr(r#""hello world""#, expect![[r#""hello world" : String"#]]);

        expr(
            r#" "hello \t world \n\r" "#,
            expect![[r#""hello \t world \n\r" : String"#]],
        );

        expr(
            r#"let s: String = "the famous \"hello world\" string"; s "#,
            expect![[r#"(let s : String = "the famous \"hello world\" string"; _#0) : String"#]],
        );

        expr(
            r#"let ugly-regex: String = "\\\\."; ugly-regex "#,
            expect![[r#"(let ugly-regex : String = "\\\\."; _#0) : String"#]],
        );

        expr(
            r#" "  "#,
            expect![[r#"
            #error : String
            Diagnostic { severity: Error, code: None, message: "Unterminated string literal", labels: [Label { style: Primary, file_id: 0, range: 1..4, message: "" }], notes: [] }
        "#]],
        );

        expr(
            r#" "  \""#,
            expect![[r#"
                #error : String
                Diagnostic { severity: Error, code: None, message: "Unterminated string literal", labels: [Label { style: Primary, file_id: 0, range: 1..6, message: "" }], notes: [] }
            "#]],
        );

        expr(
            r#" " \a ""#,
            expect![[r#"
                #error : String
                Diagnostic { severity: Error, code: None, message: "Unknown escape character: `a`", labels: [Label { style: Primary, file_id: 0, range: 3..5, message: "" }], notes: [] }
            "#]],
        );

        expr(
            r#" " \🦀 ""#,
            expect![[r#"
                #error : String
                Diagnostic { severity: Error, code: None, message: "Unknown escape character: `🦀`", labels: [Label { style: Primary, file_id: 0, range: 3..8, message: "" }], notes: [] }
            "#]],
        );

        expr(
            r#" " \🇬🇧 ""#,
            expect![[r#"
                #error : String
                Diagnostic { severity: Error, code: None, message: "Unknown escape character: `🇬`", labels: [Label { style: Primary, file_id: 0, range: 3..8, message: "" }], notes: [] }
            "#]],
        );
    }

    #[test]
    fn prim_var() {
        expr("Type", expect!["Type : Type"]);
        expr("Bool", expect!["Bool : Type"]);
        expr("Int", expect!["Int : Type"]);
        expr("Char", expect!["Char : Type"]);
        expr("String", expect!["String : Type"]);
        expr("Unit", expect!["Unit : Type"]);
        expr("unit", expect!["unit : Unit"]);
    }

    #[test]
    fn local_var() {
        expr(
            "hello-world",
            expect![[r#"
                #error : #error
                Diagnostic { severity: Error, code: None, message: "Unbound variable: `hello-world`", labels: [Label { style: Primary, file_id: 0, range: 0..11, message: "" }], notes: [] }
            "#]],
        );
    }

    #[test]
    fn let_expr() { expr("let x: Int = 5; x", expect!["(let x : Int = 5; _#0) : Int"]); }

    #[test]
    fn fun_expr() {
        expr("fun() => 5", expect!["5 : Int"]);
        expr(
            "fun(_: Int) => 5",
            expect!["(fun(_ : Int) => 5) : forall(_ : Int) -> Int"],
        );
        expr(
            "fun(x: Int) => x",
            expect!["(fun(x : Int) => _#0) : forall(x : Int) -> Int"],
        );
        expr(
            "fun(x: Int, _: Bool) => x",
            expect![
                "(fun(x : Int) => fun(_ : Bool) => _#1) : forall(x : Int) -> forall(_ : Bool) -> \
                 Int"
            ],
        );
    }

    #[test]
    fn fun_type() {
        expr("forall() -> Type", expect!["Type : Type"]);
        expr(
            "forall(A: Type, a: A) -> A",
            expect!["(forall(A : Type) -> forall(a : _#0) -> _#1) : Type"],
        );
    }

    #[test]
    fn fun_arrow() {
        expr("Int -> Bool", expect!["(forall(_ : Int) -> Bool) : Type"]);
        expr(
            "Int -> Bool -> Type",
            expect!["(forall(_ : Int) -> forall(_ : Bool) -> Type) : Type"],
        );
    }

    #[test]
    fn fun_call() {
        expr(
            "let f: Int -> Int = fun(x: Int) => x; f(1)",
            expect!["(let f : forall(_ : Int) -> Int = fun(x : Int) => _#0; _#0) : Int"],
        );
        expr(
            "let f: Int = 5; f(1)",
            expect![[r#"
                (let f : Int = 5; #error) : #error
                Diagnostic { severity: Error, code: None, message: "Expected a function", labels: [Label { style: Primary, file_id: 0, range: 16..17, message: "" }], notes: ["Help: the type of the callee is Int"] }
            "#]],
        );
        expr(
            "let f: Int -> Int = fun(x) => x; f(1, 2)",
            expect![[r#"
                (let f : forall(_ : Int) -> Int = fun(x : Int) => _#0; #error) : #error
                Diagnostic { severity: Error, code: None, message: "Called function with too many arguments", labels: [Label { style: Primary, file_id: 0, range: 33..34, message: "" }], notes: ["Help: the function expects 1 arguments, but received 2", "Help: the type of the callee is forall(_ : Int) -> Int"] }
            "#]],
        );
    }

    #[test]
    fn synth_do_expr() {
        expr("do {}", expect!["do {} : Unit"]);
        expr("do {5}", expect!["do {5} : Int"]);
        expr("do {5;}", expect!["do {let 5; } : Unit"]);
        expr(
            "do {let x: Int = 5; x}",
            expect!["do {x : Int = 5; _#0} : Int"],
        );
    }

    #[test]
    fn check_do_expr() {
        expr(
            "do {} : Int",
            expect![[r#"
                do {} : Int
                Diagnostic { severity: Error, code: None, message: "Type mismatch: expected `Int`, found `Unit`", labels: [Label { style: Primary, file_id: 0, range: 0..5, message: "" }], notes: [] }
            "#]],
        );
        expr(
            "do { false } : Int",
            expect![[r#"
                do {#error} : Int
                Diagnostic { severity: Error, code: None, message: "Type mismatch: expected `Int`, found Bool", labels: [Label { style: Primary, file_id: 0, range: 5..10, message: "" }], notes: [] }
            "#]],
        );
    }
}
