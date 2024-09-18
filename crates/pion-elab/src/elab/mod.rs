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
        expr(
            r#""hello world""#,
            expect![[r#""\"hello world\"" : String"#]],
        );
    }

    #[test]
    fn prim_var() {
        expr("Type", expect!["Type : Type"]);
        expr("Bool", expect!["Bool : Type"]);
        expr("Int", expect!["Int : Type"]);
        expr("Char", expect!["Char : Type"]);
        expr("String", expect!["String : Type"]);
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
        expr("fun() 5", expect!["5 : Int"]);
        expr(
            "fun(_: Int) 5",
            expect!["(fun(_ : Int) 5) : forall(_ : Int) Int"],
        );
        expr(
            "fun(x: Int) x",
            expect!["(fun(x : Int) _#0) : forall(x : Int) Int"],
        );
        expr(
            "fun(x: Int, _: Bool) x",
            expect!["(fun(x : Int) fun(_ : Bool) _#1) : forall(x : Int) forall(_ : Bool) Int"],
        );
    }

    #[test]
    fn fun_type() {
        expr("forall() Type", expect!["Type : Type"]);
        expr(
            "forall(A: Type, a: A) A",
            expect!["(forall(A : Type) forall(a : _#0) _#1) : Type"],
        );
    }

    #[test]
    fn fun_arrow() {
        expr("Int -> Bool", expect!["(forall(_ : Int) Bool) : Type"]);
        expr(
            "Int -> Bool -> Type",
            expect!["(forall(_ : Int) forall(_ : Bool) Type) : Type"],
        );
    }

    #[test]
    fn fun_call() {
        expr(
            "let f: Int -> Int = fun(x: Int) x; f(1)",
            expect!["(let f : forall(_ : Int) Int = fun(x : Int) _#0; _#0) : Int"],
        );
        expr(
            "let f: Int = 5; f(1)",
            expect![[r#"
                (let f : Int = 5; #error) : #error
                Diagnostic { severity: Error, code: None, message: "Expected a function", labels: [Label { style: Primary, file_id: 0, range: 16..17, message: "" }], notes: ["Help: the type of the callee is Int"] }
            "#]],
        );
        expr(
            "let f: Int -> Int = fun(x) x; f(1, 2)",
            expect![[r#"
                (let f : forall(_ : Int) Int = fun(x : Int) _#0; #error) : #error
                Diagnostic { severity: Error, code: None, message: "Called function with too many arguments", labels: [Label { style: Primary, file_id: 0, range: 30..31, message: "" }], notes: ["Help: the function expects 1 arguments, but received 2", "Help: the type of the callee is forall(_ : Int) Int"] }
            "#]],
        );
    }
}
