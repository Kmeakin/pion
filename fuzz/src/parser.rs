#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|text: &str| {
    let tokens = pion_lexer::lex(text);
    let bump = bumpalo::Bump::new();
    let (expr, _diagnostics) = pion_parser::parse_expr(0, tokens, &bump);
    std::hint::black_box(expr);
});
