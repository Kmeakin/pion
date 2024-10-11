#![no_main]

use libfuzzer_sys::fuzz_target;
use pion_elab::Elaborator;

fuzz_target!(|text: &str| {
    let file_id = 0;
    let bump = bumpalo::Bump::new();
    let mut interner = pion_core::symbol::Interner::default();

    let tokens = pion_surface::lex::lex(text);
    let (expr, _diagnostics) = pion_surface::parse::parse_expr(file_id, tokens, &bump);

    let mut elaborator = Elaborator::new(&bump, &mut interner, file_id);
    let (expr, r#type) = elaborator.synth_expr(expr.as_ref());
    let diagnostics = elaborator.finish();
    std::hint::black_box((expr, r#type, diagnostics));
});
