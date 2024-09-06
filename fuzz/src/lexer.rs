#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|text: &str| {
    let tokens = pion_lexer::lex(text);
    std::hint::black_box(tokens.count());
});
