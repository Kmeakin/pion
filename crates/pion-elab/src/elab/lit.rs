use std::borrow::Cow;
use std::str::FromStr;

use codespan_reporting::diagnostic::Diagnostic;
use pion_core::semantics::Type;
use pion_core::syntax::*;
use pion_surface::syntax as surface;
use pion_surface::syntax::Located;
use text_size::{TextRange, TextSize};

use super::Synth;
use crate::Elaborator;

impl<'core> Elaborator<'core> {
    pub fn synth_lit(
        &mut self,
        lit: Located<surface::Lit>,
    ) -> Synth<'core, Result<Lit<'core>, ()>> {
        match lit.data {
            surface::Lit::Bool(b) => (Ok(Lit::Bool(b)), Type::BOOL),
            surface::Lit::Int(text) => {
                let text = Located::new(lit.range, text);
                let n = self.synth_int(text).map(Lit::Int);
                (n, Type::INT)
            }
            surface::Lit::Char(text) => {
                let text = Located::new(lit.range, text);
                let n = self.synth_char(text).map(Lit::Char);
                (n, Type::CHAR)
            }
            surface::Lit::String(text) => {
                let text = Located::new(lit.range, text);
                let n = self.synth_string(text).map(Lit::String);
                (n, Type::STRING)
            }
        }
    }

    fn synth_int(&mut self, text: Located<&str>) -> Result<u32, ()> {
        let range = text.range;
        let text = match text.data.contains('_') {
            false => Cow::Borrowed(text.data),
            true => Cow::Owned(text.data.replace('_', "")),
        };

        let res = match () {
            () if text.starts_with("0b") || text.starts_with("0B") => {
                u32::from_str_radix(&text[2..], 16)
            }
            () if text.starts_with("0o") || text.starts_with("0O") => {
                u32::from_str_radix(&text[2..], 16)
            }
            () if text.starts_with("0x") || text.starts_with("0X") => {
                u32::from_str_radix(&text[2..], 16)
            }
            () => u32::from_str(&text),
        };

        match res {
            Ok(n) => Ok(n),
            Err(error) => {
                self.diagnostic(
                    range,
                    Diagnostic::error().with_message(format!("Invalid integer literal: {error}")),
                );
                Err(())
            }
        }
    }

    fn synth_string(&mut self, text: Located<&str>) -> Result<&'core str, ()> {
        let range = text.range;
        let text = text.data;

        let text = text.strip_prefix('"').expect("Guaranteed by lexer");

        let (text, mut terminated) = match text.strip_suffix('"') {
            Some(text) => (text, true),
            None => (text, false),
        };

        let mut error = false;
        let text = match text.contains('\\') {
            false => Cow::Borrowed(text),
            true => {
                let mut result = String::with_capacity(text.len());
                let mut chars = text.char_indices();

                while let Some((idx1, c)) = chars.next() {
                    match c {
                        '\\' => {
                            let Some((idx2, c)) = chars.next() else {
                                terminated = false;
                                break;
                            };
                            match c {
                                'n' => result.push('\n'),
                                'r' => result.push('\r'),
                                't' => result.push('\t'),
                                '\"' => result.push('"'),
                                '\'' => result.push('\''),
                                '\\' => result.push('\\'),
                                c => {
                                    error = true;
                                    let range = range + TextSize::from(1); // add 1 to skip past the leading '"'
                                    let idx1 = TextSize::try_from(idx1).unwrap();
                                    let idx2 = TextSize::try_from(idx2 + c.len_utf8()).unwrap();

                                    debug_assert_eq!(
                                        text[TextRange::new(idx1, idx2)],
                                        format!("\\{c}")
                                    );

                                    let range =
                                        TextRange::new(range.start() + idx1, range.start() + idx2);
                                    self.diagnostic(
                                        range,
                                        Diagnostic::error().with_message(format!(
                                            "Unknown escape character: `{c}`"
                                        )),
                                    );
                                }
                            }
                        }
                        c => result.push(c),
                    }
                }
                Cow::Owned(result)
            }
        };

        if !terminated {
            error = true;
            self.diagnostic(
                range,
                Diagnostic::error().with_message("Unterminated string literal"),
            );
        }

        if error {
            return Err(());
        }

        Ok(self.bump.alloc_str(&text))
    }

    fn synth_char(&mut self, text: Located<&str>) -> Result<char, ()> {
        let range = text.range;
        let text = text.data;
        let text = text.strip_prefix('\'').expect("Guaranteed by lexer");

        let mut chars = text.chars();

        let mut next = || match chars.next() {
            None => {
                self.diagnostic(
                    range,
                    Diagnostic::error().with_message("Unterminated character literal"),
                );
                Err(())
            }
            Some(c) => Ok(c),
        };

        match next()? {
            '\'' => {
                self.diagnostic(
                    range,
                    Diagnostic::error().with_message("Empty character literal"),
                );
                Err(())
            }
            '\\' => match next()? {
                'n' => Ok('\n'),
                'r' => Ok('\r'),
                't' => Ok('\t'),
                '\"' => Ok('\"'),
                '\'' => Ok('\''),
                '\\' => Ok('\\'),
                c => {
                    self.diagnostic(
                        range,
                        Diagnostic::error()
                            .with_message(format!("Unknown escape character: `{c}`")),
                    );
                    Err(())
                }
            },
            c => match next()? {
                '\'' => Ok(c),
                _ => {
                    self.diagnostic(
                        range,
                        Diagnostic::error().with_message("Character literal too long"),
                    );
                    Err(())
                }
            },
        }
    }
}
