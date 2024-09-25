use codespan_reporting::diagnostic::Diagnostic;
use pion_core::semantics::equality::AlphaEq;
use pion_core::semantics::Type;
use pion_interner::InternedStr;
use pion_surface::syntax::{self as surface, Located};

use super::{Check, Synth};
use crate::Elaborator;

pub type SynthPat<'core> = Synth<'core, Pat<'core>>;
pub type CheckPat<'core> = Check<Pat<'core>>;

#[derive(Debug, Copy, Clone)]
pub enum Pat<'core> {
    Error,
    Wildcard,
    Var(InternedStr<'core>),
}

impl<'core> Pat<'core> {
    pub fn name(&self) -> Option<InternedStr<'core>> {
        match self {
            Pat::Var(name) => Some(*name),
            _ => None,
        }
    }
}

impl<'text, 'surface, 'core> Elaborator<'core> {
    pub fn synth_pat(&mut self, pat: Located<&surface::Pat<'text, 'surface>>) -> SynthPat<'core> {
        match pat.data {
            surface::Pat::Error => (Pat::Error, Type::ERROR),
            // TODO: insert metavariables
            surface::Pat::Underscore => (Pat::Wildcard, Type::ERROR),
            surface::Pat::Var(name) => {
                let name = self.bump.alloc_str(name);
                let name = self.interner.intern(name);
                (Pat::Var(name), Type::ERROR)
            }
            surface::Pat::Paren(pat) => self.synth_pat(*pat),
            surface::Pat::TypeAnnotation { pat, r#type } => {
                let r#type = self.check_expr(*r#type, &Type::TYPE);
                let type_value = self.eval_expr(&r#type);
                let pat = self.check_pat(*pat, &type_value);
                (pat, type_value)
            }
        }
    }

    pub fn check_pat(
        &mut self,
        pat: Located<&surface::Pat<'text, 'surface>>,
        expected: &Type<'core>,
    ) -> CheckPat<'core> {
        match pat.data {
            surface::Pat::Error => Pat::Error,
            surface::Pat::Underscore => Pat::Wildcard,
            surface::Pat::Var(name) => {
                let name = self.bump.alloc_str(name);
                let name = self.interner.intern(name);
                Pat::Var(name)
            }
            surface::Pat::Paren(pat) => self.check_pat(*pat, expected),
            surface::Pat::TypeAnnotation { .. } => self.synth_and_coerce_pat(pat, expected),
        }
    }

    fn synth_and_coerce_pat(
        &mut self,
        pat: Located<&surface::Pat<'text, 'surface>>,
        expected: &Type<'core>,
    ) -> CheckPat<'core> {
        let pat_range = pat.range;
        let (pat, r#type) = self.synth_pat(pat);
        self.coerce_pat(Located::new(pat_range, pat), &r#type, expected)
    }

    fn coerce_pat(
        &mut self,
        pat: Located<Pat<'core>>,
        from: &Type<'core>,
        to: &Type<'core>,
    ) -> CheckPat<'core> {
        match from.alpha_eq(to) {
            true => pat.data,
            false => {
                self.diagnostic(
                    pat.range,
                    Diagnostic::error()
                        .with_message(format!("Type mismatch: expected `{to:?}`, found {from:?}")),
                );
                Pat::Error
            }
        }
    }
}
