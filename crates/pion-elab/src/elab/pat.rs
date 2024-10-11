use pion_core::semantics::Type;
use pion_core::symbol::Symbol;
use pion_surface::syntax::{self as surface, Located};

use super::{Check, Synth};
use crate::env::MetaSource;
use crate::Elaborator;

pub type SynthPat<'core> = Synth<'core, Pat<'core>>;
pub type CheckPat<'core> = Check<Pat<'core>>;

#[derive(Debug, Copy, Clone)]
pub enum Pat<'core> {
    Error,
    Wildcard,
    Var(Symbol<'core>),
}

impl<'core> Pat<'core> {
    pub fn name(&self) -> Option<Symbol<'core>> {
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
            surface::Pat::Underscore => {
                let source = MetaSource::PatType(pat.range, None);
                let r#type = self.push_unsolved_type(source);
                (Pat::Wildcard, r#type)
            }
            surface::Pat::Var(name) => {
                let name = self.bump.alloc_str(name);
                let name = self.interner.intern(name);
                let source = MetaSource::PatType(pat.range, Some(name));
                let r#type = self.push_unsolved_type(source);
                (Pat::Var(name), r#type)
            }
            surface::Pat::Paren(pat) => self.synth_pat(*pat),
            surface::Pat::TypeAnnotation(pat, r#type) => {
                let r#type = self.check_expr(*r#type, &Type::TYPE);
                let type_value = self.eval_env().eval(&r#type);
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
        match self.unify_env().unify(from, to) {
            Ok(()) => pat.data,
            Err(err) => {
                // Unification may have unblocked some metas
                let from = self.elim_env().subst_metas(from);
                let to = self.elim_env().subst_metas(to);
                self.diagnostic(
                    pat.range,
                    err.to_diagnostic(&self.quote_env().quote(&from), &self.quote_env().quote(&to)),
                );
                Pat::Error
            }
        }
    }
}
