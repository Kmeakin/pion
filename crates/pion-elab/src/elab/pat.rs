use pion_core::env::EnvLen;
use pion_core::semantics::Type;
use pion_core::symbol::Symbol;
use pion_core::syntax::{Expr, LetBinding, Lit};
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
    Lit(Lit<'core>),
}

impl<'core> Pat<'core> {
    pub fn name(&self) -> Option<Symbol<'core>> {
        match self {
            Pat::Var(name) => Some(*name),
            _ => None,
        }
    }

    pub const fn is_wildcard(&self) -> bool {
        matches!(self, Self::Error | Self::Wildcard | Self::Var(_))
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
                let name = self.intern(name);
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
            surface::Pat::Lit(lit) => {
                let lit = Located::new(pat.range, *lit);
                let (lit, r#type) = self.synth_lit(lit);
                let pat = match lit {
                    Ok(lit) => Pat::Lit(lit),
                    Err(()) => Pat::Error,
                };
                (pat, r#type)
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
                let name = self.intern(name);
                Pat::Var(name)
            }
            surface::Pat::Paren(pat) => self.check_pat(*pat, expected),
            surface::Pat::TypeAnnotation(..) | surface::Pat::Lit(..) => {
                self.synth_and_coerce_pat(pat, expected)
            }
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

    pub(super) fn destruct_pat(
        &mut self,
        pat: &Pat<'core>,
        expr: &Expr<'core>,
        r#type: &Type<'core>,
        toplevel_param: bool,
    ) -> Vec<LetBinding<'core, Expr<'core>>> {
        fn recur<'core>(
            ctx: &mut Elaborator<'core>,
            pat: &Pat<'core>,
            expr: &Expr<'core>,
            r#type: &Type<'core>,
            bindings: &mut Vec<LetBinding<'core, Expr<'core>>>,
            toplevel_param: bool,
        ) {
            match pat {
                Pat::Error | Pat::Wildcard | Pat::Lit(_) => {}
                Pat::Var(..) if toplevel_param => {}
                Pat::Var(..) => {
                    let name = pat.name();
                    let r#type = ctx
                        .quote_env()
                        .quote_offset(r#type, EnvLen::from(bindings.len()));
                    let expr = expr.shift(ctx.bump, EnvLen::from(bindings.len()));
                    bindings.push(LetBinding::new(name, r#type, expr));
                }
                #[cfg(false)]
                Pat::RecordLit(pat_fields) => {
                    let r#type = ctx.elim_env().update_metas(r#type);
                    let Type::RecordType(mut telescope) = r#type else {
                        unreachable!("expected record type, got {type:?}")
                    };
                    for (pat_name, pat) in *pat_fields {
                        let (telescope_name, r#type, update_telescope) =
                            ctx.elim_env().split_telescope(&mut telescope).unwrap();
                        debug_assert_eq!(*pat_name, telescope_name);

                        let expr = Expr::RecordProj(ctx.bump.alloc(*expr), *pat_name);

                        recur(ctx, pat, &expr, &r#type, bindings, false);
                        update_telescope(ctx.env.locals.next_var());
                    }
                }
                #[cfg(false)]
                Pat::Or(pats) => {
                    recur(ctx, &pats[0], expr, r#type, bindings, toplevel_param);
                }
            }
        }

        let mut bindings = Vec::new();
        recur(self, pat, expr, r#type, &mut bindings, toplevel_param);
        bindings
    }
}
