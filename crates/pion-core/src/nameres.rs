use std::collections::HashSet;
use std::hash;

use nohash::IntMap;
use pion_hir::syntax::{self as hir, Ident};
use pion_utils::identity::Identity;
use pion_utils::symbol::Symbol;

pub fn nameres_expr<'hir>(expr: &'hir hir::Expr<'hir>) {
    let mut ctx = Ctx::default();
    ctx.process_expr(expr);
    ctx.finish();
}

pub type NameDefMap<'hir> = IntMap<NameUser<'hir>, NameDefiner>;

pub type NameDefiner = Ident;

#[derive(Debug, Copy, Clone)]
pub enum NameUser<'hir> {
    IdentExpr(Identity<&'hir hir::Expr<'hir>>),
    RecordExprShorthand(Identity<&'hir Ident>),
}

impl<'hir> hash::Hash for NameUser<'hir> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        match self {
            NameUser::IdentExpr(ptr) => ptr.hash(state),
            NameUser::RecordExprShorthand(ptr) => ptr.hash(state),
        }
    }
}

impl<'hir> PartialEq for NameUser<'hir> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::IdentExpr(l0), Self::IdentExpr(r0)) => l0 == r0,
            (Self::RecordExprShorthand(l0), Self::RecordExprShorthand(r0)) => l0 == r0,
            _ => false,
        }
    }
}

impl<'hir> Eq for NameUser<'hir> {}

impl<'hir> nohash::IsEnabled for NameUser<'hir> {}

#[derive(Default)]
struct Ctx<'hir> {
    name_def_map: NameDefMap<'hir>,
    env: Vec<NameDefiner>,
    unreferenced_names: HashSet<NameDefiner>,
    diagnostics: Vec<Diagnostic>,
}

impl<'hir> Ctx<'hir> {
    fn finish(mut self) -> (NameDefMap<'hir>, Vec<Diagnostic>) {
        for ident in self.unreferenced_names {
            self.diagnostics.push(Diagnostic::UnusedName { ident });
        }
        (self.name_def_map, self.diagnostics)
    }

    fn lookup_symbol(&self, symbol: Symbol, from: usize) -> Option<NameDefiner> {
        self.env[from..]
            .iter()
            .rev()
            .find(|ident| ident.symbol == symbol)
            .copied()
    }

    fn use_name(&mut self, ident: Ident, user: NameUser<'hir>) {
        match self.lookup_symbol(ident.symbol, 0) {
            None => todo!("unbound indentifier"),
            Some(introducer) => {
                self.name_def_map.insert(user, introducer);
                self.unreferenced_names.remove(&ident);
            }
        }
    }

    fn define_name(&mut self, ident: Ident, from: usize) {
        match self.lookup_symbol(ident.symbol, from) {
            Some(first_definition) => {
                self.diagnostics.push(Diagnostic::DuplicateName {
                    first_ident: first_definition,
                    duplicate_ident: ident,
                });
            }
            None => {
                self.unreferenced_names.insert(ident);
                self.env.push(ident);
            }
        }
    }

    fn process_expr(&mut self, expr: &'hir hir::Expr<'hir>) {
        match expr {
            hir::Expr::Ident(.., ident) => {
                self.use_name(*ident, NameUser::IdentExpr(Identity(expr)));
            }
            hir::Expr::RecordLit(.., fields) => {
                fields.iter().for_each(|field| match &field.expr {
                    Some(expr) => self.process_expr(expr),
                    None => self.use_name(
                        field.name,
                        NameUser::RecordExprShorthand(Identity(&field.name)),
                    ),
                });
            }

            hir::Expr::Let(.., (pat, r#type, init, body)) => {
                if let Some(r#type) = r#type.as_ref() {
                    self.process_expr(r#type);
                }
                self.process_expr(init);
                let len = self.env.len();
                self.process_pat(pat, len);
                self.process_expr(body);
                self.env.truncate(len);
            }
            hir::Expr::RecordType(.., fields) => {
                let len = self.env.len();
                for field in *fields {
                    let hir::TypeField { name, r#type } = field;
                    self.process_expr(r#type);
                    self.define_name(*name, len);
                }
                self.env.truncate(len);
            }
            hir::Expr::FunType(.., params, body) | hir::Expr::FunLit(.., params, body) => {
                let len = self.env.len();
                for param in *params {
                    if let Some(r#type) = param.r#type.as_ref() {
                        self.process_expr(r#type);
                    }
                    self.process_pat(&param.pat, len);
                }
                self.process_expr(body);
                self.env.truncate(len);
            }
            hir::Expr::Match(.., scrut, cases) => {
                self.process_expr(scrut);
                for case in *cases {
                    let hir::MatchCase { pat, guard, expr } = case;
                    let len = self.env.len();
                    self.process_pat(pat, len);
                    if let Some(guard) = guard.as_ref() {
                        self.process_expr(guard);
                    }
                    self.process_expr(expr);
                    self.env.truncate(len);
                }
            }
            _ => expr.walk(|expr| self.process_expr(expr)),
        }
    }

    fn process_pat(&mut self, pat: &'hir hir::Pat<'hir>, len: usize) {
        match pat {
            hir::Pat::Ident(.., ident) => self.define_name(*ident, len),
            hir::Pat::RecordLit(.., fields) => fields.iter().for_each(|field| match &field.pat {
                Some(pat) => self.process_pat(pat, len),
                None => self.define_name(field.name, len),
            }),
            hir::Pat::Or(.., pats) => {
                let (head, _) = pats.split_first();
                self.process_pat(head, len);
                // TODO: how to handle the tail?
            }
            _ => pat.walk(|pat| self.process_pat(pat, len)),
        }
    }
}

pub enum Diagnostic {
    DuplicateName {
        first_ident: Ident,
        duplicate_ident: Ident,
    },
    UnusedName {
        ident: Ident,
    },
}
