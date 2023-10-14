use std::sync::Arc;

use dashmap::DashMap;

use super::*;

// REASON: keep all lifetimes explicit for clarity
#[allow(clippy::needless_lifetimes)]
pub fn elab_def<'surface, 'hir, 'core>(
    bump: &'core bumpalo::Bump,
    item_env: Arc<ItemEnv<'hir, 'core>>,
    def: &'hir pion_hir::syntax::Def<'surface, 'hir>,
) -> (Def<'core>, ElabResult<'hir, 'core, ()>) {
    let mut ctx = ElabCtx::new(bump, &def.syntax_map, item_env);

    let (expr, r#type) = match &def.r#type {
        None => {
            let Synth(expr, r#type) = ctx.synth_expr(def.expr);
            let r#type = ctx.quote_env().quote(&r#type);

            (expr, r#type)
        }
        Some(r#type) => {
            let Check(r#type) = ctx.check_expr(r#type, &Type::TYPE);
            let type_value = ctx.eval_env().eval(&r#type);
            let Check(expr) = ctx.check_expr(def.expr, &type_value);

            (expr, r#type)
        }
    };
    let expr = ctx.zonk_env(bump).zonk(&expr);
    let r#type = ctx.zonk_env(bump).zonk(&r#type);

    let def = Def {
        name: def.name,
        r#type,
        expr,
    };

    let res = ctx.finish_with(());
    (def, res)
}

// REASON: keep all lifetimes explicit for clarity
#[allow(clippy::needless_lifetimes)]
pub fn elab_expr<'surface, 'hir, 'core>(
    bump: &'core bumpalo::Bump,
    syntax_map: &'hir pion_hir::syntax::LocalSyntaxMap<'surface, 'hir>,
    expr: &'hir pion_hir::syntax::Expr<'hir>,
) -> ElabResult<'hir, 'core, (ZonkedExpr<'core>, ZonkedExpr<'core>)> {
    let mut ctx = ElabCtx::new(bump, syntax_map, Arc::new(ItemEnv::default()));

    let Synth(expr, r#type) = ctx.synth_expr(expr);
    let r#type = ctx.quote_env().quote(&r#type);

    let expr = ctx.zonk_env(bump).zonk(&expr);
    let r#type = ctx.zonk_env(bump).zonk(&r#type);
    ctx.finish_with((expr, r#type))
}

// REASON: keep all lifetimes explicit for clarity
#[allow(clippy::needless_lifetimes)]
pub fn elab_module<'surface, 'hir, 'core>(
    bump: &'core bumpalo::Bump,
    module: &'hir pion_hir::syntax::Module<'surface, 'hir>,
) -> (
    Vec<(Item<'core>, ElabResult<'hir, 'core, ()>)>,
    Vec<diagnostics::ElabDiagnostic>,
) {
    // find duplicate items
    // TODO(perf): use hashmap?
    let mut diagnostics: Vec<diagnostics::ElabDiagnostic> = Vec::new();
    let mut items: Vec<(Symbol, &pion_hir::syntax::Item)> = Vec::new();

    for item in &module.items {
        match item {
            pion_hir::syntax::Item::Def(def) => {
                match items.iter().find(|(name, _)| def.name == *name) {
                    None => items.push((def.name, item)),
                    Some((_, first_item)) => {
                        diagnostics.push(diagnostics::ElabDiagnostic::DuplicateItem {
                            name: def.name,
                            first_span: first_item.span(),
                            duplicate_span: def.name_span,
                        });
                    }
                }
            }
        }
    }

    let item_env = ItemEnv::with_capacity(items.len());

    for (name, _) in &items {
        item_env.insert(*name, None);
    }

    let item_env = Arc::new(item_env);
    let mut item_results = Vec::new();

    for (name, item) in &items {
        match item {
            pion_hir::syntax::Item::Def(def) => {
                let (def, res) = elab_def(bump, item_env.clone(), def);
                item_env.insert(*name, Some((def, res.clone())));
                item_results.push((Item::Def(def), res));
            }
        }
    }

    (item_results, diagnostics)
}

pub type ItemEnv<'hir, 'core> = DashMap<Symbol, Option<(Def<'core>, ElabResult<'hir, 'core, ()>)>>;
