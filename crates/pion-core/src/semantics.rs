use ecow::EcoVec;
use either::*;
use pion_utils::slice_vec::SliceVec;
use pion_utils::symbol::Symbol;

use crate::env::{EnvLen, Level, SharedEnv, SliceEnv, UniqueEnv};
use crate::name::{BinderName, FieldName, LocalName};
use crate::prim::Prim;
use crate::syntax::{
    BoolCases, Closure, Elim, Expr, Head, IntCases, Lit, Plicity, SplitCases, Telescope, Value,
    ZonkedExpr,
};

#[derive(Copy, Clone)]
pub struct ElimEnv<'core, 'env> {
    bump: &'core bumpalo::Bump,
    meta_values: &'env SliceEnv<Option<Value<'core>>>,
    item_values: &'env SliceEnv<Value<'core>>,
}

impl<'core, 'env> ElimEnv<'core, 'env> {
    pub fn new(
        bump: &'core bumpalo::Bump,
        meta_values: &'env SliceEnv<Option<Value<'core>>>,
        item_values: &'env SliceEnv<Value<'core>>,
    ) -> Self {
        Self {
            bump,
            meta_values,
            item_values,
        }
    }

    pub fn eval_env(
        &self,
        local_values: &'env mut SharedEnv<Value<'core>>,
    ) -> EvalEnv<'core, 'env> {
        EvalEnv::new(self.bump, self.meta_values, local_values, self.item_values)
    }

    fn get_meta(&self, var: Level) -> &'env Option<Value<'core>> {
        let value = self.meta_values.get_level(var);
        match value {
            Some(value) => value,
            None => panic!("Unbound meta variable: {var:?}"),
        }
    }

    /// Bring a value up-to-date with any new unification solutions that
    /// might now be present at the head of in the given value.
    pub fn update_metas(&self, value: &Value<'core>) -> Value<'core> {
        let mut forced_value = value.clone();
        while let Value::Stuck(Head::Meta(var), spine) = forced_value {
            match self.get_meta(var) {
                Some(head) => forced_value = self.apply_spine(head.clone(), spine),
                None => return Value::Stuck(Head::Meta(var), spine),
            }
        }
        forced_value
    }

    /// Apply an expression to an elimination spine.
    fn apply_spine(&self, head: Value<'core>, spine: EcoVec<Elim<'core>>) -> Value<'core> {
        (spine.into_iter()).fold(head, |head, elim| match elim {
            Elim::FunApp(plicity, arg) => self.fun_app(plicity, head, arg),
            Elim::FieldProj(name) => self.field_proj(head, name),
            Elim::MatchBool(cases) => self.match_bool(head, cases),
            Elim::MatchInt(cases) => self.match_int(head, cases),
        })
    }

    pub fn fun_app(&self, plicity: Plicity, fun: Value<'core>, arg: Value<'core>) -> Value<'core> {
        match fun {
            Value::Error => Value::Error,
            Value::Stuck(head, mut spine) => {
                spine.push(Elim::FunApp(plicity, arg));
                if let Head::Prim(prim) = head {
                    if let Some(value) = self.apply_prim(prim, spine.as_slice()) {
                        return value;
                    }
                }
                Value::Stuck(head, spine)
            }
            Value::FunLit(.., body) => self.apply_closure(body, arg),
            _ => panic!("Bad fun app: fun={fun:?} arg={arg:?}"),
        }
    }

    pub fn fun_apps(
        &self,
        fun: Value<'core>,
        args: impl IntoIterator<Item = (Plicity, Value<'core>)>,
    ) -> Value<'core> {
        args.into_iter()
            .fold(fun, |fun, (plicity, arg)| self.fun_app(plicity, fun, arg))
    }

    #[allow(clippy::unused_self)]
    fn apply_prim(&self, prim: Prim, args: &[Elim<'core>]) -> Option<Value<'core>> {
        #![allow(non_snake_case)]

        macro_rules! prim_rules {
            ($($prim:ident($($args:pat),+) => $rhs:expr,)*) => {
                match (prim, args) {
                    $(
                        (Prim::$prim, [$(Elim::FunApp(_, $args)),*]) => Some($rhs),
                    )*
                    _ => None,
                }
            };
        }

        prim_rules! {
            add(Value::Lit(Lit::Int(x)), Value::Lit(Lit::Int(y))) => Value::int(x.wrapping_add(*y)),
            sub(Value::Lit(Lit::Int(x)), Value::Lit(Lit::Int(y))) => Value::int(x.wrapping_sub(*y)),
            mul(Value::Lit(Lit::Int(x)), Value::Lit(Lit::Int(y))) => Value::int(x.wrapping_mul(*y)),
            eq(Value::Lit(Lit::Int(x)), Value::Lit(Lit::Int(y))) => Value::bool(x == y),
            ne(Value::Lit(Lit::Int(x)), Value::Lit(Lit::Int(y))) => Value::bool(x != y),
            lt(Value::Lit(Lit::Int(x)), Value::Lit(Lit::Int(y))) => Value::bool(x < y),
            gt(Value::Lit(Lit::Int(x)), Value::Lit(Lit::Int(y))) => Value::bool(x > y),
            lte(Value::Lit(Lit::Int(x)), Value::Lit(Lit::Int(y))) => Value::bool(x <= y),
            gte(Value::Lit(Lit::Int(x)), Value::Lit(Lit::Int(y))) => Value::bool(x >= y),
            bool_rec(_p, Value::Lit(Lit::Bool(cond)), then, r#else) => (if *cond { then } else { r#else }).clone(),
            subst(_a, _p, _x, _y, _refl, on_refl) => on_refl.clone(),
            fix(A, B, f, x) => {
                let A = A.clone();
                let B = B.clone();
                let f = f.clone();
                let x = x.clone();

                // fix @A @B f x  = f (fix @A @B f) x
                self.fun_apps(f.clone(), [(Plicity::Explicit, self.fun_apps(Value::prim(Prim::fix), [(Plicity::Implicit, A), (Plicity::Implicit, B), (Plicity::Explicit, f)])), (Plicity::Explicit, x)])
            },
        }
    }

    #[allow(clippy::unused_self)]
    // REASON: makes `field_proj` consistent with the other beta-reduction functions
    pub fn field_proj(&self, head: Value<'core>, name: FieldName) -> Value<'core> {
        match head {
            Value::Error => Value::Error,
            Value::Stuck(head, mut spine) => {
                spine.push(Elim::FieldProj(name));
                Value::Stuck(head, spine)
            }
            Value::RecordLit(value_fields) => {
                match (value_fields.iter()).find(|(potential_name, _)| *potential_name == name) {
                    Some((_, value)) => value.clone(),
                    None => {
                        panic!("Bad record proj: field `{name}` not found in `{value_fields:?}`")
                    }
                }
            }
            _ => panic!("Bad record proj: {head:?}.{name}"),
        }
    }

    pub fn match_bool(&self, scrut: Value<'core>, mut cases: BoolCases<'core>) -> Value<'core> {
        match scrut {
            Value::Error => Value::Error,
            Value::Lit(Lit::Bool(true)) => {
                return self
                    .eval_env(&mut cases.local_values)
                    .eval(&cases.pattern_cases[0]);
            }
            Value::Lit(Lit::Bool(false)) => {
                return self
                    .eval_env(&mut cases.local_values)
                    .eval(&cases.pattern_cases[1]);
            }
            Value::Stuck(head, mut spine) => {
                spine.push(Elim::MatchBool(cases));
                Value::Stuck(head, spine)
            }
            _ => panic!("Bad scrut match: {scrut:?} {cases:?}"),
        }
    }

    pub fn match_int(&self, scrut: Value<'core>, mut cases: IntCases<'core, u32>) -> Value<'core> {
        match scrut {
            Value::Error => Value::Error,
            Value::Lit(Lit::Int(lit)) => {
                for (pat_lit, expr) in cases.pattern_cases {
                    if lit == *pat_lit {
                        return self.eval_env(&mut cases.local_values).eval(expr);
                    }
                }
                match cases.default_case {
                    Some(expr) => self.eval_env(&mut cases.local_values).eval(expr),
                    None => panic!("Bad scrut match: inexhaustive cases"),
                }
            }
            Value::Stuck(head, mut spine) => {
                spine.push(Elim::MatchInt(cases));
                Value::Stuck(head, spine)
            }
            _ => panic!("Bad scrut match: {scrut:?} {cases:?}"),
        }
    }

    pub fn apply_closure(&self, mut closure: Closure<'core>, value: Value<'core>) -> Value<'core> {
        closure.local_values.push(value);
        self.eval_env(&mut closure.local_values).eval(closure.expr)
    }

    pub fn split_telescope<'tele>(
        &self,
        telescope: &'tele mut Telescope<'core>,
    ) -> Option<(FieldName, Value<'core>, impl FnOnce(Value<'core>) + 'tele)> {
        let ((name, expr), fields) = telescope.fields.split_first()?;
        let value = self.eval_env(&mut telescope.local_values).eval(expr);
        Some((*name, value, move |prev| {
            telescope.local_values.push(prev);
            telescope.fields = fields;
        }))
    }

    pub fn split_bool_cases(
        &self,
        mut cases: BoolCases<'core>,
    ) -> (Value<'core>, impl FnMut() -> Value<'core> + '_) {
        let [then, r#else] = cases.pattern_cases;
        let then = self.eval_env(&mut cases.local_values).eval(then);
        let r#else = move || self.eval_env(&mut cases.local_values).eval(r#else);
        (then, r#else)
    }

    pub fn split_int_cases(&self, cases: &mut IntCases<'core, u32>) -> SplitCases<'core, u32> {
        match cases.pattern_cases.split_first() {
            Some(((pat, expr), rest)) => {
                cases.pattern_cases = rest;
                SplitCases::Case((*pat, self.eval_env(&mut cases.local_values).eval(expr)))
            }
            None => match cases.default_case {
                Some(expr) => {
                    SplitCases::Default(self.eval_env(&mut cases.local_values).eval(expr))
                }
                None => SplitCases::None,
            },
        }
    }
}

pub struct EvalEnv<'core, 'env> {
    bump: &'core bumpalo::Bump,
    meta_values: &'env SliceEnv<Option<Value<'core>>>,
    local_values: &'env mut SharedEnv<Value<'core>>,
    item_values: &'env SliceEnv<Value<'core>>,
}

impl<'core, 'env> EvalEnv<'core, 'env> {
    pub fn new(
        bump: &'core bumpalo::Bump,
        meta_values: &'env SliceEnv<Option<Value<'core>>>,
        local_values: &'env mut SharedEnv<Value<'core>>,
        item_values: &'env SliceEnv<Value<'core>>,
    ) -> Self {
        Self {
            bump,
            meta_values,
            local_values,
            item_values,
        }
    }

    fn elim_env(&self) -> ElimEnv<'core, '_> {
        ElimEnv::new(self.bump, self.meta_values, self.item_values)
    }

    fn get_meta(&self, var: Level) -> &'env Option<Value<'core>> {
        let value = self.meta_values.get_level(var);
        match value {
            Some(value) => value,
            None => panic!("Unbound meta variable: {var:?}"),
        }
    }

    pub fn eval(&mut self, expr: &Expr<'core>) -> Value<'core> {
        match expr {
            Expr::Error => Value::Error,
            Expr::Lit(lit) => Value::Lit(*lit),
            Expr::Prim(prim) => Value::prim(*prim),
            Expr::Local(.., var) => match self.local_values.get_index(*var) {
                Some(value) => value.clone(),
                None => panic!("Unbound local variable: {var:?}"),
            },
            Expr::Item(.., var) => match self.item_values.get_level(*var) {
                Some(value) => value.clone(),
                None => panic!("Unbound item variable: {var:?}"),
            },
            Expr::Meta(var) => match self.get_meta(*var) {
                Some(value) => value.clone(),
                None => Value::meta(*var),
            },
            Expr::Let(_, (_, init, body)) => {
                let init_value = self.eval(init);
                self.local_values.push(init_value);
                let body_value = self.eval(body);
                self.local_values.pop();
                body_value
            }
            Expr::FunType(plicity, name, (domain, codomain)) => {
                let domain_value = self.eval(domain);
                let codomain = Closure::new(self.local_values.clone(), codomain);
                Value::fun_type(self.bump, *plicity, *name, domain_value, codomain)
            }
            Expr::FunLit(plicity, name, (domain, body)) => {
                let domain_value = self.eval(domain);
                let body = Closure::new(self.local_values.clone(), body);
                Value::fun_lit(self.bump, *plicity, *name, domain_value, body)
            }
            Expr::FunApp(plicity, (fun, arg)) => {
                let fun_value = self.eval(fun);
                let arg_value = self.eval(arg);
                self.elim_env().fun_app(*plicity, fun_value, arg_value)
            }
            Expr::ArrayLit(exprs) => {
                Value::array_lit(self.bump, exprs.iter().map(|expr| self.eval(expr)))
            }
            Expr::RecordType(type_fields) => {
                let telescope = Telescope::new(self.local_values.clone(), type_fields);
                Value::RecordType(telescope)
            }
            Expr::RecordLit(expr_fields) => Value::record_lit(
                self.bump,
                expr_fields
                    .iter()
                    .map(|(name, expr)| (*name, self.eval(expr))),
            ),
            Expr::FieldProj(head, name) => {
                let head = self.eval(head);
                self.elim_env().field_proj(head, *name)
            }
            Expr::MatchBool([scrut, cases @ ..]) => {
                let scrut = self.eval(scrut);
                let cases = BoolCases::new(self.local_values.clone(), cases);
                self.elim_env().match_bool(scrut, cases)
            }
            Expr::MatchInt((scrut, default), cases) => {
                let scrut = self.eval(scrut);
                let cases = IntCases::new(self.local_values.clone(), cases, default);
                self.elim_env().match_int(scrut, cases)
            }
        }
    }
}

pub struct QuoteEnv<'core, 'env> {
    bump: &'core bumpalo::Bump,
    meta_values: &'env SliceEnv<Option<Value<'core>>>,
    item_values: &'env SliceEnv<Value<'core>>,
    local_len: EnvLen,
}

impl<'core, 'env> QuoteEnv<'core, 'env> {
    pub fn new(
        bump: &'core bumpalo::Bump,
        meta_values: &'env SliceEnv<Option<Value<'core>>>,
        item_values: &'env SliceEnv<Value<'core>>,
        local_len: EnvLen,
    ) -> Self {
        Self {
            bump,
            meta_values,
            item_values,
            local_len,
        }
    }

    fn elim_env(&self) -> ElimEnv<'core, 'env> {
        ElimEnv::new(self.bump, self.meta_values, self.item_values)
    }

    fn get_meta(&self, var: Level) -> &'env Option<Value<'core>> {
        match self.meta_values.get_level(var) {
            Some(value) => value,
            None => panic!("Unbound meta variable: {var:?}"),
        }
    }

    pub fn quote_offset(&mut self, value: &Value<'core>, offset: EnvLen) -> Expr<'core> {
        let len = self.local_len();
        self.local_len.append(offset);
        let expr = self.quote(value);
        self.truncate_local(len);
        expr
    }

    /// Quote a [value][Value] back into a [expr][Expr].
    pub fn quote(&mut self, value: &Value<'core>) -> Expr<'core> {
        let value = self.elim_env().update_metas(value);
        match value {
            Value::Error => Expr::Error,
            Value::Lit(lit) => Expr::Lit(lit),
            Value::Stuck(head, spine) => {
                (spine.iter()).fold(self.quote_head(head), |head, elim| match elim {
                    Elim::FunApp(plicity, arg) => {
                        Expr::fun_app(self.bump, *plicity, head, self.quote(arg))
                    }
                    Elim::FieldProj(name) => Expr::field_proj(self.bump, head, *name),
                    Elim::MatchBool(cases) => {
                        let mut cases = cases.clone();
                        let [then, r#else] = cases.pattern_cases;

                        let elim_env = self.elim_env();
                        let then = elim_env.eval_env(&mut cases.local_values).eval(then);
                        let r#else = elim_env.eval_env(&mut cases.local_values).eval(r#else);

                        let then = self.quote(&then);
                        let r#else = self.quote(&r#else);
                        Expr::match_bool(self.bump, head, then, r#else)
                    }
                    Elim::MatchInt(cases) => {
                        let mut cases = cases.clone();
                        let mut pattern_cases = SliceVec::new(self.bump, cases.len());
                        let default = loop {
                            match self.elim_env().split_int_cases(&mut cases) {
                                SplitCases::Case((lit, expr)) => {
                                    pattern_cases.push((lit, self.quote(&expr)));
                                }
                                SplitCases::Default(value) => break Some(self.quote(&value)),
                                SplitCases::None => break None,
                            }
                        };
                        Expr::r#match_int(self.bump, head, pattern_cases.into(), default)
                    }
                })
            }
            Value::FunType(plicity, name, domain, codomain) => {
                let domain = self.quote(domain);
                let codomain = self.quote_closure(codomain);
                Expr::fun_type(self.bump, plicity, name, domain, codomain)
            }
            Value::FunLit(plicity, name, domain, body) => {
                let domain = self.quote(domain);
                let body = self.quote_closure(body);
                Expr::fun_lit(self.bump, plicity, name, domain, body)
            }
            Value::ArrayLit(values) => {
                Expr::array_lit(self.bump, values.iter().map(|value| self.quote(value)))
            }
            Value::RecordType(telescope) => {
                let type_fields = self.quote_telescope(telescope);
                Expr::RecordType(type_fields)
            }
            Value::RecordLit(value_fields) => Expr::record_lit(
                self.bump,
                value_fields
                    .iter()
                    .map(|(name, field_value)| (*name, self.quote(field_value))),
            ),
        }
    }

    /// Quote an [elimination head][Head] back into a [expr][Expr].
    fn quote_head(&mut self, head: Head) -> Expr<'core> {
        match head {
            Head::Item(item) => Expr::Item((), item),
            Head::Prim(prim) => Expr::Prim(prim),
            Head::Local(var) => match self.local_len.level_to_index(var) {
                Some(var) => Expr::Local((), var),
                None => panic!("Unbound local variable: {var:?}"),
            },
            Head::Meta(var) => match self.get_meta(var) {
                Some(value) => self.quote(value),
                None => Expr::Meta(var),
            },
        }
    }

    /// Quote a [closure][Closure] back into an [expr][Expr].
    fn quote_closure(&mut self, closure: Closure<'core>) -> Expr<'core> {
        let var = Value::local(self.local_len.to_level());
        let value = self.elim_env().apply_closure(closure, var);

        self.push_local();
        let expr = self.quote(&value);
        self.pop_local();

        expr
    }

    /// Quote a [telescope][Telescope] back into a slice of [exprs][Expr].
    fn quote_telescope(
        &mut self,
        mut telescope: Telescope<'core>,
    ) -> &'core [(FieldName, Expr<'core>)] {
        let len = self.local_len();
        let mut expr_fields = SliceVec::new(self.bump, telescope.len());

        while let Some((name, value, cont)) = self.elim_env().split_telescope(&mut telescope) {
            let var = Value::local(self.local_len.to_level());
            cont(var);
            expr_fields.push((name, self.quote(&value)));
            self.push_local();
        }

        self.truncate_local(len);
        expr_fields.into()
    }

    fn local_len(&self) -> EnvLen { self.local_len }
    fn truncate_local(&mut self, len: EnvLen) { self.local_len.truncate(len) }

    fn push_local(&mut self) { self.local_len.push(); }
    fn pop_local(&mut self) { self.local_len.pop(); }
}

pub struct ZonkEnv<'core, 'env, 'out> {
    out_bump: &'out bumpalo::Bump,
    inner_bump: &'core bumpalo::Bump,
    meta_values: &'env SliceEnv<Option<Value<'core>>>,
    local_values: &'env mut SharedEnv<Value<'core>>,
    item_values: &'env SliceEnv<Value<'core>>,
    local_names: &'env mut UniqueEnv<BinderName>,
    item_names: &'env SliceEnv<Symbol>,
}

impl<'core, 'env, 'out> ZonkEnv<'core, 'env, 'out> {
    pub fn new(
        out_bump: &'out bumpalo::Bump,
        inner_bump: &'core bumpalo::Bump,
        meta_values: &'env SliceEnv<Option<Value<'core>>>,
        local_values: &'env mut SharedEnv<Value<'core>>,
        item_values: &'env SliceEnv<Value<'core>>,
        local_names: &'env mut UniqueEnv<BinderName>,
        item_names: &'env SliceEnv<Symbol>,
    ) -> Self {
        Self {
            out_bump,
            inner_bump,
            meta_values,
            local_values,
            item_values,
            local_names,
            item_names,
        }
    }

    fn quote_env(&mut self) -> QuoteEnv<'core, '_> {
        QuoteEnv::new(
            self.inner_bump,
            self.meta_values,
            self.item_values,
            self.local_names.len(),
        )
    }

    fn eval_env(&mut self) -> EvalEnv<'core, '_> {
        EvalEnv::new(
            self.inner_bump,
            self.meta_values,
            self.local_values,
            self.item_values,
        )
    }

    fn elim_env(&self) -> ElimEnv<'core, '_> {
        ElimEnv::new(self.inner_bump, self.meta_values, self.item_values)
    }

    fn get_meta(&self, var: Level) -> &'env Option<Value<'core>> {
        let value = self.meta_values.get_level(var);
        match value {
            Some(value) => value,
            None => panic!("Unbound meta variable: {var:?}"),
        }
    }

    pub fn zonk(&mut self, expr: &Expr<'core>) -> ZonkedExpr<'out> {
        match expr {
            Expr::Error => Expr::Error,
            Expr::Lit(lit) => Expr::Lit(*lit),
            Expr::Prim(prim) => Expr::Prim(*prim),
            Expr::Local((), var) => match self.local_names.get_index(*var) {
                Some(BinderName::User(symbol)) => Expr::Local(LocalName::User(*symbol), *var),
                Some(BinderName::Underscore) => Expr::Local(LocalName::Generated, *var),
                None => panic!("Unbound local variable: {var:?}"),
            },
            Expr::Item((), var) => match self.item_names.get_level(*var) {
                Some(symbol) => Expr::Item(*symbol, *var),
                None => panic!("Unbound item variable: {var:?}"),
            },
            // These exprs might be elimination spines with metavariables at
            // their head that need to be unfolded.
            Expr::Meta(..)
            | Expr::FunApp(..)
            | Expr::FieldProj(..)
            | Expr::MatchBool(..)
            | Expr::MatchInt(..) => match self.zonk_meta_var_spines(expr) {
                Left(expr) => expr,
                Right(value) => {
                    let expr = self.quote_env().quote(&value);
                    self.zonk(&expr)
                }
            },
            Expr::Let(name, (r#type, init, body)) => {
                let r#type = self.zonk(r#type);
                let init = self.zonk(init);
                let body = self.zonk_with_binder(*name, body);
                Expr::r#let(self.out_bump, *name, r#type, init, body)
            }
            Expr::FunLit(plicity, name, (domain, body)) => {
                let domain = self.zonk(domain);
                let body = self.zonk_with_binder(*name, body);
                Expr::fun_lit(self.out_bump, *plicity, *name, domain, body)
            }
            Expr::FunType(plicity, name, (domain, codomain)) => {
                let domain = self.zonk(domain);
                let codomain = self.zonk_with_binder(*name, codomain);
                Expr::fun_type(self.out_bump, *plicity, *name, domain, codomain)
            }
            Expr::ArrayLit(exprs) => {
                Expr::array_lit(self.out_bump, exprs.iter().map(|expr| self.zonk(expr)))
            }
            Expr::RecordType(type_fields) => {
                let len = self.local_len();
                let type_fields = self.out_bump.alloc_slice_fill_iter(type_fields.iter().map(
                    |(name, r#type)| {
                        let r#type = self.zonk(r#type);
                        self.push_local(BinderName::from(*name));
                        (*name, r#type)
                    },
                ));
                self.truncate_local(len);
                Expr::RecordType(type_fields)
            }
            Expr::RecordLit(expr_fields) => Expr::record_lit(
                self.out_bump,
                expr_fields
                    .iter()
                    .map(|(name, expr)| (*name, self.zonk(expr))),
            ),
        }
    }

    pub fn zonk_value(&mut self, value: &Value<'core>) -> ZonkedExpr<'out> {
        let value = self.elim_env().update_metas(value);
        match value {
            Value::Error => Expr::Error,
            Value::Lit(lit) => Expr::Lit(lit),
            Value::Stuck(head, spine) => {
                spine
                    .iter()
                    .fold(self.zonk_head(head), |head, elim| match elim {
                        Elim::FunApp(plicity, arg) => {
                            Expr::fun_app(self.out_bump, *plicity, head, self.zonk_value(arg))
                        }
                        Elim::FieldProj(name) => Expr::field_proj(self.out_bump, head, *name),
                        Elim::MatchBool(cases) => {
                            let mut cases = cases.clone();
                            let [then, r#else] = cases.pattern_cases;

                            let elim_env = self.elim_env();
                            let then = elim_env.eval_env(&mut cases.local_values).eval(then);
                            let r#else = elim_env.eval_env(&mut cases.local_values).eval(r#else);

                            let then = self.zonk_value(&then);
                            let r#else = self.zonk_value(&r#else);
                            Expr::match_bool(self.out_bump, head, then, r#else)
                        }
                        Elim::MatchInt(cases) => {
                            let mut cases = cases.clone();
                            let mut pattern_cases = SliceVec::new(self.out_bump, cases.len());
                            let default = loop {
                                match self.elim_env().split_int_cases(&mut cases) {
                                    SplitCases::Case((lit, expr)) => {
                                        pattern_cases.push((lit, self.zonk_value(&expr)));
                                    }
                                    SplitCases::Default(value) => {
                                        break Some(self.zonk_value(&value))
                                    }
                                    SplitCases::None => break None,
                                }
                            };
                            Expr::r#match_int(self.out_bump, head, pattern_cases.into(), default)
                        }
                    })
            }
            Value::FunType(plicity, name, domain, body) => {
                let domain = self.zonk_value(domain);
                let body = self.zonk_closure(name, body);
                Expr::fun_type(self.out_bump, plicity, name, domain, body)
            }
            Value::FunLit(plicity, name, domain, body) => {
                let domain = self.zonk_value(domain);
                let body = self.zonk_closure(name, body);
                Expr::fun_lit(self.out_bump, plicity, name, domain, body)
            }
            Value::ArrayLit(exprs) => Expr::array_lit(
                self.out_bump,
                exprs.iter().map(|value| self.zonk_value(value)),
            ),
            Value::RecordType(mut telescope) => {
                let len = self.local_len();
                let mut expr_fields = SliceVec::new(self.out_bump, telescope.len());
                while let Some((name, value, cont)) =
                    self.elim_env().split_telescope(&mut telescope)
                {
                    let var = Value::local(self.local_len().to_level());
                    cont(var);
                    expr_fields.push((name, self.zonk_value(&value)));
                    self.push_local(BinderName::from(name));
                }

                self.truncate_local(len);
                Expr::RecordType(expr_fields.into())
            }
            Value::RecordLit(fields) => Expr::record_lit(
                self.out_bump,
                fields
                    .iter()
                    .map(|(name, value)| (*name, self.zonk_value(value))),
            ),
        }
    }

    fn zonk_head(&mut self, head: Head) -> ZonkedExpr<'out> {
        match head {
            Head::Prim(prim) => Expr::Prim(prim),
            Head::Local(var) => match self.local_names.get_level(var) {
                Some(BinderName::User(symbol)) => Expr::Local(
                    LocalName::User(*symbol),
                    self.local_len().level_to_index(var).unwrap(),
                ),
                Some(BinderName::Underscore) => Expr::Local(
                    LocalName::Generated,
                    self.local_len().level_to_index(var).unwrap(),
                ),
                None => panic!("Unbound local variable: {var:?}"),
            },
            Head::Item(var) => match self.item_names.get_level(var) {
                Some(symbol) => Expr::Item(*symbol, var),
                None => panic!("Unbound item variable: {var:?}"),
            },
            Head::Meta(var) => match self.get_meta(var) {
                Some(value) => self.zonk_value(value),
                None => Expr::Meta(var),
            },
        }
    }

    fn zonk_with_binder(&mut self, name: BinderName, expr: &Expr<'core>) -> ZonkedExpr<'out> {
        self.push_local(name);
        let ret = self.zonk(expr);
        self.pop_local();
        ret
    }

    fn zonk_closure(&mut self, name: BinderName, closure: Closure<'core>) -> ZonkedExpr<'out> {
        let var = Value::local(self.local_len().to_level());
        let value = self.elim_env().apply_closure(closure, var);

        self.push_local(name);
        let expr = self.zonk_value(&value);
        self.pop_local();

        expr
    }

    /// Unfold elimination spines with solved metavariables at their head.
    pub fn zonk_meta_var_spines(
        &mut self,
        expr: &Expr<'core>,
    ) -> Either<ZonkedExpr<'out>, Value<'core>> {
        match expr {
            Expr::Meta(var) => match self.get_meta(*var) {
                None => Left(Expr::Meta(*var)),
                Some(value) => Right(value.clone()),
            },
            Expr::FunApp(plicity, (fun, arg)) => match self.zonk_meta_var_spines(fun) {
                Left(fun_expr) => {
                    let arg_expr = self.zonk(arg);
                    Left(Expr::fun_app(self.out_bump, *plicity, fun_expr, arg_expr))
                }
                Right(fun_value) => {
                    let arg_value = self.eval_env().eval(arg);
                    Right(self.elim_env().fun_app(*plicity, fun_value, arg_value))
                }
            },
            Expr::FieldProj(scrut, name) => match self.zonk_meta_var_spines(scrut) {
                Left(scrut_expr) => Left(Expr::field_proj(self.out_bump, scrut_expr, *name)),
                Right(scrut_value) => Right(self.elim_env().field_proj(scrut_value, *name)),
            },
            Expr::MatchBool([scrut, cases @ ..]) => match self.zonk_meta_var_spines(scrut) {
                Left(scrut_expr) => {
                    let [then, r#else] = cases;
                    let then = self.zonk(then);
                    let r#else = self.zonk(r#else);
                    Left(Expr::match_bool(self.out_bump, scrut_expr, then, r#else))
                }
                Right(scrut_value) => {
                    let cases = BoolCases::new(self.local_values.clone(), cases);
                    Right(self.elim_env().match_bool(scrut_value, cases))
                }
            },
            Expr::MatchInt((scrut, default), cases) => match self.zonk_meta_var_spines(scrut) {
                Left(scrut_expr) => {
                    let cases = self.out_bump.alloc_slice_fill_iter(
                        cases.iter().map(|(lit, expr)| (*lit, self.zonk(expr))),
                    );
                    let default = default.map(|expr| self.zonk(&expr));
                    Left(Expr::r#match_int(self.out_bump, scrut_expr, cases, default))
                }
                Right(scrut_value) => {
                    let cases = IntCases::new(self.local_values.clone(), cases, default);
                    Right(self.elim_env().match_int(scrut_value, cases))
                }
            },
            expr => Left(self.zonk(expr)),
        }
    }

    fn push_local(&mut self, name: BinderName) {
        debug_assert_eq!(self.local_names.len(), self.local_values.len());

        let var = Value::local(self.local_values.len().to_level());
        self.local_names.push(name);
        self.local_values.push(var);
    }

    fn pop_local(&mut self) {
        debug_assert_eq!(self.local_names.len(), self.local_values.len());

        self.local_names.pop();
        self.local_values.pop();
    }

    fn local_len(&self) -> EnvLen {
        debug_assert_eq!(self.local_names.len(), self.local_values.len());
        self.local_names.len()
    }

    fn truncate_local(&mut self, len: EnvLen) {
        debug_assert_eq!(self.local_names.len(), self.local_values.len());

        self.local_names.truncate(len);
        self.local_values.truncate(len);
    }
}
