use pion_core::env::{DeBruijnIndex, EnvLen, SharedEnv, UniqueEnv};
use pion_core::semantics::{Type, Value};
use pion_core::symbol::Symbol;
use pion_core::syntax::{Expr, LocalVar, Name};
use text_size::TextRange;

use crate::unify::PartialRenaming;

#[derive(Default)]
pub struct ElabEnv<'core> {
    pub locals: LocalEnv<'core>,
    pub metas: MetaEnv<'core>,
    pub renaming: PartialRenaming,
}

#[derive(Default)]
pub struct LocalEnv<'core> {
    pub names: UniqueEnv<Name<'core>>,
    pub infos: UniqueEnv<LocalInfo<'core>>,
    pub types: UniqueEnv<Type<'core>>,
    pub values: SharedEnv<Value<'core>>,
}

#[derive(Debug, Copy, Clone)]
pub enum LocalInfo<'core> {
    Let(Expr<'core>),
    Param,
}

impl<'core> LocalEnv<'core> {
    pub fn len(&self) -> EnvLen { self.names.len() }

    pub fn lookup(
        &self,
        name: Symbol<'core>,
    ) -> Option<(LocalVar<DeBruijnIndex>, &Type<'core>, &Value<'core>)> {
        let index = self.names.find(&Some(name))?;
        Some((
            LocalVar::new(index),
            self.types.get(index).unwrap(),
            self.values.get(index).unwrap(),
        ))
    }

    pub fn push(
        &mut self,
        name: Name<'core>,
        info: LocalInfo<'core>,
        r#type: Type<'core>,
        value: Value<'core>,
    ) {
        self.names.push(name);
        self.infos.push(info);
        self.types.push(r#type);
        self.values.push(value);
    }

    pub fn push_param(&mut self, name: Name<'core>, r#type: Type<'core>) {
        let value = Value::local_var(LocalVar::new(self.names.len().to_level()));
        self.push(name, LocalInfo::Param, r#type, value);
    }

    pub fn push_let(
        &mut self,
        name: Name<'core>,
        r#type: Type<'core>,
        init: Expr<'core>,
        value: Value<'core>,
    ) {
        self.push(name, LocalInfo::Let(init), r#type, value);
    }

    pub fn pop(&mut self) {
        self.names.pop();
        self.infos.pop();
        self.types.pop();
        self.values.pop();
    }

    pub fn truncate(&mut self, len: EnvLen) {
        self.names.truncate(len);
        self.infos.truncate(len);
        self.types.truncate(len);
        self.values.truncate(len);
    }
}

#[derive(Default)]
pub struct MetaEnv<'core> {
    pub sources: UniqueEnv<MetaSource<'core>>,
    pub types: UniqueEnv<Type<'core>>,
    pub values: UniqueEnv<Option<Value<'core>>>,
}

impl<'core> MetaEnv<'core> {
    pub fn len(&self) -> EnvLen { self.sources.len() }

    pub fn push(&mut self, source: MetaSource<'core>, r#type: Type<'core>) {
        self.sources.push(source);
        self.types.push(r#type);
        self.values.push(None);
    }

    pub fn iter(
        &self,
    ) -> impl Iterator<Item = (MetaSource<'core>, &Type<'core>, &Option<Value<'core>>)> + '_ {
        self.sources
            .iter()
            .zip(self.types.iter())
            .zip(self.values.iter())
            .map(|((source, r#type), value)| (*source, r#type, value))
    }
}

#[derive(Debug, Copy, Clone)]
pub enum MetaSource<'core> {
    PatType(TextRange, Name<'core>),
    HoleType(TextRange),
    HoleExpr(TextRange),
    ImplicitArg(TextRange, Name<'core>),
    MatchType(TextRange),
}

impl MetaSource<'_> {
    pub fn range(&self) -> TextRange {
        match self {
            MetaSource::PatType(range, ..)
            | MetaSource::HoleExpr(range, ..)
            | MetaSource::HoleType(range, ..)
            | MetaSource::ImplicitArg(range, ..)
            | MetaSource::MatchType(range, ..) => *range,
        }
    }
}
