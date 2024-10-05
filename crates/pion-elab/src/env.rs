use pion_core::env::{EnvLen, RelativeVar, SharedEnv, UniqueEnv};
use pion_core::semantics::{Type, Value};
use pion_interner::InternedStr;
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
    pub names: UniqueEnv<Option<InternedStr<'core>>>,
    pub infos: UniqueEnv<LocalInfo>,
    pub types: UniqueEnv<Type<'core>>,
    pub values: SharedEnv<Value<'core>>,
}

#[derive(Debug, Copy, Clone)]
pub enum LocalInfo {
    Let,
    Param,
}

impl<'core> LocalEnv<'core> {
    pub fn len(&self) -> EnvLen { self.names.len() }

    pub fn lookup(&self, name: InternedStr) -> Option<RelativeVar> {
        self.names
            .iter()
            .rev()
            .position(|item| *item == Some(name))
            .map(RelativeVar::new)
    }

    pub fn push(
        &mut self,
        name: Option<InternedStr<'core>>,
        info: LocalInfo,
        r#type: Type<'core>,
        value: Value<'core>,
    ) {
        self.names.push(name);
        self.infos.push(info);
        self.types.push(r#type);
        self.values.push(value);
    }

    pub fn push_param(&mut self, name: Option<InternedStr<'core>>, r#type: Type<'core>) {
        let value = Value::local_var(self.names.len().to_absolute());
        self.push(name, LocalInfo::Param, r#type, value);
    }

    pub fn push_let(
        &mut self,
        name: Option<InternedStr<'core>>,
        r#type: Type<'core>,
        value: Value<'core>,
    ) {
        self.push(name, LocalInfo::Let, r#type, value);
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
    PatType(TextRange, Option<InternedStr<'core>>),
    HoleType(TextRange),
    HoleExpr(TextRange),
}

impl MetaSource<'_> {
    pub fn range(&self) -> TextRange {
        match self {
            MetaSource::PatType(range, ..)
            | MetaSource::HoleExpr(range, ..)
            | MetaSource::HoleType(range, ..) => *range,
        }
    }
}
