use pion_core::env::{EnvLen, RelativeVar, SharedEnv, UniqueEnv};
use pion_core::semantics::{Type, Value};
use pion_interner::InternedStr;

#[derive(Default)]
pub struct ElabEnv<'core> {
    pub locals: LocalEnv<'core>,
    pub metas: MetaEnv<'core>,
}

#[derive(Default)]
pub struct LocalEnv<'core> {
    pub names: UniqueEnv<Option<InternedStr<'core>>>,
    pub types: UniqueEnv<Type<'core>>,
    pub values: SharedEnv<Value<'core>>,
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
        r#type: Type<'core>,
        value: Value<'core>,
    ) {
        self.names.push(name);
        self.types.push(r#type);
        self.values.push(value);
    }

    pub fn push_param(&mut self, name: Option<InternedStr<'core>>, r#type: Type<'core>) {
        let value = Value::local_var(self.names.len().to_absolute());
        self.push(name, r#type, value);
    }

    pub fn push_let(
        &mut self,
        name: Option<InternedStr<'core>>,
        r#type: Type<'core>,
        value: Value<'core>,
    ) {
        self.push(name, r#type, value);
    }

    pub fn pop(&mut self) {
        self.names.pop();
        self.types.pop();
        self.values.pop();
    }
}

#[derive(Default)]
pub struct MetaEnv<'core> {
    pub values: SharedEnv<Option<Value<'core>>>,
}
