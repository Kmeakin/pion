use pion_core::semantics::Type;

mod expr;
mod lit;
mod r#match;
mod pat;
mod stmt;

pub type Synth<'core, T> = (T, Type<'core>);
pub type Check<T> = T;
