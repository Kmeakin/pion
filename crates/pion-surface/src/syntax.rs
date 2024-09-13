use std::fmt;

use text_size::TextRange;

#[derive(Copy, Clone)]
pub struct Located<T> {
    pub range: TextRange,
    pub data: T,
}

impl<T: fmt::Debug> fmt::Debug for Located<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Located")
            .field(&self.range)
            .field(&self.data)
            .finish()
    }
}

impl<T> Located<T> {
    pub fn new(range: TextRange, data: T) -> Self { Self { range, data } }

    pub fn map<V>(self, f: impl FnOnce(T) -> V) -> Located<V> {
        Located::new(self.range, f(self.data))
    }

    pub fn as_ref(&self) -> Located<&T> { Located::new(self.range, &self.data) }
}

#[derive(Copy, Clone)]
pub enum Expr<'text, 'surface> {
    Error,
    Var(&'text str),
    Bool(bool),
    Number(&'text str),
    Char(&'text str),
    String(&'text str),
    Paren(Located<&'surface Self>),
    TypeAnnotation {
        expr: Located<&'surface Self>,
        r#type: Located<&'surface Self>,
    },
    FunCall {
        callee: Located<&'surface Self>,
        args: &'surface [Located<FunArg<'text, 'surface>>],
    },
    FunExpr {
        params: &'surface [Located<FunParam<'text, 'surface>>],
        body: Located<&'surface Self>,
    },
    FunType {
        params: &'surface [Located<FunParam<'text, 'surface>>],
        body: Located<&'surface Self>,
    },
    FunArrow {
        domain: Located<&'surface Self>,
        codomain: Located<&'surface Self>,
    },
    Let {
        binding: Located<&'surface LetBinding<'text, 'surface>>,
        body: Located<&'surface Self>,
    },
}

#[derive(Copy, Clone)]
pub struct LetBinding<'text, 'surface> {
    pub pat: Located<Pat<'text, 'surface>>,
    pub expr: Located<Expr<'text, 'surface>>,
}

#[derive(Copy, Clone)]
pub enum Pat<'text, 'surface> {
    Error,
    Underscore,
    Var(&'text str),
    Paren(Located<&'surface Self>),
    TypeAnnotation {
        pat: Located<&'surface Self>,
        r#type: Located<&'surface Expr<'text, 'surface>>,
    },
}

#[derive(Copy, Clone)]
pub struct FunArg<'text, 'surface> {
    pub expr: Located<Expr<'text, 'surface>>,
}

#[derive(Copy, Clone)]
pub struct FunParam<'text, 'surface> {
    pub pat: Located<Pat<'text, 'surface>>,
}
