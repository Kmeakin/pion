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

#[derive(Debug, Copy, Clone)]
pub struct File<'text, 'surface> {
    pub stmts: &'surface [Stmt<'text, 'surface>],
}

#[derive(Debug, Copy, Clone)]
pub enum Expr<'text, 'surface> {
    Error,
    Hole,
    Var(&'text str),
    Lit(Lit<'text>),
    Paren(Located<&'surface Self>),
    TypeAnnotation(Located<&'surface Self>, Located<&'surface Self>),
    FunCall(
        Located<&'surface Self>,
        &'surface [Located<FunArg<'text, 'surface>>],
    ),
    FunExpr(
        &'surface [Located<FunParam<'text, 'surface>>],
        Located<&'surface Self>,
    ),
    FunType(
        &'surface [Located<FunParam<'text, 'surface>>],
        Located<&'surface Self>,
    ),
    FunArrow(Located<&'surface Self>, Located<&'surface Self>),
    Do(
        &'surface [Stmt<'text, 'surface>],
        Option<Located<&'surface Expr<'text, 'surface>>>,
    ),
    If(
        Located<&'surface Expr<'text, 'surface>>,
        Located<&'surface Expr<'text, 'surface>>,
        Located<&'surface Expr<'text, 'surface>>,
    ),
    Match(
        Located<&'surface Expr<'text, 'surface>>,
        &'surface [Located<MatchCase<'text, 'surface>>],
    ),
}

#[derive(Debug, Copy, Clone)]
pub struct MatchCase<'text, 'surface> {
    pub pat: Located<Pat<'text, 'surface>>,
    pub expr: Located<Expr<'text, 'surface>>,
}

#[derive(Debug, Copy, Clone)]
pub enum Stmt<'text, 'surface> {
    Command(Command<'text, 'surface>),
    Let(Located<LetBinding<'text, 'surface>>),
    Expr(Located<&'surface Expr<'text, 'surface>>),
}

#[derive(Debug, Copy, Clone)]
pub enum Command<'text, 'surface> {
    Check(Located<&'surface Expr<'text, 'surface>>),
    Eval(Located<&'surface Expr<'text, 'surface>>),
}

#[derive(Debug, Copy, Clone)]
pub struct LetBinding<'text, 'surface> {
    pub pat: Located<Pat<'text, 'surface>>,
    pub init: Located<Expr<'text, 'surface>>,
}

#[derive(Debug, Copy, Clone)]
pub enum Pat<'text, 'surface> {
    Error,
    Underscore,
    Var(&'text str),
    Paren(Located<&'surface Self>),
    TypeAnnotation(
        Located<&'surface Self>,
        Located<&'surface Expr<'text, 'surface>>,
    ),
}

#[derive(Debug, Copy, Clone)]
pub struct FunArg<'text, 'surface> {
    pub plicity: Plicity,
    pub expr: Located<Expr<'text, 'surface>>,
}

#[derive(Debug, Copy, Clone)]
pub struct FunParam<'text, 'surface> {
    pub plicity: Plicity,
    pub pat: Located<Pat<'text, 'surface>>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Plicity {
    Explicit,
    Implicit,
}

#[derive(Debug, Copy, Clone)]
pub enum Lit<'text> {
    Bool(bool),
    Int(&'text str),
    Char(&'text str),
    String(&'text str),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn type_sizes() {
        assert_eq!(size_of::<File>(), 16);
        assert_eq!(size_of::<Expr>(), 56);
        assert_eq!(size_of::<Stmt>(), 120);
        assert_eq!(size_of::<Command>(), 24);
        assert_eq!(size_of::<LetBinding>(), 112);
        assert_eq!(size_of::<Pat>(), 40);
        assert_eq!(size_of::<FunArg>(), 72);
        assert_eq!(size_of::<FunParam>(), 56);
        assert_eq!(size_of::<Lit>(), 24);
    }
}
