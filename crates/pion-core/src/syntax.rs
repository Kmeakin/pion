use crate::env::{DeBruijn, DeBruijnIndex, DeBruijnLevel, EnvLen};
use crate::prim::PrimVar;
use crate::symbol::Symbol;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Expr<'core> {
    Error,

    Lit(Lit<'core>),

    PrimVar(PrimVar),
    LocalVar(LocalVar<'core, DeBruijnIndex>),
    MetaVar(MetaVar),

    FunType(FunParam<'core, &'core Self>, &'core Self),
    FunLit(FunParam<'core, &'core Self>, &'core Self),
    FunApp(&'core Self, FunArg<&'core Self>),

    Do(&'core [Stmt<'core>], Option<&'core Self>),
    If(&'core Self, &'core Self, &'core Self),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct LocalVar<'core, V> {
    pub name: Name<'core>,
    pub de_bruijn: V,
}

impl<'core, V> LocalVar<'core, V> {
    pub const fn new(name: Name<'core>, de_bruijn: V) -> Self { Self { name, de_bruijn } }
}

impl DeBruijn for LocalVar<'_, DeBruijnIndex> {
    fn to_level(self, len: EnvLen) -> Option<DeBruijnLevel> { self.de_bruijn.to_level(len) }
    fn to_index(self, len: EnvLen) -> Option<DeBruijnIndex> { self.de_bruijn.to_index(len) }
}

impl DeBruijn for LocalVar<'_, DeBruijnLevel> {
    fn to_level(self, len: EnvLen) -> Option<DeBruijnLevel> { self.de_bruijn.to_level(len) }
    fn to_index(self, len: EnvLen) -> Option<DeBruijnIndex> { self.de_bruijn.to_index(len) }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct MetaVar {
    pub de_bruijn: DeBruijnLevel,
}

impl MetaVar {
    pub const fn new(de_bruijn: DeBruijnLevel) -> Self { Self { de_bruijn } }
}

impl DeBruijn for MetaVar {
    fn to_level(self, len: EnvLen) -> Option<DeBruijnLevel> { self.de_bruijn.to_level(len) }
    fn to_index(self, len: EnvLen) -> Option<DeBruijnIndex> { self.de_bruijn.to_index(len) }
}

pub type Name<'core> = Option<Symbol<'core>>;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Lit<'core> {
    Bool(bool),
    Int(u32),
    Char(char),
    String(&'core str),
}

impl<'core> Expr<'core> {
    pub const TYPE: Self = Self::PrimVar(PrimVar::Type);
    pub const BOOL: Self = Self::PrimVar(PrimVar::Bool);
    pub const INT: Self = Self::PrimVar(PrimVar::Int);
    pub const STRING: Self = Self::PrimVar(PrimVar::String);
    pub const CHAR: Self = Self::PrimVar(PrimVar::Char);
    pub const UNIT_TYPE: Self = Self::PrimVar(PrimVar::Unit);
    pub const UNIT_VALUE: Self = Self::PrimVar(PrimVar::unit);

    pub const fn bool(b: bool) -> Self { Self::Lit(Lit::Bool(b)) }
    pub const fn int(n: u32) -> Self { Self::Lit(Lit::Int(n)) }
    pub const fn char(c: char) -> Self { Self::Lit(Lit::Char(c)) }
    pub const fn string(s: &'core str) -> Self { Self::Lit(Lit::String(s)) }

    /// Returns `true` if the term contains an occurrence of the local variable.
    pub fn binds_local(&self, mut var: DeBruijnIndex) -> bool {
        match self {
            Expr::Error | Expr::Lit(_) | Expr::PrimVar(_) | Expr::MetaVar(_) => false,
            Expr::LocalVar(v) => v.de_bruijn == var,
            Expr::FunType(param, body) | Expr::FunLit(param, body) => {
                param.r#type.binds_local(var) || body.binds_local(var.succ())
            }
            Expr::FunApp(fun, arg) => fun.binds_local(var) || arg.expr.binds_local(var),
            Expr::Do(stmts, expr) => {
                stmts.iter().any(|stmt| match stmt {
                    Stmt::Expr(expr) => expr.binds_local(var),
                    Stmt::Let(binding) => {
                        let result =
                            binding.r#type.binds_local(var) || binding.init.binds_local(var);
                        var = var.succ();
                        result
                    }
                }) || expr.map_or(false, |expr| expr.binds_local(var))
            }
            Expr::If(cond, then, r#else) => [cond, then, r#else]
                .iter()
                .any(|expr| expr.binds_local(var)),
        }
    }

    #[must_use]
    pub fn shift(&self, bump: &'core bumpalo::Bump, amount: EnvLen) -> Self {
        return recur(self, bump, DeBruijnIndex::default(), amount);

        /// Increment all `LocalVar`s greater than or equal to `min` by
        /// `amount`.
        /// See <https://github.com/dhall-lang/dhall-lang/blob/master/standard/shift.md>.
        fn recur<'core>(
            expr: &Expr<'core>,
            bump: &'core bumpalo::Bump,
            min: DeBruijnIndex,
            amount: EnvLen,
        ) -> Expr<'core> {
            // Skip traversing and rebuilding the term if it would make no change.
            // Increases sharing.
            if amount == EnvLen::default() {
                return *expr;
            }

            match expr {
                Expr::LocalVar(var) if var.de_bruijn >= min => {
                    Expr::LocalVar(LocalVar::new(var.name, var.de_bruijn + amount))
                }

                Expr::Error
                | Expr::Lit(..)
                | Expr::PrimVar(..)
                | Expr::LocalVar(..)
                | Expr::MetaVar(..) => *expr,

                Expr::FunLit { 0: param, 1: body } => {
                    let r#type = recur(param.r#type, bump, min, amount);
                    let body = recur(body, bump, min.succ(), amount);
                    let (r#type, body) = bump.alloc((r#type, body));
                    let param = FunParam::new(param.plicity, param.name, &*r#type);
                    Expr::FunLit(param, body)
                }
                Expr::FunType { 0: param, 1: body } => {
                    let r#type = recur(param.r#type, bump, min, amount);
                    let body = recur(body, bump, min.succ(), amount);
                    let (r#type, body) = bump.alloc((r#type, body));
                    let param = FunParam::new(param.plicity, param.name, &*r#type);
                    Expr::FunType(param, body)
                }
                Expr::FunApp { 0: fun, 1: arg } => {
                    let fun = recur(fun, bump, min, amount);
                    let arg_expr = recur(arg.expr, bump, min, amount);
                    let (fun, arg_expr) = bump.alloc((fun, arg_expr));
                    Expr::FunApp(fun, FunArg::new(arg.plicity, arg_expr))
                }

                Expr::If(cond, then, r#else) => {
                    let cond = recur(cond, bump, min, amount);
                    let then = recur(then, bump, min, amount);
                    let r#else = recur(r#else, bump, min, amount);
                    let (cond, then, r#else) = bump.alloc((cond, then, r#else));
                    Expr::If(cond, then, r#else)
                }
                Expr::Do(stmts, expr) => {
                    let mut min = min;
                    let stmts = bump.alloc_slice_fill_iter(stmts.iter().map(|stmt| match stmt {
                        Stmt::Expr(expr) => Stmt::Expr(recur(expr, bump, min, amount)),
                        Stmt::Let(let_binding) => {
                            let r#type = recur(&let_binding.r#type, bump, min, amount);
                            let init = recur(&let_binding.init, bump, min, amount);
                            min = min.succ();
                            Stmt::Let(LetBinding::new(let_binding.name, r#type, init))
                        }
                    }));
                    let trailing_expr =
                        expr.map(|expr| &*bump.alloc(recur(expr, bump, min, amount)));
                    Expr::Do(stmts, trailing_expr)
                }
            }
        }
    }

    pub fn wrap_in_lets(
        bump: &'core bumpalo::Bump,
        bindings: &[LetBinding<'core, Self>],
        body: Self,
    ) -> Self {
        match bindings {
            [] => body,
            [..] => Expr::Do(
                bump.alloc_slice_fill_iter(bindings.iter().map(|binding| Stmt::Let(*binding))),
                Some(bump.alloc(body)),
            ),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Stmt<'core> {
    Let(LetBinding<'core, Expr<'core>>),
    Expr(Expr<'core>),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct LetBinding<'core, T> {
    pub name: Name<'core>,
    pub r#type: T,
    pub init: T,
}

impl<'core, T> LetBinding<'core, T> {
    pub const fn new(name: Name<'core>, r#type: T, init: T) -> Self { Self { name, r#type, init } }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct FunParam<'core, T> {
    pub plicity: Plicity,
    pub name: Name<'core>,
    pub r#type: T,
}

impl<'core, T> FunParam<'core, T> {
    pub const fn new(plicity: Plicity, name: Name<'core>, r#type: T) -> Self {
        Self {
            plicity,
            name,
            r#type,
        }
    }
    pub const fn explicit(name: Name<'core>, r#type: T) -> Self {
        Self::new(Plicity::Explicit, name, r#type)
    }
    pub const fn implicit(name: Name<'core>, r#type: T) -> Self {
        Self::new(Plicity::Implicit, name, r#type)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct FunArg<T> {
    pub plicity: Plicity,
    pub expr: T,
}

impl<T> FunArg<T> {
    pub const fn new(plicity: Plicity, expr: T) -> Self { Self { plicity, expr } }
    pub const fn explicit(expr: T) -> Self { Self::new(Plicity::Explicit, expr) }
    pub const fn implicit(expr: T) -> Self { Self::new(Plicity::Implicit, expr) }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Plicity {
    /// Parameter/argument is inferred from context.
    Implicit,
    /// Parameter/argument is provided by the programmer.
    Explicit,
}

impl Plicity {
    pub const fn description(&self) -> &'static str {
        match self {
            Self::Implicit => "implicit",
            Self::Explicit => "explicit",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn type_sizes() {
        assert_eq!(size_of::<Expr>(), 48);
        assert_eq!(size_of::<Lit>(), 24);
        assert_eq!(size_of::<Stmt>(), 112);
        assert_eq!(size_of::<LetBinding<Expr>>(), 112);
        assert_eq!(size_of::<FunParam<Expr>>(), 72);
        assert_eq!(size_of::<FunArg<Expr>>(), 56);
    }
}
