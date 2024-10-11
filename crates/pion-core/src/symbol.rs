use core::fmt;
use std::hash::Hash;

use fxhash::FxHashSet;

#[derive(Debug, Copy, Clone)]
pub struct Symbol<'text>(&'text str);

impl PartialEq for Symbol<'_> {
    fn eq(&self, other: &Self) -> bool { std::ptr::eq(self.0, other.0) }
}

impl Eq for Symbol<'_> {}

impl Hash for Symbol<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) { std::ptr::hash(self.0, state) }
}

impl AsRef<str> for Symbol<'_> {
    fn as_ref(&self) -> &str { self.0 }
}

impl fmt::Display for Symbol<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.0.fmt(f) }
}

#[derive(Debug, Clone)]
pub struct Interner<'text> {
    set: FxHashSet<&'text str>,
}

impl<'text> Interner<'text> {
    pub fn new(set: FxHashSet<&'text str>) -> Self { Self { set } }

    pub fn intern<F: FnOnce(&str) -> &'text str>(&mut self, value: &str, f: F) -> Symbol<'text> {
        Symbol(self.set.get_or_insert_with(value, f))
    }
}

impl Default for Interner<'_> {
    fn default() -> Self {
        Self {
            set: sym::ALL.iter().map(|s| s.0).collect(),
        }
    }
}

macro_rules! symbols {
    ($($sym:ident $(,)?),*) => {
        #[allow(non_upper_case_globals, reason = "So we can distinguish uppercase from lowercase")]
        pub mod sym {
            use super::Symbol;

            pub const ALL: &[Symbol<'static>] = &[$($sym),*];
            $(pub const $sym: Symbol<'static> = Symbol(stringify!($sym));)*
        }
    };
}

#[rustfmt::skip]
symbols![
    A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z,
    a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z,
];
