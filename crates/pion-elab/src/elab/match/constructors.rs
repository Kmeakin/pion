use std::ops::ControlFlow;

use internal_iterator::InternalIterator;
use pion_core::symbol::Symbol;
use pion_core::syntax::Lit;
use smallvec::{smallvec, SmallVec};

use super::matrix::PatMatrix;
use crate::elab::pat::Pat;

/// The head constructor of a pattern
#[derive(Debug, Copy, Clone)]
pub enum Constructor<'core> {
    Lit(Lit<'core>),
    Record(&'core [(Symbol<'core>, Pat<'core>)]),
}

impl<'core> PartialEq for Constructor<'core> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Lit(left_lit), Self::Lit(right_lit)) => left_lit == right_lit,
            #[cfg(false)]
            (Self::Record(left_fields), Self::Record(right_fields)) => {
                pion_core::syntax::record_keys_equal(left_fields, right_fields)
            }
            _ => false,
        }
    }
}

impl<'core> Eq for Constructor<'core> {}

impl<'core> Constructor<'core> {
    /// Return number of fields `self` carries
    pub const fn arity(&self) -> usize {
        match self {
            Constructor::Lit(_) => 0,
            Constructor::Record(labels) => labels.len(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Constructors<'core> {
    #[cfg(false)]
    Record(&'core [(Symbol<'core>, Pat<'core>)]),
    Bools(BoolSet),
    Ints(SmallVec<[u32; 4]>),

    Phantom(
        std::convert::Infallible,
        std::marker::PhantomData<&'core ()>,
    ),
}

/// Non-empty set of `bool`s.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum BoolSet {
    False = 1,
    True = 2,
    Both = 3,
}

#[allow(
    clippy::as_conversions,
    reason = "`BoolSet` and `bool` are guaranteed to fit in `u8`"
)]
impl BoolSet {
    pub fn contains(self, b: bool) -> bool {
        let bitset = self as u8;
        let mask = 1 << u8::from(b);
        bitset & mask != 0
    }

    pub const fn union(self, other: Self) -> Self {
        // SAFETY: `BoolSet` and `u8` are guaranteed to fit in `u8`
        unsafe { std::mem::transmute(self as u8 | other as u8) }
    }

    pub fn insert(&mut self, b: bool) { *self = self.union(Self::from(b)); }

    pub const fn is_full(self) -> bool { matches!(self, Self::Both) }
}

impl From<bool> for BoolSet {
    fn from(value: bool) -> Self {
        match value {
            true => Self::True,
            false => Self::False,
        }
    }
}

impl Constructors<'_> {
    pub fn is_exhaustive(&self) -> bool {
        match self {
            #[cfg(false)]
            Constructors::Record(_) => true,
            Constructors::Bools(bools) => bools.is_full(),
            Constructors::Ints(ints) => (ints.len()) >= u32::MAX as usize,
            Constructors::Phantom(d, _) => match *d {},
        }
    }
}

pub struct PatConstructors<'core> {
    pat: Pat<'core>,
}

impl<'core> PatConstructors<'core> {
    pub const fn new(pat: Pat<'core>) -> Self { Self { pat } }
}

impl<'core> InternalIterator for PatConstructors<'core> {
    type Item = Constructor<'core>;

    fn try_for_each<R, F>(self, mut on_ctor: F) -> ControlFlow<R>
    where
        F: FnMut(Self::Item) -> ControlFlow<R>,
    {
        fn recur<'core, R>(
            pat: Pat<'core>,
            on_ctor: &mut impl FnMut(Constructor<'core>) -> ControlFlow<R>,
        ) -> ControlFlow<R> {
            match pat {
                Pat::Error | Pat::Wildcard | Pat::Var(..) => ControlFlow::Continue(()),
                Pat::Lit(.., lit) => on_ctor(Constructor::Lit(lit)),
                // Pat::RecordLit(.., fields) => on_ctor(Constructor::Record(fields)),
                // Pat::Or(pats) => pats.iter().try_for_each(|pat| recur(*pat, on_ctor)),
            }
        }

        recur(self.pat, &mut on_ctor)
    }
}

pub fn has_constructors(pat: &Pat) -> bool { PatConstructors::new(*pat).next().is_some() }

impl<'core> PatMatrix<'core> {
    /// Collect all the `Constructor`s in the `index`th column
    pub fn column_constructors(&self, index: usize) -> Option<Constructors<'core>> {
        let column = self.column(index).map(|(pat, _)| *pat);
        return start(column);

        fn start<'core>(
            mut column: impl Iterator<Item = Pat<'core>>,
        ) -> Option<Constructors<'core>> {
            while let Some(pat) = column.next() {
                match pat {
                    Pat::Error | Pat::Wildcard | Pat::Var(_) => continue,
                    #[cfg(false)]
                    Pat::RecordLit(fields) => return Some(Constructors::Record(fields)),
                    Pat::Lit(Lit::Bool(value)) => {
                        return Some(Constructors::Bools(bools(column, BoolSet::from(value))))
                    }
                    Pat::Lit(Lit::Int(value)) => {
                        return Some(Constructors::Ints(ints(column, smallvec![value])))
                    }
                    Pat::Lit(Lit::Char(_)) => todo!(),
                    Pat::Lit(Lit::String(_)) => todo!(),
                    #[cfg(false)]
                    Pat::Or(alts) => {
                        let mut alts = alts.iter().copied();
                        while let Some(pat) = alts.next() {
                            match start(std::iter::once(pat)) {
                                None => continue,
                                Some(ctors) => match ctors {
                                    Constructors::Record(_) => return Some(ctors),
                                    Constructors::Bools(mut values) => {
                                        if !values.is_full() {
                                            values = bools(alts, values);
                                        }
                                        return Some(Constructors::Bools(bools(column, values)));
                                    }
                                    Constructors::Ints(mut values) => {
                                        values = ints(alts, values);
                                        return Some(Constructors::Ints(ints(column, values)));
                                    }
                                },
                            }
                        }
                    }
                }
            }
            None
        }

        fn bools<'core>(column: impl Iterator<Item = Pat<'core>>, mut values: BoolSet) -> BoolSet {
            for pat in column {
                match pat {
                    Pat::Error | Pat::Wildcard | Pat::Var(..) => continue,
                    Pat::Lit(.., Lit::Bool(value)) => {
                        values.insert(value);
                        if values.is_full() {
                            break;
                        }
                    }
                    Pat::Lit(..) => unreachable!(),
                    #[cfg(false)]
                    Pat::RecordLit(..) => unreachable!(),
                    #[cfg(false)]
                    Pat::Or(alts) => {
                        values = bools(alts.iter().copied(), values);
                        if values.is_full() {
                            break;
                        }
                    }
                }
            }
            values
        }

        fn ints<'core>(
            column: impl Iterator<Item = Pat<'core>>,
            mut values: SmallVec<[u32; 4]>,
        ) -> SmallVec<[u32; 4]> {
            for pat in column {
                match pat {
                    Pat::Error | Pat::Wildcard | Pat::Var(..) => continue,
                    Pat::Lit(.., Lit::Int(value)) => {
                        if let Err(index) = values.binary_search(&value) {
                            values.insert(index, value);
                        }
                    }
                    Pat::Lit(..) => unreachable!(),

                    #[cfg(false)]
                    Pat::RecordLit(..) => unreachable!(),

                    #[cfg(false)]
                    Pat::Or(alts) => values = ints(alts.iter().copied(), values),
                }
            }
            values
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn boolset_contains() {
        assert!(BoolSet::False.contains(false));
        assert!(!BoolSet::False.contains(true));

        assert!(!BoolSet::True.contains(false));
        assert!(BoolSet::True.contains(true));

        assert!(BoolSet::Both.contains(false));
        assert!(BoolSet::Both.contains(true));
    }

    #[test]
    fn boolset_union() {
        assert_eq!(BoolSet::False.union(BoolSet::False), BoolSet::False);
        assert_eq!(BoolSet::False.union(BoolSet::True), BoolSet::Both);

        assert_eq!(BoolSet::True.union(BoolSet::False), BoolSet::Both);
        assert_eq!(BoolSet::True.union(BoolSet::True), BoolSet::True);

        assert_eq!(BoolSet::Both.union(BoolSet::False), BoolSet::Both);
        assert_eq!(BoolSet::Both.union(BoolSet::True), BoolSet::Both);
    }
}
