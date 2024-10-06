//! Local variables and environments.

use std::fmt;
use std::ops::{Add, Deref, DerefMut};

use ecow::EcoVec;

/// A de Bruijn level: counts number of binders from the binder that introduced
/// the variable to the start of the environment.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Default, Hash)]
pub struct DeBruijnLevel(usize);

impl DeBruijnLevel {
    pub const fn new(value: usize) -> Self { Self(value) }
}

impl fmt::Display for DeBruijnLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.0.fmt(f) }
}

impl DeBruijnLevel {
    pub fn iter() -> impl Iterator<Item = Self> { (0..).map(Self) }
}

/// A de Bruijn index: counts number of binders from the variable to the binder
/// that introduced it.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Default, Hash)]
pub struct DeBruijnIndex(usize);

impl DeBruijnIndex {
    pub const fn new(value: usize) -> Self { Self(value) }

    #[must_use]
    pub const fn succ(self) -> Self { Self(self.0 + 1) }

    #[must_use]
    pub fn pred(self) -> Option<Self> { self.0.checked_sub(1).map(Self) }

    pub fn iter() -> impl Iterator<Item = Self> { (0..).map(Self) }

    pub fn iter_from(start: Self) -> impl Iterator<Item = Self> { (start.0..).map(Self) }
}

impl fmt::Display for DeBruijnIndex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.0.fmt(f) }
}

impl Add<EnvLen> for DeBruijnIndex {
    type Output = Self;
    fn add(self, rhs: EnvLen) -> Self::Output { Self(self.0 + rhs.0) }
}

/// A specialized representation of an environment for when we don't care about
/// the elements themselves, just the number of elements in the environment.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Default, Hash)]
pub struct EnvLen(usize);

impl fmt::Display for EnvLen {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.0.fmt(f) }
}

impl EnvLen {
    pub const fn new(len: usize) -> Self { Self(len) }

    /// Get a `DeBruijnLevel` representing the most recent entry in the
    /// environment.
    pub const fn to_level(self) -> DeBruijnLevel { DeBruijnLevel(self.0) }

    /// Get a new environment with one extra element.
    #[must_use]
    pub const fn succ(self) -> Self { Self(self.0 + 1) }

    /// Get a new environment with one less element.
    pub fn pred(self) -> Option<Self> { self.0.checked_sub(1).map(Self) }

    /// Push a new element onto the environment.
    pub fn push(&mut self) { self.0 += 1; }

    /// Pop an new element off the environment.
    pub fn pop(&mut self) { self.0 -= 1; }

    /// Push many elements onto an environment.
    pub fn append(&mut self, other: Self) { self.0 += other.0; }

    /// Truncate the environment to `new_len`.
    pub fn truncate(&mut self, new_len: Self) { self.0 = new_len.0; }

    /// Reset the environment to the empty environment.
    pub fn clear(&mut self) { self.0 = 0; }
}

impl Add for EnvLen {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output { Self(self.0 + rhs.0) }
}

pub trait DeBruijn: Copy + fmt::Debug {
    fn to_level(self, len: EnvLen) -> Option<DeBruijnLevel>;
    fn to_index(self, len: EnvLen) -> Option<DeBruijnIndex>;
}

impl DeBruijn for DeBruijnLevel {
    fn to_level(self, _: EnvLen) -> Option<DeBruijnLevel> { Some(self) }
    fn to_index(self, len: EnvLen) -> Option<DeBruijnIndex> {
        Some(DeBruijnIndex(len.0.checked_sub(self.0)?.checked_sub(1)?))
    }
}

impl DeBruijn for DeBruijnIndex {
    fn to_level(self, len: EnvLen) -> Option<DeBruijnLevel> {
        Some(DeBruijnLevel(len.0.checked_sub(self.0)?.checked_sub(1)?))
    }
    fn to_index(self, _: EnvLen) -> Option<DeBruijnIndex> { Some(self) }
}

/// An environment that is cheap to mutate, but expensive (*O(n)*) to clone.
#[derive(Debug, Clone)]
pub struct UniqueEnv<T> {
    elems: Vec<T>,
}

impl<T> UniqueEnv<T> {
    pub const fn new() -> Self { Self { elems: Vec::new() } }

    pub fn push(&mut self, elem: T) { self.elems.push(elem); }
    pub fn pop(&mut self) { self.elems.pop(); }

    pub fn truncate(&mut self, len: EnvLen) { self.elems.truncate(len.0); }
    pub fn clear(&mut self) { self.elems.clear(); }

    pub fn resize(&mut self, len: EnvLen, value: T)
    where
        T: Clone,
    {
        self.elems.resize(len.0, value);
    }
}

impl<T> Default for UniqueEnv<T> {
    fn default() -> Self { Self::new() }
}

impl<T> Deref for UniqueEnv<T> {
    type Target = SliceEnv<T>;
    fn deref(&self) -> &Self::Target { self.elems[..].into() }
}

impl<T> DerefMut for UniqueEnv<T> {
    fn deref_mut(&mut self) -> &mut Self::Target { (&mut self.elems[..]).into() }
}

/// An environment that is cheap to clone, with copy on-write-semantics for
/// mutation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SharedEnv<T> {
    elems: EcoVec<T>,
}

impl<T: Clone> SharedEnv<T> {
    pub const fn new() -> Self {
        Self {
            elems: EcoVec::new(),
        }
    }

    pub fn push(&mut self, elem: T) { self.elems.push(elem); }
    pub fn pop(&mut self) { self.elems.pop(); }

    pub fn truncate(&mut self, len: EnvLen) { self.elems.truncate(len.0); }
    pub fn clear(&mut self) { self.elems.clear(); }
}

impl<T: Clone> Default for SharedEnv<T> {
    fn default() -> Self { Self::new() }
}

impl<T> Deref for SharedEnv<T> {
    type Target = SliceEnv<T>;
    fn deref(&self) -> &Self::Target { self.elems[..].into() }
}

/// A fixed-length view of an environment.
/// `SliceEnv` is to `UniqueEnv` as `[T]` is to `Vec<T>`.
#[derive(Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct SliceEnv<T> {
    elems: [T],
}

impl<T> SliceEnv<T> {
    pub const fn len(&self) -> EnvLen { EnvLen(self.elems.len()) }

    pub const fn is_empty(&self) -> bool { self.elems.is_empty() }

    pub fn iter(&self) -> std::slice::Iter<T> { self.elems.iter() }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<T> { self.elems.iter_mut() }

    pub fn get(&self, db: impl DeBruijn) -> Option<&T> {
        self.elems.get(db.to_level(self.len())?.0)
    }

    pub fn get_mut(&mut self, db: impl DeBruijn) -> Option<&mut T> {
        self.elems.get_mut(db.to_level(self.len())?.0)
    }

    /// # Panics
    /// Panics if `db` is out of bounds.
    pub fn set(&mut self, db: impl DeBruijn, value: T) {
        match self.get_mut(db) {
            Some(place) => *place = value,
            None => panic!("set: index out of bounds: {db:?} > {}", self.len()),
        }
    }

    pub fn find(&self, elem: &T) -> Option<DeBruijnIndex>
    where
        T: PartialEq,
    {
        self.elems
            .iter()
            .rev()
            .position(|it| it == elem)
            .map(DeBruijnIndex::new)
    }
}

impl<'a, T> IntoIterator for &'a SliceEnv<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter { self.elems.iter() }
}

impl<'a, T> IntoIterator for &'a mut SliceEnv<T> {
    type Item = &'a mut T;
    type IntoIter = std::slice::IterMut<'a, T>;
    fn into_iter(self) -> Self::IntoIter { self.elems.iter_mut() }
}

impl<'a, T> From<&'a [T]> for &'a SliceEnv<T> {
    fn from(slice: &'a [T]) -> &'a SliceEnv<T> {
        // SAFETY:
        // - `SliceEnv<T>` is equivalent to an `[T]` internally
        #[allow(
            clippy::as_conversions,
            reason = "ptr::cast is not available for unsized types"
        )]
        unsafe {
            &*(std::ptr::from_ref::<[T]>(slice) as *const SliceEnv<T>)
        }
    }
}

impl<'a, T> From<&'a mut [T]> for &'a mut SliceEnv<T> {
    fn from(slice: &'a mut [T]) -> &'a mut SliceEnv<T> {
        // SAFETY:
        // - `SliceEnv<T>` is equivalent to an `[T]` internally
        #[allow(
            clippy::as_conversions,
            reason = "ptr::cast is not available for unsized types"
        )]
        unsafe {
            &mut *(std::ptr::from_mut(slice) as *mut SliceEnv<T>)
        }
    }
}
