#![feature(hash_set_entry)]

use core::fmt;
use std::hash::Hash;

use fxhash::FxHashSet;

pub struct Interned<'a, T: ?Sized>(&'a T);

pub type InternedStr<'a> = Interned<'a, str>;

impl<T: ?Sized> Copy for Interned<'_, T> {}

impl<T: ?Sized> Clone for Interned<'_, T> {
    fn clone(&self) -> Self { *self }
}

impl<T: ?Sized> PartialEq for Interned<'_, T> {
    fn eq(&self, other: &Self) -> bool { std::ptr::eq(self.0, other.0) }
}

impl<T: ?Sized> Eq for Interned<'_, T> {}

impl<T: ?Sized> Hash for Interned<'_, T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) { std::ptr::hash(self.0, state) }
}

impl<T: ?Sized> AsRef<T> for Interned<'_, T> {
    fn as_ref(&self) -> &T { self.0 }
}

impl<T: fmt::Debug + ?Sized> fmt::Debug for Interned<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt::Debug::fmt(self.0, f)
    }
}

impl<T: fmt::Display + ?Sized> fmt::Display for Interned<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt::Display::fmt(self.0, f)
    }
}

pub struct Interner<'a, T: ?Sized> {
    set: FxHashSet<&'a T>,
}

impl<T: ?Sized> Default for Interner<'_, T> {
    fn default() -> Self {
        Self {
            set: FxHashSet::default(),
        }
    }
}

impl<'a, T> Interner<'a, T>
where
    T: Eq + Hash + ?Sized,
{
    pub fn intern(&mut self, value: &'a T) -> Interned<'a, T> {
        Interned(self.set.get_or_insert(value))
    }
}
