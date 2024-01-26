#![feature(maybe_uninit_slice)]

pub mod identity;
pub mod location;
pub mod numeric_conversions;
pub mod slice_vec;
pub mod source;
pub mod symbol;

pub fn slice_eq_by_key<T, V: PartialEq>(
    xs: &[T],
    ys: &[T],
    key_fn: impl Copy + Fn(&T) -> V,
) -> bool {
    if xs.len() != ys.len() {
        return false;
    }

    Iterator::eq(xs.iter().map(key_fn), ys.iter().map(key_fn))
}

pub fn slice_eq_by_keys<T1, T2, V1: PartialEq<V2>, V2>(
    xs: &[T1],
    ys: &[T2],
    key_fn1: impl Fn(&T1) -> V1,
    key_fn2: impl Fn(&T2) -> V2,
) -> bool {
    if xs.len() != ys.len() {
        return false;
    }

    Iterator::eq(xs.iter().map(key_fn1), ys.iter().map(key_fn2))
}
