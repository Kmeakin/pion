use std::fmt;
use std::ops::{Add, Index, Range};

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct BytePos(u32);

impl Add<u32> for BytePos {
    type Output = Self;
    fn add(self, rhs: u32) -> Self::Output { Self(self.0 + rhs) }
}

#[allow(clippy::cast_possible_truncation)]
// REASON: truncations are made explicit by the methods
impl BytePos {
    pub fn new(value: u32) -> Self { Self(value) }

    pub const fn truncate_usize(value: usize) -> Self { Self(value as u32) }

    pub const fn truncate_u64(value: u64) -> Self { Self(value as u32) }

    pub const fn extend_u64(self) -> u64 { self.0 as u64 }

    pub const fn extend_usize(self) -> usize { self.0 as usize }
}

impl From<u32> for BytePos {
    fn from(value: u32) -> Self { Self(value) }
}

impl From<BytePos> for u32 {
    fn from(pos: BytePos) -> Self { pos.0 }
}

impl From<BytePos> for u64 {
    fn from(pos: BytePos) -> Self { pos.extend_u64() }
}

impl From<BytePos> for usize {
    fn from(pos: BytePos) -> Self { pos.extend_usize() }
}

impl From<text_size::TextSize> for BytePos {
    fn from(size: text_size::TextSize) -> Self { Self(u32::from(size)) }
}

impl fmt::Debug for BytePos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.0.fmt(f) }
}

impl fmt::Display for BytePos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.0.fmt(f) }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct ByteSpan {
    pub start: BytePos,
    pub end: BytePos,
}

impl From<BytePos> for ByteSpan {
    fn from(start: BytePos) -> Self { Self::new(start, BytePos(start.0 + 1)) }
}

impl Index<ByteSpan> for str {
    type Output = Self;
    fn index(&self, span: ByteSpan) -> &Self::Output { &self[Range::<usize>::from(span)] }
}

impl Index<ByteSpan> for String {
    type Output = str;
    fn index(&self, span: ByteSpan) -> &Self::Output { &self[Range::<usize>::from(span)] }
}

impl ByteSpan {
    pub const fn new(start: BytePos, end: BytePos) -> Self { Self { start, end } }

    pub const fn truncate_usize(range: Range<usize>) -> Self {
        Self::new(
            BytePos::truncate_usize(range.start),
            BytePos::truncate_usize(range.end),
        )
    }

    pub const fn truncate_u64(range: Range<u64>) -> Self {
        Self::new(
            BytePos::truncate_u64(range.start),
            BytePos::truncate_u64(range.end),
        )
    }
}

impl From<ByteSpan> for Range<usize> {
    fn from(span: ByteSpan) -> Self { span.start.into()..span.end.into() }
}

impl From<ByteSpan> for Range<u32> {
    fn from(span: ByteSpan) -> Self { span.start.into()..span.end.into() }
}

impl From<Range<u32>> for ByteSpan {
    fn from(range: Range<u32>) -> Self { Self::new(range.start.into(), range.end.into()) }
}

impl From<text_size::TextRange> for ByteSpan {
    fn from(range: text_size::TextRange) -> Self {
        Self::new(range.start().into(), range.end().into())
    }
}

impl fmt::Debug for ByteSpan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

impl fmt::Display for ByteSpan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}
