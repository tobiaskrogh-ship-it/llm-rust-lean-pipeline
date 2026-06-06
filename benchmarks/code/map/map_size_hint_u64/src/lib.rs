//! Extracted from
//! `core::iter::adapters::map::<impl Iterator for Map<I, F>>::size_hint`.
//!
//! Original:
//! ```ignore
//! #[inline]
//! fn size_hint(&self) -> (usize, Option<usize>) {
//!     self.iter.size_hint()
//! }
//! ```
//!
//! Monomorphized with `I = core::ops::Range<u64>` and `F = fn(u64) -> u64`.

use core::ops::Range;

/// Concrete monomorphization of `core::iter::adapters::map::Map<I, F>`.
pub struct Map {
    pub iter: Range<u64>,
    pub f: fn(u64) -> u64,
}

impl Map {
    /// Return the inner iterator's `size_hint` unchanged — `Map` is 1:1.
    #[inline]
    pub fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // No direct source test for `size_hint` on `Map`. Skill rule: write a
    // minimum of one trivial test.

    #[test]
    fn size_hint_passes_through_full_range() {
        let m = Map { iter: 0..10, f: |x| x + 3 };
        assert_eq!(m.size_hint(), (10, Some(10)));
    }

    #[test]
    fn size_hint_passes_through_after_partial_consumption() {
        let mut m = Map { iter: 0..10, f: |x| x + 3 };
        m.iter.next();
        m.iter.next();
        assert_eq!(m.size_hint(), (8, Some(8)));
    }

    #[test]
    fn size_hint_passes_through_after_back_consumption() {
        let mut m = Map { iter: 0..10, f: |x| x + 3 };
        m.iter.next_back();
        assert_eq!(m.size_hint(), (9, Some(9)));
    }
}
