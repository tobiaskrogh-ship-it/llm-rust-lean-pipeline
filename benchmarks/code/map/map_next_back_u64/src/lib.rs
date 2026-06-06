//! Extracted from
//! `core::iter::adapters::map::<impl DoubleEndedIterator for Map<I, F>>::next_back`.
//!
//! Original:
//! ```ignore
//! #[inline]
//! fn next_back(&mut self) -> Option<B> {
//!     self.iter.next_back().map(&mut self.f)
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
    /// Pull the next item from the back of the inner iterator and map it.
    #[inline]
    pub fn next_back(&mut self) -> Option<u64> {
        self.iter.next_back().map(&mut self.f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from `tests/iter/adapters/map.rs::test_double_ended_map`:
    //   let mut it = xs.iter().map(|&x| x * -1);
    //   ...
    //   assert_eq!(it.next_back(), Some(-6));
    //   assert_eq!(it.next_back(), Some(-5));
    //   ...
    //   assert_eq!(it.next_back(), Some(-4));
    //
    // Translated to a Range<u64> with a u64-safe mapper. The intent — that the
    // back end yields the last mapped element — survives.
    #[test]
    fn next_back_yields_last_mapped_item() {
        let mut it = Map { iter: 1..7, f: |x| x * 2 };
        assert_eq!(it.next_back(), Some(12));
        assert_eq!(it.next_back(), Some(10));
        assert_eq!(it.next_back(), Some(8));
        assert_eq!(it.next_back(), Some(6));
        assert_eq!(it.next_back(), Some(4));
        assert_eq!(it.next_back(), Some(2));
        assert_eq!(it.next_back(), None);
    }

    // Tail of `test_map_try_folds`:
    //   let mut iter = (0..40).map(|x| x + 10);
    //   ...
    //   assert_eq!(iter.next_back(), Some(46));
    //
    // We translate the index arithmetic to u64. The last element of
    // (0..40).map(|x| x + 10) is 49; after popping one back we have 48; etc.
    // The test below skips three from the back, so the next is 49 - 3 = 46.
    #[test]
    fn next_back_after_partial_drain() {
        let mut iter = Map { iter: 0..40, f: |x| x + 10 };
        // Pop three from the back.
        iter.next_back();
        iter.next_back();
        iter.next_back();
        assert_eq!(iter.next_back(), Some(46));
    }
}
