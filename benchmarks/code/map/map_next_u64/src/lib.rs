//! Extracted from `core::iter::adapters::map::<impl Iterator for Map<I, F>>::next`.
//!
//! Original:
//! ```ignore
//! #[inline]
//! fn next(&mut self) -> Option<B> {
//!     self.iter.next().map(&mut self.f)
//! }
//! ```
//!
//! Monomorphized with `I = core::ops::Range<u64>` and `F = fn(u64) -> u64`,
//! producing `B = u64`.

use core::ops::Range;

/// Concrete monomorphization of `core::iter::adapters::map::Map<I, F>`.
pub struct Map {
    pub iter: Range<u64>,
    pub f: fn(u64) -> u64,
}

impl Map {
    /// Pull the next item from the inner iterator and map it.
    #[inline]
    pub fn next(&mut self) -> Option<u64> {
        self.iter.next().map(&mut self.f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from `tests/iter/adapters/map.rs::test_double_ended_map`:
    //   let mut it = xs.iter().map(|&x| x * -1);
    //   assert_eq!(it.next(), Some(-1));
    //   assert_eq!(it.next(), Some(-2));
    //
    // Translated to a Range<u64> with a u64-safe mapper.
    #[test]
    fn next_yields_mapped_items() {
        let mut it = Map { iter: 1..7, f: |x| x * 2 };
        assert_eq!(it.next(), Some(2));
        assert_eq!(it.next(), Some(4));
        assert_eq!(it.next(), Some(6));
        assert_eq!(it.next(), Some(8));
        assert_eq!(it.next(), Some(10));
        assert_eq!(it.next(), Some(12));
        assert_eq!(it.next(), None);
    }

    // Transferred from `tests/iter/adapters/map.rs::test_map_try_folds` (the
    // tail of that test, which exercises `iter.next()` after a try_fold):
    //   let mut iter = (0..40).map(|x| x + 10);
    //   ...
    //   assert_eq!(iter.next(), Some(20));
    #[test]
    fn next_after_partial_drain() {
        let mut iter = Map { iter: 0..40, f: |x| x + 10 };
        // Drain ten elements.
        for _ in 0..10 {
            iter.next();
        }
        // The eleventh element of (0..40).map(|x| x + 10) is 20.
        assert_eq!(iter.next(), Some(20));
    }
}
