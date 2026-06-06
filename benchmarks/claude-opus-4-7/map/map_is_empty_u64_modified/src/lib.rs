//! Extracted from
//! `core::iter::adapters::map::<impl ExactSizeIterator for Map<I, F>>::is_empty`.
//!
//! Original:
//! ```ignore
//! fn is_empty(&self) -> bool {
//!     self.iter.is_empty()
//! }
//! ```
//!
//! Monomorphized with `I = core::ops::Range<u64>` and `F = fn(u64) -> u64`.
//!
//! Notes:
//! - `ExactSizeIterator::is_empty` is itself an unstable method whose default
//!   body is `self.len() == 0`. Per the skill's "inline trait method calls"
//!   rule we inline that default body.
//! - `Range<u64>` does not implement `ExactSizeIterator` on stable, so the
//!   inner `len()` is itself inlined as `end - start`. The composed result is
//!   simply `start >= end` — exactly the predicate `Range::is_empty` would
//!   return (and the same body the `Iterator::next` impl uses to decide
//!   exhaustion).

use core::ops::Range;

/// Concrete monomorphization of `core::iter::adapters::map::Map<I, F>`.
pub struct Map {
    pub iter: Range<u64>,
    pub f: fn(u64) -> u64,
}

impl Map {
    /// Report whether the inner iterator is empty.
    pub fn is_empty(&self) -> bool {
        // `ExactSizeIterator::is_empty` -> `self.len() == 0`,
        // and `<Range<u64>>::len()` inlines to `end - start` (as usize).
        // The composed predicate simplifies to `start >= end`.
        self.iter.start >= self.iter.end
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // No direct source test for `Map::is_empty` alone. Skill rule: write a
    // minimum of one trivial test.
    #[test]
    fn is_empty_false_for_nonempty_range() {
        let m = Map { iter: 0..10, f: |x| x + 3 };
        assert!(!m.is_empty());
    }

    #[test]
    fn is_empty_true_for_empty_range() {
        let m = Map { iter: 5..5, f: |x| x + 3 };
        assert!(m.is_empty());
    }

    #[test]
    fn is_empty_after_full_drain() {
        let mut m = Map { iter: 0..3, f: |x| x + 1 };
        while m.iter.next().is_some() {}
        assert!(m.is_empty());
    }

    // ---------------------------------------------------------------------
    // Property-based tests.
    //
    // Contract of `Map::is_empty`:
    //   - precondition:  none (total function on `&Map`).
    //   - postcondition: result == (self.iter.start >= self.iter.end).
    //   - failure modes: none.
    //
    // The postcondition contains two independent semantic claims:
    //   (1) the result is `start >= end` -- note the non-strict comparison,
    //       so `start == end` already counts as empty;
    //   (2) the field `f` does not appear in the postcondition, i.e. the
    //       answer does not depend on the mapping function.
    // Each claim gets its own test.
    // ---------------------------------------------------------------------

    /// Postcondition: `m.is_empty()` matches `start >= end` across a
    /// representative sweep of `(start, end)` pairs, including the
    /// `start == end` boundary, the `start > end` (degenerate) case,
    /// and `u64` extremes.
    #[test]
    fn property_matches_start_ge_end() {
        let points: [u64; 10] = [
            0,
            1,
            2,
            7,
            100,
            12345,
            u64::MAX / 2,
            u64::MAX - 1,
            u64::MAX,
            999,
        ];
        let f: fn(u64) -> u64 = |x| x.wrapping_add(7);
        for &s in &points {
            for &e in &points {
                let m = Map { iter: s..e, f };
                assert_eq!(
                    m.is_empty(),
                    s >= e,
                    "is_empty() disagreed with start >= end at start={}, end={}",
                    s,
                    e,
                );
            }
        }
    }

    /// Postcondition does not mention `f`: for any fixed range, swapping
    /// the mapping function must not change the answer.
    #[test]
    fn property_independent_of_mapper_fn() {
        let fs: [fn(u64) -> u64; 5] = [
            |x| x,
            |_| 0,
            |_| u64::MAX,
            |x| x.wrapping_add(1),
            |x| x.wrapping_mul(2),
        ];
        let ranges: [(u64, u64); 7] = [
            (0, 0),
            (0, 1),
            (0, 10),
            (10, 0),
            (5, 5),
            (u64::MAX, u64::MAX),
            (0, u64::MAX),
        ];
        for &(s, e) in &ranges {
            let expected = s >= e;
            for &f in &fs {
                let m = Map { iter: s..e, f };
                assert_eq!(
                    m.is_empty(),
                    expected,
                    "is_empty() depended on `f` at start={}, end={}",
                    s,
                    e,
                );
            }
        }
    }
}
