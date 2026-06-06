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

    // A small fixed bank of mapper functions used by the property tests below.
    // We pick three structurally different functions so that a buggy
    // implementation cannot trivially pass (e.g. one that always returns its
    // input unchanged would fail on the multiply and xor variants).
    const MAPPERS: &[fn(u64) -> u64] = &[
        |x| x,                              // identity
        |x| x.wrapping_mul(3),              // arithmetic, exercises wrapping
        |x| x ^ 0x5A5A_5A5A_5A5A_5A5A_u64,  // bitwise
    ];

    // Property (postcondition, empty case):
    //   Forall start, end with start >= end, and forall mapper f:
    //     Map { iter: start..end, f }.next() == None
    //     and the inner range is left unchanged.
    //
    // Captures the "empty range yields None and is a no-op on state" contract
    // clause. Includes the boundary case start == end at several positions
    // (including u64::MAX) and inverted ranges where start > end.
    #[test]
    fn prop_empty_range_yields_none_and_is_noop() {
        let empties: &[(u64, u64)] = &[
            (0, 0),
            (1, 1),
            (42, 42),
            (u64::MAX, u64::MAX),
            (10, 5),       // inverted
            (u64::MAX, 0), // inverted, extreme
        ];
        for &f in MAPPERS {
            for &(lo, hi) in empties {
                let mut m = Map { iter: lo..hi, f };
                assert_eq!(m.next(), None, "empty range {}..{} should yield None", lo, hi);
                assert_eq!(m.iter.start, lo, "start must be unchanged on empty");
                assert_eq!(m.iter.end, hi, "end must be unchanged on empty");
                // Calling again still yields None (the empty state is stable).
                assert_eq!(m.next(), None);
            }
        }
    }

    // Property (postcondition, non-empty case):
    //   Forall start, end with start < end, and forall mapper f:
    //     let mut m = Map { iter: start..end, f };
    //     m.next() == Some(f(start))
    //     m.iter.start == start + 1
    //     m.iter.end   == end
    //
    // Captures the "single-step" contract: which value is produced and how
    // the iterator state advances. This is the core observable behavior of
    // `next` on a non-empty range, independent of the choice of `f`.
    #[test]
    fn prop_nonempty_yields_some_f_start_and_advances_by_one() {
        let nonempties: &[(u64, u64)] = &[
            (0, 1),
            (0, 100),
            (50, 51),
            (1_000, 1_001),
            (123, 456),
            (u64::MAX - 1, u64::MAX),
        ];
        for &f in MAPPERS {
            for &(lo, hi) in nonempties {
                let mut m = Map { iter: lo..hi, f };
                let result = m.next();
                assert_eq!(result, Some(f(lo)), "next on {}..{} should be Some(f({}))", lo, hi, lo);
                assert_eq!(m.iter.start, lo + 1, "start must advance by exactly 1");
                assert_eq!(m.iter.end, hi, "end must be unchanged");
            }
        }
    }

    // Property (full-drain agreement):
    //   Forall start, end with start <= end, and forall mapper f:
    //     repeatedly calling `Map { iter: start..end, f }.next()` yields
    //     exactly the sequence Some(f(start)), Some(f(start+1)), ...,
    //     Some(f(end-1)), then None forever.
    //
    // This is the inductive composition of the two single-step properties
    // above; we keep it as one combined check because the "and then None
    // forever" tail is the cheapest place to also pin down stability of the
    // exhausted state across multiple post-exhaustion calls.
    #[test]
    fn prop_full_drain_matches_range_then_map() {
        let cases: &[(u64, u64)] = &[
            (0, 0),     // empty: just None
            (0, 1),     // singleton
            (3, 8),     // small interior range
            (100, 110), // larger range
        ];
        for &f in MAPPERS {
            for &(lo, hi) in cases {
                let mut m = Map { iter: lo..hi, f };
                for k in lo..hi {
                    assert_eq!(m.next(), Some(f(k)), "step {} of {}..{}", k, lo, hi);
                }
                // Past the end: None, and stays None.
                assert_eq!(m.next(), None);
                assert_eq!(m.next(), None);
            }
        }
    }
}
