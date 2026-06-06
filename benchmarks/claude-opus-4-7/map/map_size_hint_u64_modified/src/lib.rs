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
    //
    // Inlined by hand: `Range::size_hint` extracts to the unmodeled
    // `core_models.iter.traits.iterator.Iterator.size_hint`, so `lake build`
    // fails. Field access on the modeled `Range` struct (`self.iter.start` /
    // `self.iter.end`) does survive extraction.
    // Cf. rewrite_patterns/range_next_to_field_access.rs and the sibling
    // proof_patterns/map_next_u64_modified.
    //
    // Semantics: for `Range<u64>` the stdlib returns `(0, Some(0))` on an
    // empty/inverted range, and otherwise computes `diff = end - start` as
    // `usize`, returning `(diff, Some(diff))` when it fits and
    // `(usize::MAX, None)` otherwise. On the 64-bit targets the test suite
    // runs on, `usize == u64` so the cast is lossless and the `None` branch
    // is unreachable for any concrete range; the tests confirm this.
    #[inline]
    pub fn size_hint(&self) -> (usize, Option<usize>) {
        if self.iter.start >= self.iter.end {
            (0, Some(0))
        } else {
            let diff = self.iter.end - self.iter.start;
            let n = diff as usize;
            (n, Some(n))
        }
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

    // Contract: `size_hint` must return exactly what the inner iterator's
    // `size_hint` returns. Check pass-through across several distinct range
    // configurations (empty, singleton, small, large, offset).
    #[test]
    fn size_hint_matches_inner_for_various_ranges() {
        let cases: [Range<u64>; 5] =
            [0..0, 0..1, 0..100, 7..42, 1_000..2_000];
        for r in cases {
            let expected = r.clone().size_hint();
            let m = Map { iter: r, f: |x| x };
            assert_eq!(m.size_hint(), expected);
        }
    }

    // Contract: `size_hint` depends only on `iter`, not on `f`. Two `Map`s
    // with identical ranges but different closures must report the same hint.
    // (Independent claim — pass-through alone doesn't say f is irrelevant.)
    #[test]
    fn size_hint_is_independent_of_f() {
        let m_identity = Map { iter: 3..20, f: |x| x };
        let m_shifted = Map { iter: 3..20, f: |x| x.wrapping_add(7) };
        let m_constant = Map { iter: 3..20, f: |_| 0 };
        let hint = m_identity.size_hint();
        assert_eq!(m_shifted.size_hint(), hint);
        assert_eq!(m_constant.size_hint(), hint);
    }

    // Boundary: an empty range (start == end) yields (0, Some(0)).
    #[test]
    fn size_hint_empty_range_is_zero_exact() {
        let m = Map { iter: 5..5, f: |x| x };
        assert_eq!(m.size_hint(), (0, Some(0)));
    }

    // Boundary: a "reversed" range (start > end) is also treated as empty
    // by `Range<u64>`, so the hint is (0, Some(0)).
    #[test]
    fn size_hint_reversed_range_is_zero_exact() {
        let m = Map { iter: 10..5, f: |x| x };
        assert_eq!(m.size_hint(), (0, Some(0)));
    }

    // `size_hint` does not modify the iterator — calling it twice yields the
    // same value, and the underlying range is unchanged. (Captures the
    // implicit "pure / read-only" part of the contract.)
    #[test]
    fn size_hint_is_pure() {
        let m = Map { iter: 0..10, f: |x| x };
        let first = m.size_hint();
        let second = m.size_hint();
        assert_eq!(first, second);
        // Range is untouched.
        assert_eq!(m.iter.clone().count(), 10);
    }
}
