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
    //
    // `Range<u64>::next_back()` is a `DoubleEndedIterator` method which the
    // Hax Lean prelude does not model — the original `self.iter.next_back()
    // .map(&mut self.f)` extracts to a `sorry` body. Sibling rewrite
    // `iter_fold_to_while_loop.rs` shows that the prelude DOES model the
    // `Range` struct fields (`self.iter.start`, `self.iter.end`) directly,
    // and `Option` constructors (`Some` / `None`) work. Inline the
    // `next_back` + `Option::map` semantics by hand:
    //   - empty range (start >= end): return None, no mutation
    //   - non-empty range: decrement end and return Some(f(end - 1))
    #[inline]
    pub fn next_back(&mut self) -> Option<u64> {
        if self.iter.start >= self.iter.end {
            None
        } else {
            self.iter.end = self.iter.end - 1;
            Some((self.f)(self.iter.end))
        }
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

    // ---------------------------------------------------------------------
    // Property-based contract tests.
    //
    // The contract of `next_back` has two independent clauses:
    //
    //   (1) Empty-range clause. If `iter.start >= iter.end`, the call
    //       returns `None` and leaves `iter` unchanged (no work done, `f`
    //       not invoked).
    //
    //   (2) Non-empty-range clause. If `iter.start < iter.end`, the call
    //       returns `Some(f(iter.end - 1))`, decrements `iter.end` by one,
    //       and leaves `iter.start` unchanged.
    //
    // There is no precondition (the function is always safely callable)
    // and no failure mode beyond returning `None` on an empty range.
    // ---------------------------------------------------------------------

    // A non-trivial mapping function used by the property tests below. We
    // pick a `fn(u64) -> u64` (not a closure) so it matches the field
    // type, and use `wrapping_*` so it is total on the entire u64 domain
    // — the contract of `next_back` says nothing about overflow in `f`,
    // and the tests should not be the thing that perturbs that.
    fn probe_fn(x: u64) -> u64 {
        x.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(0xDEADBEEF)
    }

    // Clause (1): on every empty range we sweep, `next_back` returns
    // `None` and the `Range` endpoints are left exactly as they were.
    //
    // This catches a buggy implementation that, say, returns
    // `Some(f(end))` regardless, or that mutates `start`/`end` on the
    // empty path.
    #[test]
    fn prop_empty_range_returns_none_and_preserves_iter() {
        for start in 0u64..16 {
            // `end <= start` covers both `end == start` (canonically
            // empty) and `end < start` (already-exhausted form).
            for end in 0u64..=start {
                let mut m = Map { iter: start..end, f: probe_fn };
                let r = m.next_back();
                assert_eq!(r, None, "start={start}, end={end}");
                assert_eq!(m.iter.start, start, "start={start}, end={end}");
                assert_eq!(m.iter.end, end, "start={start}, end={end}");
            }
        }
    }

    // Clause (2): on every non-empty range we sweep, `next_back` returns
    // `Some(f(end - 1))`, `iter.end` is decremented by exactly one, and
    // `iter.start` is untouched.
    //
    // This catches off-by-one bugs (e.g. yielding `f(end)` or `f(start)`),
    // failure to advance the range, or perturbation of `start`.
    #[test]
    fn prop_nonempty_range_pops_and_maps_back_element() {
        for start in 0u64..16 {
            for end in (start + 1)..(start + 24) {
                let mut m = Map { iter: start..end, f: probe_fn };
                let r = m.next_back();
                assert_eq!(
                    r,
                    Some(probe_fn(end - 1)),
                    "start={start}, end={end}",
                );
                assert_eq!(m.iter.start, start, "start={start}, end={end}");
                assert_eq!(m.iter.end, end - 1, "start={start}, end={end}");
            }
        }
    }

    // Boundary case: the contract must also hold at the top of the u64
    // domain. A buggy implementation that, e.g., used `end` instead of
    // `end - 1` would overflow here; the standard-library impl does not.
    #[test]
    fn prop_contract_holds_at_u64_max_boundary() {
        // Non-empty range ending at u64::MAX: yields f(u64::MAX - 1)
        // and the range shrinks by one from the back.
        let mut m = Map {
            iter: (u64::MAX - 3)..u64::MAX,
            f: probe_fn,
        };
        assert_eq!(m.next_back(), Some(probe_fn(u64::MAX - 1)));
        assert_eq!(m.iter.start, u64::MAX - 3);
        assert_eq!(m.iter.end, u64::MAX - 1);

        // Empty range pinned at u64::MAX: returns None, preserves iter.
        let mut m = Map {
            iter: u64::MAX..u64::MAX,
            f: probe_fn,
        };
        assert_eq!(m.next_back(), None);
        assert_eq!(m.iter.start, u64::MAX);
        assert_eq!(m.iter.end, u64::MAX);
    }
}
