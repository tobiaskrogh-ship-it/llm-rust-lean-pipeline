//! Extracted from
//! `core::iter::adapters::map::<impl DoubleEndedIterator for Map<I, F>>::try_rfold`.
//!
//! Original:
//! ```ignore
//! fn try_rfold<Acc, G, R>(&mut self, init: Acc, g: G) -> R
//! where
//!     Self: Sized,
//!     G: FnMut(Acc, Self::Item) -> R,
//!     R: Try<Output = Acc>,
//! {
//!     self.iter.try_rfold(init, map_try_fold(&mut self.f, g))
//! }
//! ```
//!
//! Monomorphized with `I = core::ops::Range<u64>`, `F = fn(u64) -> u64`,
//! `Acc = u64`, and `R = Option<u64>`. The private helper `map_try_fold` is
//! inlined below.

use core::ops::Range;

/// Concrete monomorphization of `core::iter::adapters::map::Map<I, F>`.
pub struct Map {
    pub iter: Range<u64>,
    pub f: fn(u64) -> u64,
}

/// Inlined private helper `map_try_fold` from
/// `core::iter::adapters::map::map_try_fold`, monomorphized to `u64` /
/// `Option<u64>`.
fn map_try_fold<'a>(
    f: &'a mut impl FnMut(u64) -> u64,
    mut g: impl FnMut(u64, u64) -> Option<u64> + 'a,
) -> impl FnMut(u64, u64) -> Option<u64> + 'a {
    move |acc, elt| g(acc, f(elt))
}

impl Map {
    /// Try-fold from the back through `g` after applying the inner mapper.
    pub fn try_rfold(
        &mut self,
        init: u64,
        g: impl FnMut(u64, u64) -> Option<u64>,
    ) -> Option<u64> {
        self.iter.try_rfold(init, map_try_fold(&mut self.f, g))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from `tests/iter/adapters/map.rs::test_map_try_folds`:
    //   let f = &|acc, x| i32::checked_add(2 * acc, x);
    //   assert_eq!((0..10).map(|x| x + 3).try_rfold(7, f),
    //              (3..13).try_rfold(7, f));
    // Translated to u64 / Option<u64>.
    #[test]
    fn try_rfold_matches_shifted_try_rfold() {
        let g = |acc: u64, x: u64| u64::checked_add(2 * acc, x);
        let mut m = Map { iter: 0..10, f: |x| x + 3 };
        let mapped = m.try_rfold(7, g);
        let unmapped = (3..13u64).try_rfold(7u64, g);
        assert_eq!(mapped, unmapped);
    }

    // Second block of `test_map_try_folds` exercising the back end:
    //   let mut iter = (0..40).map(|x| x + 10);
    //   ...
    //   assert_eq!(iter.try_rfold(0, i8::checked_add), None);
    //   assert_eq!(iter.next_back(), Some(46));
    //
    // Translated to u64 with a manual `u8::MAX` ceiling.
    #[test]
    fn try_rfold_short_circuits_on_overflow() {
        let mut iter = Map { iter: 0..40, f: |x| x + 10 };
        let g = |acc: u64, x: u64| {
            let s = acc + x;
            if s > u8::MAX as u64 { None } else { Some(s) }
        };
        assert_eq!(iter.try_rfold(0, g), None);
        // After the short circuit the back end still has elements.
        assert!(iter.iter.next_back().is_some());
    }

    // ---------------------------------------------------------------------
    // Property-based tests
    // ---------------------------------------------------------------------

    /// Hand-rolled reference: fold `g` over `f(x)` for `x` from `end-1` down to
    /// `start`, short-circuiting on `None`. Returns the final result together
    /// with the value `iter.end` should have after the call (i.e. `start` on
    /// success, or the element that caused the short-circuit on failure).
    fn reference_back_fold(
        start: u64,
        end: u64,
        init: u64,
        f: fn(u64) -> u64,
        g: fn(u64, u64) -> Option<u64>,
    ) -> (Option<u64>, u64) {
        let mut acc = init;
        let mut cur = end;
        while cur > start {
            cur -= 1;
            match g(acc, f(cur)) {
                Some(new_acc) => acc = new_acc,
                None => return (None, cur),
            }
        }
        (Some(acc), start)
    }

    // Property: for every `(start, end, init, f, g)`, `Map::try_rfold` returns
    // the same value as `reference_back_fold` (postcondition on the value) AND
    // leaves `iter.start` unchanged while setting `iter.end` to the position
    // implied by the consumed back-portion (postcondition on iterator state,
    // including the precise short-circuit point). A buggy implementation that
    // iterated front-to-back, applied `g` before `f`, mis-handled short-circuit,
    // or over-/under-consumed the iterator would be caught.
    #[test]
    fn try_rfold_matches_reference_back_fold_and_iter_state() {
        let fs: &[fn(u64) -> u64] = &[
            |x| x,
            |x| x + 3,
            |x| x.wrapping_mul(7),
        ];
        fn checked(acc: u64, x: u64) -> Option<u64> {
            acc.checked_add(x)
        }
        fn cap_add(acc: u64, x: u64) -> Option<u64> {
            let s = acc.checked_add(x)?;
            if s > 200 { None } else { Some(s) }
        }
        fn always_none(_: u64, _: u64) -> Option<u64> {
            None
        }
        let gs: &[fn(u64, u64) -> Option<u64>] = &[checked, cap_add, always_none];

        for &f in fs {
            for &g in gs {
                for start in 0..4u64 {
                    for length in 0..12u64 {
                        let end = start + length;
                        for &init in &[0u64, 5, 100] {
                            let mut m = Map { iter: start..end, f };
                            let actual = m.try_rfold(init, g);
                            let (expected_val, expected_end) =
                                reference_back_fold(start, end, init, f, g);
                            assert_eq!(
                                actual, expected_val,
                                "value mismatch for {start}..{end}, init={init}",
                            );
                            assert_eq!(
                                m.iter.start, start,
                                "iter.start unexpectedly changed for {start}..{end}",
                            );
                            assert_eq!(
                                m.iter.end, expected_end,
                                "iter.end mismatch for {start}..{end}, init={init}",
                            );
                        }
                    }
                }
            }
        }
    }

    // Property: on an empty range, `try_rfold` returns `Some(init)` and does
    // not invoke `f` or `g`. We probe non-invocation indirectly by picking
    // `g = |_, _| None`: if `g` were called even once, the result would be
    // `None`, not `Some(init)`.
    #[test]
    fn try_rfold_empty_range_returns_init_without_calls() {
        for start in 0..5u64 {
            for &init in &[0u64, 7, 1_000] {
                let mut m = Map {
                    iter: start..start,
                    f: |x| x.wrapping_add(1),
                };
                let result = m.try_rfold(init, |_, _| None);
                assert_eq!(
                    result,
                    Some(init),
                    "empty range should return Some(init) without invoking g",
                );
                assert_eq!(
                    m.iter,
                    start..start,
                    "empty iter should remain empty after the call",
                );
            }
        }
    }
}
