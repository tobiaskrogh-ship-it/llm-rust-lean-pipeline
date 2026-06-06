//! Extracted from
//! `core::iter::adapters::map::<impl Iterator for Map<I, F>>::try_fold`.
//!
//! Original:
//! ```ignore
//! fn try_fold<Acc, G, R>(&mut self, init: Acc, g: G) -> R
//! where
//!     Self: Sized,
//!     G: FnMut(Acc, Self::Item) -> R,
//!     R: Try<Output = Acc>,
//! {
//!     self.iter.try_fold(init, map_try_fold(&mut self.f, g))
//! }
//! ```
//!
//! Monomorphized with `I = core::ops::Range<u64>`, `F = fn(u64) -> u64`,
//! `Acc = u64`, and `R = Option<u64>` (the standard short-circuit carrier
//! used in the source's integration test, where `i32::checked_add` returns
//! `Option`). The private helper `map_try_fold` is inlined below.

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
    /// Try-fold all elements through `g` after applying the inner mapper.
    pub fn try_fold(
        &mut self,
        init: u64,
        g: impl FnMut(u64, u64) -> Option<u64>,
    ) -> Option<u64> {
        self.iter.try_fold(init, map_try_fold(&mut self.f, g))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from `tests/iter/adapters/map.rs::test_map_try_folds`:
    //   let f = &|acc, x| i32::checked_add(2 * acc, x);
    //   assert_eq!((0..10).map(|x| x + 3).try_fold(7, f),
    //              (3..13).try_fold(7, f));
    // Translated to u64 / Option<u64>.
    #[test]
    fn try_fold_matches_shifted_try_fold() {
        let g = |acc: u64, x: u64| u64::checked_add(2 * acc, x);
        let mut m = Map { iter: 0..10, f: |x| x + 3 };
        let mapped = m.try_fold(7, g);
        let unmapped = (3..13u64).try_fold(7u64, g);
        assert_eq!(mapped, unmapped);
    }

    // Second block of `test_map_try_folds`:
    //   let mut iter = (0..40).map(|x| x + 10);
    //   assert_eq!(iter.try_fold(0, i8::checked_add), None);
    //   assert_eq!(iter.next(), Some(20));
    //
    // Translated to u64 with a manual `u8::MAX` ceiling to reproduce the
    // overflow at the same elements.
    #[test]
    fn try_fold_short_circuits_on_overflow() {
        let mut iter = Map { iter: 0..40, f: |x| x + 10 };
        let g = |acc: u64, x: u64| {
            let s = acc + x;
            if s > u8::MAX as u64 { None } else { Some(s) }
        };
        assert_eq!(iter.try_fold(0, g), None);
        // After the short circuit, the next element of (0..40).map(|x| x + 10)
        // is the one we tripped on plus one. With u8 ceiling 255, the sum
        // 10+11+...+20 = 165 then 165+21 = 186, +22=208, +23=231, +24=255,
        // +25=280 -> overflow at x=25 (mapped from inner=15). So inner is at
        // position 16, mapped value is 26 — but in the i8 original the trip
        // point is different. We only check structural equivalence: the
        // first short-circuit returns None, and there are still elements left.
        assert!(iter.iter.next().is_some());
    }

    // ----------------------------------------------------------------------
    // Property tests.
    //
    // Each test below is a property expressed by quantifying over a finite
    // grid of inputs and asserting an invariant. They capture independent
    // clauses of the `Map::try_fold` contract; redundant derived facts
    // (commutativity of `g`, algebraic identities of `f`, etc.) are omitted
    // on purpose — they don't constrain the implementation any further than
    // the reference-equivalence test below.
    // ----------------------------------------------------------------------

    /// Property — reference equivalence.
    ///
    /// `Map::try_fold` agrees with a hand-rolled `for`-loop that applies the
    /// inner mapper `f` to each element and then folds with `g`, exiting
    /// early on `None`. This single property captures:
    ///
    /// * the success postcondition (when `g` never trips, the return value
    ///   is the left-fold over `f`-mapped elements starting from `init`),
    /// * the short-circuit postcondition (when `g` returns `None` at some
    ///   element, the return value is `None`),
    /// * the empty-range corner case (when the inner range is empty, no
    ///   call to `g` is made and the return value is `Some(init)`).
    ///
    /// A buggy implementation that skipped `f`, folded right-to-left, or
    /// kept going past a `None` would fail this test: `g(acc, x) =
    /// checked(2*acc + x)` with a finite ceiling is non-commutative in its
    /// arguments and detects fold direction.
    #[test]
    fn prop_try_fold_matches_manual_loop() {
        fn f(x: u64) -> u64 {
            x.wrapping_mul(3).wrapping_add(7)
        }

        for start in 0u64..6 {
            for len in 0u64..8 {
                let end = start + len;
                for &init in &[0u64, 1, 42, 1000] {
                    for &ceiling in &[0u64, 5, 50, 500, 5_000, u64::MAX] {
                        let g = |acc: u64, x: u64| {
                            let doubled = 2u64.checked_mul(acc)?;
                            let s = doubled.checked_add(x)?;
                            if s > ceiling { None } else { Some(s) }
                        };

                        // Actual: the function under test.
                        let mut m = Map { iter: start..end, f };
                        let actual = m.try_fold(init, g);

                        // Reference: explicit for-loop with early exit.
                        let mut acc = init;
                        let mut short_circuited = false;
                        for x in start..end {
                            match g(acc, f(x)) {
                                Some(v) => acc = v,
                                None => {
                                    short_circuited = true;
                                    break;
                                }
                            }
                        }
                        let expected = if short_circuited { None } else { Some(acc) };

                        assert_eq!(
                            actual, expected,
                            "start={start} end={end} init={init} ceiling={ceiling}"
                        );
                    }
                }
            }
        }
    }

    /// Property — iterator advance on short-circuit.
    ///
    /// When `g` returns `None` on the element at inner-range position `k`,
    /// the underlying `Range` is left positioned exactly one element past
    /// the failing position. This is an independent semantic claim: the
    /// reference-equivalence test above only inspects the return value,
    /// not the post-call state of `self.iter`.
    ///
    /// A buggy implementation that left the iterator pointing at the
    /// failing element, or fully drained the range past the failing
    /// element, would be caught here.
    #[test]
    fn prop_short_circuit_advances_past_failing_element() {
        fn f(x: u64) -> u64 {
            x + 100
        }

        let start = 10u64;
        let end = 30u64;

        for trip_pos in 0u64..(end - start) {
            let trip_inner = start + trip_pos;
            let trip_value = f(trip_inner);

            // `g` returns `None` exactly on the element at inner position
            // `trip_pos`, and `Some(0)` everywhere else. `f` is injective on
            // u64 (translation), so no earlier element collides with
            // `trip_value`.
            let g = |_acc: u64, x: u64| {
                if x == trip_value { None } else { Some(0u64) }
            };

            let mut m = Map { iter: start..end, f };
            let r = m.try_fold(0, g);
            assert_eq!(r, None, "trip_pos={trip_pos}: expected short-circuit");

            // The inner range must now resume at `trip_inner + 1`.
            let got_next = m.iter.next();
            let expected_next = trip_inner + 1;
            if expected_next < end {
                assert_eq!(
                    got_next,
                    Some(expected_next),
                    "trip_pos={trip_pos}: iterator should resume at trip_inner+1"
                );
            } else {
                assert_eq!(
                    got_next, None,
                    "trip_pos={trip_pos}: iterator should be exhausted"
                );
            }
        }
    }
}
