//! Extracted from `core::iter::adapters::map::map_fold`.
//!
//! Original signature:
//! ```ignore
//! fn map_fold<T, B, Acc>(
//!     mut f: impl FnMut(T) -> B,
//!     mut g: impl FnMut(Acc, B) -> Acc,
//! ) -> impl FnMut(Acc, T) -> Acc
//! ```
//!
//! Monomorphized with `T = B = Acc = u64`.

/// Compose a unary mapper `f` and a binary folder `g` into a single fold step
/// that first applies `f` to the element and then folds the result with `g`.
pub fn map_fold(
    mut f: impl FnMut(u64) -> u64,
    mut g: impl FnMut(u64, u64) -> u64,
) -> impl FnMut(u64, u64) -> u64 {
    move |acc, elt| g(acc, f(elt))
}

#[cfg(test)]
mod tests {
    use super::*;

    // No direct source test exists for `map_fold` in isolation — it is exercised
    // through the `<Map as Iterator>::fold` impl. The closest source test is
    // `test_map_try_folds` in `tests/iter/adapters/map.rs`, which exercises the
    // try-fold variant. We transfer the spirit of that test (and the
    // `test_double_ended_map` test) translated to direct use of `map_fold`.

    #[test]
    fn map_fold_matches_unmapped_fold() {
        // Mirror the assertion shape from `test_map_try_folds`:
        //   (0..10).map(|x| x + 3).fold(7, g) == (3..13).fold(7, g)
        // for g = |acc, x| 2 * acc + x.
        let g = |acc: u64, x: u64| 2 * acc + x;
        let mapped: u64 = (0..10u64).fold(7, map_fold(|x| x + 3, g));
        let unmapped: u64 = (3..13u64).fold(7, g);
        assert_eq!(mapped, unmapped);
    }

    #[test]
    fn map_fold_sums_with_offset() {
        // Equivalent to (0..3).map(|x| x + 1).fold(0, |a,b| a + b) == 1+2+3 = 6.
        let mut step = map_fold(|x: u64| x + 1, |a, b| a + b);
        let mut acc: u64 = 0;
        for x in 0..3u64 {
            acc = step(acc, x);
        }
        assert_eq!(acc, 6);
    }

    #[test]
    fn map_fold_double_ended_like() {
        // Mirror the spirit of `test_double_ended_map`, but without the negation
        // (we are u64). Map each value through `x * 2` and fold by addition,
        // forward and backward. The two folds must agree.
        let data = [1u64, 2, 3, 4, 5, 6];
        let g = |a: u64, b: u64| a + b;
        let fwd: u64 = data.iter().copied().fold(0, map_fold(|x| x * 2, g));
        let rev: u64 = data.iter().rev().copied().fold(0, map_fold(|x| x * 2, g));
        assert_eq!(fwd, 42);
        assert_eq!(rev, 42);
    }

    // --- Contract-level property tests ------------------------------------
    //
    // The definitional contract of `map_fold(f, g)` is that the returned
    // step closure computes `g(acc, f(elt))` for every (acc, elt). The
    // sequence-level tests above only assert derived consequences of this
    // contract; the tests below pin down the single-step contract directly.

    #[test]
    fn map_fold_step_equals_compose_of_f_and_g() {
        // Postcondition: `map_fold(f, g)(acc, elt) == g(acc, f(elt))`.
        //
        // We choose:
        //   - `f` non-identity (so skipping `f` would be caught),
        //   - `g` non-commutative and non-trivial in both arguments (so
        //     skipping `g`, swapping g's two arguments, or applying `f` to
        //     `acc` instead of `elt` would all be caught).
        // We use wrapping arithmetic so the assertion is meaningful at the
        // boundaries of `u64` without depending on overflow-panic behaviour.
        let f = |x: u64| x.wrapping_mul(3).wrapping_add(7);
        let g = |a: u64, b: u64| a.wrapping_mul(5).wrapping_add(b);

        // Representative grid of (acc, elt) pairs, including boundary values.
        let sample = [
            0u64,
            1,
            2,
            17,
            1_000,
            u64::MAX / 2,
            u64::MAX - 1,
            u64::MAX,
        ];
        for &acc in &sample {
            for &elt in &sample {
                // Fresh `step` per pair: `map_fold` returns a `FnMut`, and we
                // want to test the per-call contract, not cross-call behaviour.
                let mut step = map_fold(f, g);
                let got = step(acc, elt);
                let expected = g(acc, f(elt));
                assert_eq!(got, expected, "acc = {acc}, elt = {elt}");
            }
        }
    }

    #[test]
    fn map_fold_invokes_f_and_g_exactly_once_per_call() {
        // FnMut contract: each invocation of the returned step closure must
        // call `f` exactly once and `g` exactly once. This is observable
        // because `f` and `g` are `FnMut` and may carry mutable state; calling
        // them too many or too few times would silently corrupt that state.
        use core::cell::Cell;
        let f_calls = Cell::new(0u64);
        let g_calls = Cell::new(0u64);

        let f = |x: u64| {
            f_calls.set(f_calls.get() + 1);
            x
        };
        let g = |a: u64, b: u64| {
            g_calls.set(g_calls.get() + 1);
            a.wrapping_add(b)
        };

        let mut step = map_fold(f, g);
        let n: u64 = 10;
        for i in 0..n {
            let _ = step(0, i);
        }
        drop(step);

        assert_eq!(f_calls.get(), n, "f should be called exactly once per step");
        assert_eq!(g_calls.get(), n, "g should be called exactly once per step");
    }
}
