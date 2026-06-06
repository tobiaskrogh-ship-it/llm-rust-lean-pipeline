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
}
