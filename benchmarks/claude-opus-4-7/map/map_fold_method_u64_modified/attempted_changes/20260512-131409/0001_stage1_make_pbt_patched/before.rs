//! Extracted from
//! `core::iter::adapters::map::<impl Iterator for Map<I, F>>::fold`.
//!
//! Original:
//! ```ignore
//! fn fold<Acc, G>(self, init: Acc, g: G) -> Acc
//! where
//!     G: FnMut(Acc, Self::Item) -> Acc,
//! {
//!     self.iter.fold(init, map_fold(self.f, g))
//! }
//! ```
//!
//! Monomorphized with `I = core::ops::Range<u64>`, `F = fn(u64) -> u64`, and
//! `Acc = u64`. The private helper `map_fold` is inlined below.

use core::ops::Range;

/// Concrete monomorphization of `core::iter::adapters::map::Map<I, F>`.
pub struct Map {
    pub iter: Range<u64>,
    pub f: fn(u64) -> u64,
}

/// Inlined private helper `map_fold` from
/// `core::iter::adapters::map::map_fold`, monomorphized to `u64`.
fn map_fold(
    mut f: impl FnMut(u64) -> u64,
    mut g: impl FnMut(u64, u64) -> u64,
) -> impl FnMut(u64, u64) -> u64 {
    move |acc, elt| g(acc, f(elt))
}

impl Map {
    /// Consume the `Map` by folding all elements through `g` after applying
    /// the inner mapper.
    pub fn fold(self, init: u64, g: impl FnMut(u64, u64) -> u64) -> u64 {
        self.iter.fold(init, map_fold(self.f, g))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Mirror of `tests/iter/adapters/map.rs::test_map_try_folds`, adapted to
    // the (non-try) `fold` path. The source asserts that a mapped fold equals
    // the equivalent fold over a shifted range.
    #[test]
    fn fold_matches_shifted_fold() {
        let g = |acc: u64, x: u64| 2 * acc + x;
        let mapped = Map { iter: 0..10, f: |x| x + 3 }.fold(7, g);
        let unmapped: u64 = (3..13u64).fold(7, g);
        assert_eq!(mapped, unmapped);
    }

    // Mirror of `tests/iter/adapters/map.rs::test_double_ended_map`, adapted
    // to compare the forward fold with a hand-summed expected value.
    #[test]
    fn fold_sums_with_offset() {
        let m = Map { iter: 1..7, f: |x| x * 2 };
        // 2+4+6+8+10+12 = 42
        let sum = m.fold(0, |a, b| a + b);
        assert_eq!(sum, 42);
    }
}
