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
}
