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
}
