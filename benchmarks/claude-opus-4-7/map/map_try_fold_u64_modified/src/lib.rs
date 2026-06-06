//! Extracted from `core::iter::adapters::map::map_try_fold`.
//!
//! Original signature:
//! ```ignore
//! fn map_try_fold<'a, T, B, Acc, R>(
//!     f: &'a mut impl FnMut(T) -> B,
//!     mut g: impl FnMut(Acc, B) -> R + 'a,
//! ) -> impl FnMut(Acc, T) -> R + 'a
//! ```
//!
//! Monomorphized with `T = B = Acc = u64` and `R = Option<u64>`. The original
//! used the unstable `Try` trait for `R`; we pick the standard
//! short-circuiting carrier `Option<u64>`, which is the same shape used in the
//! integration test `test_map_try_folds` (`i32::checked_add` returns `Option`).

/// Compose a unary mapper `f` and a binary short-circuiting folder `g` into a
/// single try-fold step that applies `f` to the element and then folds the
/// result with `g`, propagating `None`/`Some(_)`.
pub fn map_try_fold<'a>(
    f: &'a mut impl FnMut(u64) -> u64,
    mut g: impl FnMut(u64, u64) -> Option<u64> + 'a,
) -> impl FnMut(u64, u64) -> Option<u64> + 'a {
    move |acc, elt| g(acc, f(elt))
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from `tests/iter/adapters/map.rs::test_map_try_folds`:
    //
    //   let f = &|acc, x| i32::checked_add(2 * acc, x);
    //   assert_eq!((0..10).map(|x| x + 3).try_fold(7, f), (3..13).try_fold(7, f));
    //
    // We rewrite to use `map_try_fold` directly. Switching the carrier to
    // `Option<u64>` keeps the structural assertion (a mapped try_fold equals
    // the equivalent unmapped try_fold over the shifted range).

    #[test]
    fn map_try_fold_matches_unmapped_try_fold() {
        let mut mapper = |x: u64| x + 3;
        let g = |acc: u64, x: u64| u64::checked_add(2 * acc, x);

        let mapped: Option<u64> = (0..10u64).try_fold(7u64, map_try_fold(&mut mapper, g));
        let unmapped: Option<u64> = (3..13u64).try_fold(7u64, g);
        assert_eq!(mapped, unmapped);
    }

    #[test]
    fn map_try_rfold_matches_unmapped_try_rfold() {
        let mut mapper = |x: u64| x + 3;
        let g = |acc: u64, x: u64| u64::checked_add(2 * acc, x);

        let mapped: Option<u64> = (0..10u64).try_rfold(7u64, map_try_fold(&mut mapper, g));
        let unmapped: Option<u64> = (3..13u64).try_rfold(7u64, g);
        assert_eq!(mapped, unmapped);
    }

    #[test]
    fn map_try_fold_short_circuits_on_none() {
        // Translation of the second block of `test_map_try_folds`:
        //   let mut iter = (0..40).map(|x| x + 10);
        //   assert_eq!(iter.try_fold(0, i8::checked_add), None);
        //
        // We use u8 widened to u64 with a manual ceiling at u8::MAX.
        let mut iter = 0..40u64;
        let mut mapper = |x: u64| x + 10;
        let g = |acc: u64, x: u64| {
            let s = acc + x;
            if s > u8::MAX as u64 { None } else { Some(s) }
        };
        assert_eq!(iter.try_fold(0u64, map_try_fold(&mut mapper, g)), None);
    }

    // ---------------------------------------------------------------------
    // Property-based tests for the contract of `map_try_fold`.
    //
    // The full contract of `map_try_fold(f, g)` is the single equation
    //
    //     map_try_fold(f, g)(acc, elt) == g(acc, f(elt))
    //
    // for every `acc`, `elt`, `f`, `g` on which `f` and `g` do not panic.
    // The tests below pin this equation down pointwise on a grid, with
    // asymmetric `f` and `g` chosen so that the standard families of bugs
    // (argument swap, applying `f` to `acc` instead of `elt`, applying `f`
    // twice, dropping `f`, calling `g` twice, etc.) all change the value.
    // ---------------------------------------------------------------------

    /// Postcondition (value clause): `map_try_fold(f, g)(acc, elt)` equals
    /// the explicit composition `g(acc, f(elt))` for every `(acc, elt)`
    /// in the grid.
    ///
    /// `f(x) = x + 5` and `g(a, b) = checked_add(2*a, b)` are both
    /// asymmetric in their arguments, so a buggy implementation that
    /// returns any other plausible composition (e.g. `g(f(acc), elt)`,
    /// `g(acc, elt)`, `g(acc, f(f(elt)))`) would produce a different
    /// value on at least one grid point.
    #[test]
    fn prop_closure_value_equals_g_of_acc_and_f_of_elt() {
        let mut f = |x: u64| x + 5;
        let g = |a: u64, b: u64| u64::checked_add(2 * a, b);
        let mut closure = map_try_fold(&mut f, g);

        for acc in 0u64..50 {
            for elt in 0u64..50 {
                let expected = u64::checked_add(2 * acc, elt + 5);
                assert_eq!(closure(acc, elt), expected, "acc={acc}, elt={elt}");
            }
        }
    }

    /// Failure clause: when `g(acc, f(elt))` is `None`, the closure is
    /// `None`; when it is `Some(v)`, the closure is `Some(v)`.
    ///
    /// This is a sub-case of the value equation above, but is called out
    /// separately so the short-circuiting behavior is captured as its own
    /// obligation. The grid is sized so that `g` returns both `Some` and
    /// `None` over the inputs explored, exercising both branches.
    #[test]
    fn prop_short_circuits_iff_g_returns_none() {
        let mut f = |x: u64| x + 7;
        let g = |a: u64, b: u64| {
            let s = a * 3 + b;
            if s >= 50 { None } else { Some(s) }
        };
        let mut closure = map_try_fold(&mut f, g);

        for acc in 0u64..20 {
            for elt in 0u64..20 {
                let fe = elt + 7;
                let s = acc * 3 + fe;
                let expected = if s >= 50 { None } else { Some(s) };
                assert_eq!(closure(acc, elt), expected, "acc={acc}, elt={elt}");
            }
        }
    }
}
