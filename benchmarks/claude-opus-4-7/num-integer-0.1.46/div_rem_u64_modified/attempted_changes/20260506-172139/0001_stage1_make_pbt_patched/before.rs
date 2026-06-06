//! Extracted from `num-integer` 0.1.46:
//!
//! ```text
//! pub fn div_rem<T: Integer>(x: T, y: T) -> (T, T) {
//!     x.div_rem(&y)
//! }
//! ```
//!
//! and the `Integer::div_rem` impl produced by the `impl_integer_for_usize!`
//! macro for the unsigned primitives:
//!
//! ```text
//! fn div_rem(&self, other: &Self) -> (Self, Self) {
//!     (*self / *other, *self % *other)
//! }
//! ```
//!
//! Monomorphized to `u64`: the trait dispatch collapses to plain `/` and `%`
//! on `u64`, so the extracted function is just the pair of those primitive
//! operators.

#![no_std]

/// Simultaneous truncated integer division and remainder for `u64`.
///
/// Returns `(quotient, remainder)` where `quotient = x / y` and
/// `remainder = x % y`. Panics on `y == 0`, matching the behavior of the
/// underlying `u64` operators (and of the original `num_integer::div_rem`).
#[inline]
pub fn div_rem(x: u64, y: u64) -> (u64, u64) {
    (x / y, x % y)
}

#[cfg(test)]
mod tests {
    use super::div_rem;

    // ------------------------------------------------------------------
    // Tests adapted from the doc-comment on `Integer::div_rem` in
    // num-integer 0.1.46 (src/lib.rs lines 248-258). The original doc-test
    // exercises signed types; only the non-negative cases survive after
    // monomorphization to `u64`.
    // ------------------------------------------------------------------
    #[test]
    fn doc_test_examples() {
        assert_eq!(div_rem(8, 3), (2, 2));
        assert_eq!(div_rem(1, 2), (0, 1));
        assert_eq!(div_rem(0, 1), (0, 0));
    }

    // ------------------------------------------------------------------
    // Adapted from `test_div_rem` in the `impl_integer_for_isize!` macro
    // (src/lib.rs lines 632-654). The unsigned macro does not include a
    // `test_div_rem`, so we transfer the signed test's *structure* (the
    // division rule `d * q + r == n`, plus equivalence with `(n/d, n%d)`)
    // and instantiate it for `u64`.
    // ------------------------------------------------------------------
    fn test_division_rule((n, d): (u64, u64), (q, r): (u64, u64)) {
        assert_eq!(d * q + r, n);
    }

    #[test]
    fn test_div_rem() {
        fn test_nd_dr(nd: (u64, u64), qr: (u64, u64)) {
            let (n, d) = nd;
            let separate_div_rem = (n / d, n % d);
            let combined_div_rem = div_rem(n, d);

            test_division_rule(nd, qr);

            assert_eq!(separate_div_rem, qr);
            assert_eq!(combined_div_rem, qr);
        }

        test_nd_dr((8, 3), (2, 2));
        test_nd_dr((1, 2), (0, 1));
        test_nd_dr((10, 3), (3, 1));
        test_nd_dr((5, 5), (1, 0));
        test_nd_dr((3, 7), (0, 3));
        test_nd_dr((0, 1), (0, 0));
    }

    // ------------------------------------------------------------------
    // Contract-style postcondition test: for any divisor `d != 0`,
    // `div_rem(n, d) == (q, r)` must satisfy
    //     n == d * q + r   AND   0 <= r < d.
    // This is the defining contract of truncated division on unsigned
    // integers and is the strongest equivalence the transferred tests can
    // give us without a formal proof.
    // ------------------------------------------------------------------
    #[test]
    fn postcondition_division_rule() {
        for n in 0u64..=200 {
            for d in 1u64..=50 {
                let (q, r) = div_rem(n, d);
                assert_eq!(d * q + r, n, "division rule failed at ({n}, {d})");
                assert!(r < d, "remainder out of range at ({n}, {d}): r = {r}");
            }
        }
    }

    // ------------------------------------------------------------------
    // Cross-check against the original `num_integer::div_rem` on a sweep
    // of inputs. This is the strongest behavioral-equivalence check
    // available without a formal proof.
    // ------------------------------------------------------------------
    #[test]
    fn agrees_with_source() {
        for a in 0u64..=64 {
            for b in 1u64..=64 {
                assert_eq!(
                    div_rem(a, b),
                    num_integer::div_rem(a, b),
                    "extracted disagrees with source at ({a}, {b})"
                );
            }
        }

        // A handful of larger inputs, including ones near `u64::MAX`.
        let cases: &[(u64, u64)] = &[
            (u64::MAX, 1),
            (u64::MAX, 2),
            (u64::MAX, 3),
            (u64::MAX, u64::MAX),
            (u64::MAX - 1, u64::MAX),
            (1_000_000_007, 999_983),
            (1u64 << 63, 7),
            (0, u64::MAX),
        ];
        for &(a, b) in cases {
            assert_eq!(
                div_rem(a, b),
                num_integer::div_rem(a, b),
                "extracted disagrees with source at ({a}, {b})"
            );
        }
    }
}
