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

    // ------------------------------------------------------------------
    // Failure-condition tests. The doc-comment specifies "Panics on
    // `y == 0`" — this is the precondition of the contract. The panic
    // must happen for *any* `x`, so we cover both a nonzero and zero
    // dividend (the precondition is on `y` alone).
    //
    // Each `#[should_panic]` test can witness exactly one panic, so the
    // two cases live in separate functions.
    // ------------------------------------------------------------------
    #[test]
    #[should_panic]
    fn panics_on_zero_divisor_nonzero_dividend() {
        let _ = div_rem(42, 0);
    }

    #[test]
    #[should_panic]
    fn panics_on_zero_divisor_zero_dividend() {
        // `0 / 0` must also panic: the precondition rules out `y == 0`
        // independently of `x`.
        let _ = div_rem(0, 0);
    }

    // ------------------------------------------------------------------
    // Property-based postcondition sweep using a deterministic LCG.
    // `postcondition_division_rule` only reaches `n <= 200, d <= 50`,
    // and `agrees_with_source` only sweeps `a, b <= 64` plus a handful
    // of hand-picked large cases. This extends the postcondition check
    // (`n == d*q + r` and `r < d`) to a randomly-sampled sweep of
    // full-width `u64` inputs, so high-bit dividends, high-bit
    // divisors, and arbitrary bit patterns in between are all
    // exercised. The seed and LCG constants are fixed, so the test is
    // deterministic and reproducible.
    // ------------------------------------------------------------------
    #[test]
    fn postcondition_division_rule_random() {
        // Knuth MMIX LCG constants.
        let mut state: u64 = 0x0123_4567_89ab_cdef;
        let mut next = || {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            state
        };

        for _ in 0..2_000 {
            let n = next();
            let d = next();
            if d == 0 {
                // Precondition: divisor must be nonzero. (In practice
                // an LCG essentially never lands on 0, but we guard
                // explicitly so the test is correct by construction.)
                continue;
            }
            let (q, r) = div_rem(n, d);
            // Correct truncated division gives `q == n/d`, so
            // `q * d <= n` and `q * d + r == n` cannot overflow.
            // A buggy implementation returning a too-large `q` would
            // either overflow (caught in debug) or fail the equality
            // (caught in release).
            assert_eq!(q * d + r, n, "division rule failed at ({n}, {d})");
            assert!(r < d, "remainder out of range at ({n}, {d}): r = {r}");
        }
    }
}
