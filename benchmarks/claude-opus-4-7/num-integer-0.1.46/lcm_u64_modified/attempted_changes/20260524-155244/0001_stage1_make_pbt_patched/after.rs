//! Extracted from `num-integer` 0.1.46, function `num_integer::lcm`,
//! monomorphized to `u64`.
//!
//! The original `pub fn lcm<T: Integer>(x: T, y: T) -> T` simply forwards to
//! `x.lcm(&y)`, whose `u64` implementation calls `self.gcd_lcm(other).1`. The
//! `gcd_lcm` implementation in turn calls `self.gcd(other)` (Stein's
//! algorithm). Everything is inlined here so the crate is self-contained.

#![no_std]

/// Calculates the Lowest Common Multiple (LCM) of `x` and `y`.
#[inline]
pub fn lcm(x: u64, y: u64) -> u64 {
    // Original: `x.lcm(&y)` -> `self.gcd_lcm(other).1`
    if x == 0 && y == 0 {
        return 0;
    }
    let gcd = gcd_u64(x, y);
    x * (y / gcd)
}

/// Greatest Common Divisor of two `u64`s using Stein's (binary) algorithm.
/// Inlined from the `Integer` impl for `u64` in `num-integer` 0.1.46.
#[inline]
fn gcd_u64(a: u64, b: u64) -> u64 {
    let mut m = a;
    let mut n = b;
    if m == 0 || n == 0 {
        return m | n;
    }

    // find common factors of 2
    let shift = (m | n).trailing_zeros();

    // divide n and m by 2 until odd
    m >>= m.trailing_zeros();
    n >>= n.trailing_zeros();

    while m != n {
        if m > n {
            m -= n;
            m >>= m.trailing_zeros();
        } else {
            n -= m;
            n >>= n.trailing_zeros();
        }
    }
    m << shift
}

#[cfg(test)]
mod tests {
    use super::lcm;

    // Transferred from the source crate's `impl_integer_for_usize!` test
    // module (`test_lcm`) — monomorphized to u64 and rewritten to call the
    // free function `lcm` instead of the `Integer::lcm` method.
    #[test]
    fn test_lcm() {
        assert_eq!(lcm(1u64, 0), 0u64);
        assert_eq!(lcm(0u64, 1), 0u64);
        assert_eq!(lcm(1u64, 1), 1u64);
        assert_eq!(lcm(8u64, 9), 72u64);
        assert_eq!(lcm(11u64, 5), 55u64);
        assert_eq!(lcm(15u64, 17), 255u64);
    }

    // Transferred from the top-level `test_lcm_overflow` test in the source
    // crate — only the `u64` case is kept since this crate is monomorphized
    // to `u64`. The `checked_mul` overflow sanity check is preserved.
    #[test]
    fn test_lcm_overflow() {
        let x: u64 = 0x8000_0000_0000_0000;
        let y: u64 = 0x02;
        let r: u64 = 0x8000_0000_0000_0000;
        let o = x.checked_mul(y);
        assert!(
            o.is_none(),
            "sanity checking that u64 input {} * {} overflows",
            x,
            y
        );
        assert_eq!(lcm(x, y), r);
        assert_eq!(lcm(y, x), r);
    }

    // Doc-test from `Integer::lcm` (monomorphized to u64; the `0.lcm(&0)`
    // case is included in `test_lcm` already as part of the trait
    // contract — added here verbatim from the doc-comment).
    #[test]
    fn test_lcm_doc() {
        assert_eq!(lcm(7u64, 3), 21);
        assert_eq!(lcm(2u64, 4), 4);
        assert_eq!(lcm(0u64, 0), 0);
    }

    // -------- Property-based contract tests --------
    //
    // The bounded ranges below stay well below `u64::MAX.sqrt()`, so the
    // expression `x * (y / gcd(x, y))` cannot wrap inside the loops. That
    // lets the tests express the no-overflow contract directly.

    /// Contract clause: `lcm(0, y) == 0` and `lcm(x, 0) == 0` for every
    /// input. This is the "zero is absorbing" precondition/postcondition
    /// — the function short-circuits when either argument is zero, and
    /// the result must literally be zero (not just any multiple of zero).
    #[test]
    fn prop_zero_is_absorbing() {
        for v in 0u64..200 {
            assert_eq!(lcm(0, v), 0, "lcm(0, {}) should be 0", v);
            assert_eq!(lcm(v, 0), 0, "lcm({}, 0) should be 0", v);
        }
        // A few large values too, to make sure we don't merely exercise
        // the small-input path.
        for v in [1u64, 7, 1 << 20, 1 << 40, u64::MAX].iter().copied() {
            assert_eq!(lcm(0, v), 0);
            assert_eq!(lcm(v, 0), 0);
        }
    }

    /// Contract clause (postcondition): when `x > 0` and `y > 0`, the
    /// result is a multiple of `x`. This is one half of "common multiple".
    #[test]
    fn prop_result_is_multiple_of_x() {
        for x in 1u64..40 {
            for y in 1u64..40 {
                let l = lcm(x, y);
                assert!(
                    l % x == 0,
                    "lcm({}, {}) = {} is not a multiple of x",
                    x, y, l
                );
            }
        }
    }

    /// Contract clause (postcondition): when `x > 0` and `y > 0`, the
    /// result is a multiple of `y`. This is the other half of "common
    /// multiple", independent of being a multiple of `x` because the
    /// implementation is asymmetric (`x * (y / gcd)`).
    #[test]
    fn prop_result_is_multiple_of_y() {
        for x in 1u64..40 {
            for y in 1u64..40 {
                let l = lcm(x, y);
                assert!(
                    l % y == 0,
                    "lcm({}, {}) = {} is not a multiple of y",
                    x, y, l
                );
            }
        }
    }

    /// Contract clause (postcondition): the result is the *least* positive
    /// common multiple — i.e., no positive integer strictly less than
    /// `lcm(x, y)` is divisible by both `x` and `y`. This is the
    /// "L" (least) in LCM and is independent of "common multiple": a
    /// buggy implementation could return `x * y` (always a common
    /// multiple) and still satisfy the divisibility tests above; this
    /// test rules that out.
    #[test]
    fn prop_result_is_least_common_multiple() {
        for x in 1u64..25 {
            for y in 1u64..25 {
                let l = lcm(x, y);
                // Search every positive integer strictly below `l` and
                // confirm none of them is a common multiple.
                for z in 1..l {
                    assert!(
                        !(z % x == 0 && z % y == 0),
                        "lcm({}, {}) = {} but {} is a smaller common multiple",
                        x, y, l, z
                    );
                }
            }
        }
    }

}
