//! Extracted from `num-integer` 0.1.46, function `num_integer::lcm`,
//! monomorphized to `u64`.
//!
//! The original `pub fn lcm<T: Integer>(x: T, y: T) -> T` simply forwards to
//! `x.lcm(&y)`, whose `u64` implementation calls `self.gcd_lcm(other).1`. The
//! `gcd_lcm` implementation in turn calls `self.gcd(other)` (Stein's
//! algorithm). Everything is inlined here so the crate is self-contained.

#![no_std]

/// Hand-rolled `u64::trailing_zeros` so the extracted Lean does not refer to
/// `core_models.num.Impl_9.trailing_zeros`, which is not provided by the Hax
/// numeric model. Matches the standard-library semantics: returns `64` when
/// `x == 0`, otherwise the number of trailing zero bits of `x`.
#[inline]
fn trailing_zeros_u64(x: u64) -> u32 {
    if x == 0 {
        return 64;
    }
    let mut v = x;
    let mut count: u32 = 0;
    while v & 1 == 0 {
        // `v` is non-zero and even at the loop head, so `v >> 1` is strictly
        // smaller and still non-negative — a valid termination measure.
        hax_lib::loop_decreases!(v);
        v >>= 1;
        count += 1;
    }
    count
}

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
    let shift = trailing_zeros_u64(m | n);

    // divide n and m by 2 until odd
    m >>= trailing_zeros_u64(m);
    n >>= trailing_zeros_u64(n);

    while m != n {
        // Stein's loop: at the head of each iteration `m` and `n` are both
        // odd and positive (the pre-loop shifts strip trailing zeros, and
        // the body re-establishes oddness). Each iteration replaces the
        // larger of the two — call it `M` — by `(M - other) >> tz(M -
        // other)`, which is `< M / 2` (the difference is even, so `tz >=
        // 1`). The new top set bit of `M` therefore drops by at least one
        // position; the unchanged value's top bit was already below `M`'s
        // (since it was the smaller), so the top set bit of `m | n`
        // strictly decreases — i.e. `m | n` itself strictly decreases as
        // an integer. We use `m | n` rather than `m + n` because addition
        // can overflow on inputs like `lcm(u64::MAX, 1)`, which would
        // force the proof to discharge `addOverflow = false`. We use
        // `m | n` rather than `if m > n { m } else { n }` because Hax's
        // `mvcgen` cannot currently handle if-then-else inside the
        // termination measure ("hax_construct_pure: mvcgen generated more
        // than one goal..."). The macro body is gated by
        // `#[cfg(hax_compilation)]`, so this expression is never evaluated
        // at runtime.
        hax_lib::loop_decreases!(m | n);
        if m > n {
            m -= n;
            m >>= trailing_zeros_u64(m);
        } else {
            n -= m;
            n >>= trailing_zeros_u64(n);
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

    /// Contract clause (postcondition): `lcm` is symmetric in its
    /// arguments. This is a non-trivial claim because the implementation
    /// is asymmetric — it computes `x * (y / gcd(x, y))`, treating the
    /// two arguments differently. A reordering bug (e.g. forgetting the
    /// `y / gcd` rearrangement that prevents overflow) could break
    /// symmetry on inputs near `u64::MAX`, so we exercise the overflow
    /// edge in addition to small inputs.
    #[test]
    fn prop_commutative() {
        for x in 0u64..40 {
            for y in 0u64..40 {
                assert_eq!(
                    lcm(x, y),
                    lcm(y, x),
                    "lcm is not commutative on ({}, {})",
                    x, y
                );
            }
        }
        // Edge values chosen so the no-overflow precondition is
        // satisfied — including the overflow-adjacent pair from
        // `test_lcm_overflow`, where the `x * (y / gcd)` rearrangement
        // saves us, and a couple of other large combinations whose lcm
        // still fits in u64.
        let big = [
            (1u64, u64::MAX),
            (2, 0x8000_0000_0000_0000),
            (0x8000_0000_0000_0000, 0x8000_0000_0000_0000),
            (3, 5),
            (1u64 << 40, 1u64 << 20),
        ];
        for (x, y) in big.iter().copied() {
            assert_eq!(lcm(x, y), lcm(y, x), "asymmetric on ({}, {})", x, y);
        }
    }
}
