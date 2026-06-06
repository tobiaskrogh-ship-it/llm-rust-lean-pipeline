//! `trailing_zeros_u64` — a minimal single-`while`-loop reference example.
//!
//! Counts the number of trailing (low-order) zero bits of a `u64`, with the
//! convention `trailing_zeros_u64(0) == 64`. It is a shift-and-count loop:
//! shift the value right one bit at a time while the low bit is zero,
//! counting the shifts. The loop terminates because the working value `y`
//! strictly decreases — in fact halves — every iteration and stays non-zero.
//!
//! This crate exists as a proof-pattern reference: a single `while` loop
//! walked by a bit-level measure (`y` as a Nat), which is the helper shape
//! Stein's binary GCD depends on.

/// Number of trailing zero bits of `x`; `trailing_zeros_u64(0) == 64`.
///
/// For `x != 0` the result `r` satisfies: `r < 64`, `2^r` divides `x`,
/// and bit `r` of `x` is set (so `r` is the position of the lowest set
/// bit and `x` is not divisible by `2^(r + 1)`).
pub fn trailing_zeros_u64(x: u64) -> u32 {
    if x == 0 {
        return 64;
    }
    let mut y = x;
    let mut count: u32 = 0;
    while y & 1 == 0 {
        y >>= 1;
        count = count + 1;
    }
    count
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Hand-computed values, including the `x == 0` convention.
    #[test]
    fn known_values() {
        assert_eq!(trailing_zeros_u64(0), 64);
        assert_eq!(trailing_zeros_u64(1), 0);
        assert_eq!(trailing_zeros_u64(2), 1);
        assert_eq!(trailing_zeros_u64(3), 0);
        assert_eq!(trailing_zeros_u64(4), 2);
        assert_eq!(trailing_zeros_u64(8), 3);
        assert_eq!(trailing_zeros_u64(12), 2);
        assert_eq!(trailing_zeros_u64(1u64 << 63), 63);
    }

    /// Postcondition (range): for a non-zero input the result is below 64.
    #[test]
    fn result_below_64_when_nonzero() {
        for x in 1u64..=300 {
            assert!(trailing_zeros_u64(x) < 64);
        }
    }

    /// Postcondition (divisibility): `2^result` divides `x`.
    #[test]
    fn power_of_two_divides() {
        for x in 1u64..=300 {
            let r = trailing_zeros_u64(x);
            assert_eq!(x % (1u64 << r), 0);
        }
    }

    /// Postcondition (exactness): bit `result` of `x` is set, so `x` is
    /// not divisible by `2^(result + 1)`.
    #[test]
    fn lowest_set_bit_is_at_result() {
        for x in 1u64..=300 {
            let r = trailing_zeros_u64(x);
            assert_eq!((x >> r) & 1, 1);
        }
    }
}
