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
}
