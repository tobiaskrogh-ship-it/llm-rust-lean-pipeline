//! Concrete `u64` extraction of `num_integer::div_mod_floor`.
//!
//! Source: `num-integer` v0.1.46, `src/lib.rs`.
//!
//! The free function in the source crate is:
//!
//! ```ignore
//! pub fn div_mod_floor<T: Integer>(x: T, y: T) -> (T, T) {
//!     x.div_mod_floor(&y)
//! }
//! ```
//!
//! The `Integer` trait provides a default implementation
//!
//! ```ignore
//! fn div_mod_floor(&self, other: &Self) -> (Self, Self) {
//!     (self.div_floor(other), self.mod_floor(other))
//! }
//! ```
//!
//! For unsigned integer types, the impl provided by the
//! `impl_integer_for_usize!` macro overrides only `div_floor`/`mod_floor`,
//! leaving the default `div_mod_floor`. The unsigned definitions are:
//!
//! ```ignore
//! fn div_floor(&self, other: &Self) -> Self { *self / *other }
//! fn mod_floor(&self, other: &Self) -> Self { *self % *other }
//! ```
//!
//! So for `T = u64`, `div_mod_floor(x, y)` is `(x / y, x % y)`.
//! Both operations panic on `y == 0` (matching the source's behavior).

/// Simultaneous floored integer division and modulus, monomorphized to `u64`.
///
/// Equivalent to `num_integer::div_mod_floor::<u64>(x, y)`.
#[inline]
pub fn my_div_mod_floor(x: u64, y: u64) -> (u64, u64) {
    (x / y, x % y)
}

#[cfg(test)]
mod tests {
    use super::my_div_mod_floor;

    // Transferred from the `test_div_mod_floor` test produced by the
    // `impl_integer_for_usize!` macro in num-integer/src/lib.rs (line 961).
    // The original test exercised `div_floor`, `mod_floor`, and
    // `div_mod_floor` together; here we keep the `div_mod_floor` checks
    // (which transitively cover the floor/mod values).
    #[test]
    fn test_div_mod_floor() {
        assert_eq!(my_div_mod_floor(10, 3), (3u64, 1u64));
        assert_eq!(my_div_mod_floor(5, 5), (1u64, 0u64));
        assert_eq!(my_div_mod_floor(3, 7), (0u64, 3u64));
    }

    // Contract-style postcondition: for any non-zero `y`, the returned
    // `(q, r)` must satisfy `q * y + r == x` and `0 <= r < y`.
    #[test]
    fn postcondition_div_mod_floor() {
        for x in 0u64..=100 {
            for y in 1u64..=50 {
                let (q, r) = my_div_mod_floor(x, y);
                assert!(r < y, "remainder out of range at ({x}, {y}): r={r}");
                assert_eq!(q * y + r, x, "q*y + r != x at ({x}, {y})");
            }
        }
    }

    // Cross-check against the original `num-integer` crate on a sweep
    // of small inputs.
    #[test]
    fn agrees_with_source() {
        for x in 0u64..=80 {
            for y in 1u64..=80 {
                assert_eq!(
                    my_div_mod_floor(x, y),
                    num_integer::div_mod_floor(x, y),
                    "extracted disagrees with source at ({x}, {y})"
                );
            }
        }
    }

    // Spot-check large values near `u64::MAX`.
    #[test]
    fn agrees_with_source_large() {
        let cases: &[(u64, u64)] = &[
            (u64::MAX, 1),
            (u64::MAX, 2),
            (u64::MAX, u64::MAX),
            (u64::MAX - 1, 7),
            (1, u64::MAX),
            (0, u64::MAX),
            (1u64 << 63, 3),
        ];
        for &(x, y) in cases {
            assert_eq!(
                my_div_mod_floor(x, y),
                num_integer::div_mod_floor(x, y),
                "disagree at ({x}, {y})"
            );
        }
    }
}
