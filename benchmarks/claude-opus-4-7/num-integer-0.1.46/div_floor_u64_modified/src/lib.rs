//! Extracted `div_floor` from the `num-integer` crate (v0.1.46),
//! monomorphized to the concrete type `u64`.
//!
//! Source:
//!   - Free function `num_integer::div_floor`
//!     (src/lib.rs:398), which delegates to `Integer::div_floor`.
//!   - For unsigned integers, `Integer::div_floor` is defined in the
//!     `impl_integer_for_usize!` macro (src/lib.rs:853) as `*self / *other`.
//!
//! For `u64`, floored division coincides with truncated division because
//! both operands are non-negative, so the extracted body is simply `x / y`.

/// Floored integer division for `u64`.
///
/// Equivalent to the original generic `num_integer::div_floor::<u64>(x, y)`.
#[inline]
pub fn div_floor(x: u64, y: u64) -> u64 {
    x / y
}

#[cfg(test)]
mod tests {
    use super::div_floor;

    // Transferred from num-integer-0.1.46 src/lib.rs:960
    // (`test_div_mod_floor` inside the `impl_integer_for_usize!` macro).
    // Only the `div_floor` assertions are kept; the `mod_floor` /
    // `div_mod_floor` ones are dropped because those functions are not
    // part of this extraction.
    #[test]
    fn test_div_floor() {
        assert_eq!(div_floor(10u64, 3u64), 3u64);
        assert_eq!(div_floor(5u64, 5u64), 1u64);
        assert_eq!(div_floor(3u64, 7u64), 0u64);
        assert_eq!(div_floor(3u64, 7u64), 0u64);
    }

    // Contract-style postcondition: for any non-zero divisor `d`,
    //   q = div_floor(n, d)   ==>   q * d <= n  &&  n - q * d < d
    // This is the defining property of floored division on non-negative
    // integers (and for u64, floored == truncated == Euclidean division).
    #[test]
    fn postcondition_floor_division() {
        for n in 0u64..=100 {
            for d in 1u64..=20 {
                let q = div_floor(n, d);
                assert!(q * d <= n, "q*d <= n failed for n={n} d={d} q={q}");
                assert!(n - q * d < d, "n - q*d < d failed for n={n} d={d} q={q}");
            }
        }
    }

    // Failure condition: `div_floor` has an implicit precondition that
    // the divisor is non-zero. When called with `y == 0`, the underlying
    // `x / y` traps and panics. This captures that contract clause —
    // a buggy implementation that silently returned, say, 0 or u64::MAX
    // for `y == 0` would be caught here.
    #[test]
    #[should_panic]
    fn panics_on_zero_divisor() {
        // numerator is non-zero so the panic isn't "0/0" specific —
        // it's the divisor being zero that drives the failure.
        let _ = div_floor(7, 0);
    }

    // Cross-check against the original `num-integer` implementation
    // on a sweep of inputs. This is the strongest available
    // behavioral-equivalence check without a formal proof.
    #[test]
    fn agrees_with_source() {
        for x in 0u64..=50 {
            for y in 1u64..=50 {
                assert_eq!(
                    div_floor(x, y),
                    num_integer::div_floor(x, y),
                    "extracted disagrees with source at ({x}, {y})"
                );
            }
        }

        // A handful of larger values too.
        let xs: [u64; 5] = [0, 1, u64::MAX, u64::MAX - 1, 1_000_000_007];
        let ys: [u64; 5] = [1, 2, 3, 1_000_000_007, u64::MAX];
        for &x in &xs {
            for &y in &ys {
                assert_eq!(
                    div_floor(x, y),
                    num_integer::div_floor(x, y),
                    "extracted disagrees with source at ({x}, {y})"
                );
            }
        }
    }
}
