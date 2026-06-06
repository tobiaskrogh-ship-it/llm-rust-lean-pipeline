// Monomorphic u64 version of `Integer::is_multiple_of` from
// num-integer 0.1.46 (the unsigned-impl branch, src/lib.rs:929-934).
// Returns whether `a` is an integer multiple of `b`. Special-cases
// `b == 0`: only `0` is a multiple of `0`.
pub fn is_multiple_of(a: u64, b: u64) -> bool {
    if b == 0 {
        a == 0
    } else {
        a % b == 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn known_values() {
        assert!(is_multiple_of(12, 3));
        assert!(is_multiple_of(12, 4));
        assert!(!is_multiple_of(12, 5));
        assert!(is_multiple_of(0, 7));
        assert!(is_multiple_of(7, 1));
    }

    /// Boundary: only `0` is a multiple of `0` (the convention `b == 0`
    /// special case in the source).
    #[test]
    fn zero_divisor_only_zero() {
        assert!(is_multiple_of(0, 0));
        assert!(!is_multiple_of(1, 0));
        assert!(!is_multiple_of(7, 0));
        assert!(!is_multiple_of(u64::MAX, 0));
    }

    /// Postcondition (b > 0): `is_multiple_of(a, b)` iff there exists
    /// `k : u64` with `a = k * b`.
    #[test]
    fn agrees_with_division() {
        for a in 0u64..=50 {
            for b in 1u64..=20 {
                assert_eq!(is_multiple_of(a, b), a % b == 0,
                    "is_multiple_of({a}, {b})");
            }
        }
    }

    /// Postcondition C3 (constructive direction, `b > 0`): if `a = k * b`
    /// for some `k : u64`, then `is_multiple_of(a, b)` is `true`.
    /// Tests by *constructing* `a` from a witness `k`, rather than by
    /// recomputing `a % b` (which would tautologically match the
    /// implementation).
    #[test]
    fn multiples_have_witnesses() {
        for b in 1u64..=100 {
            for k in 0u64..=100 {
                let a = k * b; // safe: 100 * 100 = 10_000, no overflow
                assert!(is_multiple_of(a, b),
                    "is_multiple_of({a}, {b}) should be true (witness k={k})");
            }
        }
    }

    /// Postcondition C4 (non-divisible direction, `b > 1`): if
    /// `a = q * b + r` with `0 < r < b`, then `is_multiple_of(a, b)`
    /// is `false`. Constructs explicit non-multiples to rule out a
    /// buggy implementation that always returns `true`.
    #[test]
    fn non_multiples_have_no_witness() {
        for b in 2u64..=50 {
            for q in 0u64..=50 {
                for r in 1u64..b {
                    let a = q * b + r; // safe: 50*50 + 49 < 2600
                    assert!(!is_multiple_of(a, b),
                        "is_multiple_of({a}, {b}) should be false (a = {q}*{b} + {r})");
                }
            }
        }
    }

    /// Postcondition at the upper end of `u64`: large multiples and
    /// near-multiples behave correctly. Guards against bugs that
    /// surface only for values outside the small ranges above.
    #[test]
    fn large_values() {
        // u64::MAX = 2^64 - 1 = 3 * 5 * 17 * 257 * 641 * 65537 * 6700417
        assert!(is_multiple_of(u64::MAX, 1));
        assert!(is_multiple_of(u64::MAX, u64::MAX));
        assert!(is_multiple_of(u64::MAX, 3));
        assert!(is_multiple_of(u64::MAX, 65537));
        assert!(!is_multiple_of(u64::MAX, 2));
        assert!(!is_multiple_of(u64::MAX - 1, 3));
        // Constructed witness near the top: largest multiple of 7 ≤ u64::MAX.
        let big = (u64::MAX / 7) * 7;
        assert!(is_multiple_of(big, 7));
        assert!(!is_multiple_of(big + 1, 7));
    }
}
