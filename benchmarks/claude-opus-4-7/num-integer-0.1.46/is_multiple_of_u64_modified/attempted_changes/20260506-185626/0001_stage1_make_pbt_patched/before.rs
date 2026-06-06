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
}
