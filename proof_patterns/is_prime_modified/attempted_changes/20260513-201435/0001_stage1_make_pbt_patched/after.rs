/// Return true iff n is prime. (Return type corrected from CLEVER's
/// auto-defaulted `u64` to `bool` to match the docstring.)
fn has_divisor_at(n: u64, d: u64) -> bool {
    if d * d > n {
        false
    } else if n % d == 0 {
        true
    } else {
        has_divisor_at(n, d + 1)
    }
}

pub fn is_prime(n: u64) -> bool {
    if n < 2 {
        false
    } else {
        !has_divisor_at(n, 2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Trial-division oracle used as the reference for `is_prime`.
    /// Encodes the mathematical definition of primality directly.
    fn naive_is_prime(n: u64) -> bool {
        if n < 2 {
            return false;
        }
        let mut d: u64 = 2;
        while d.saturating_mul(d) <= n {
            if n % d == 0 {
                return false;
            }
            d += 1;
        }
        true
    }

    proptest! {
        /// Boundary clause of the contract: values below 2 are never prime.
        #[test]
        fn below_two_is_not_prime(n in 0u64..2) {
            prop_assert!(!is_prime(n));
        }

        /// Full iff contract on a bounded range: `is_prime` agrees with the
        /// trial-division definition of primality. Catches errors in either
        /// direction (false positives and false negatives) for n in 0..10_000.
        #[test]
        fn matches_naive_definition(n in 0u64..10_000) {
            prop_assert_eq!(is_prime(n), naive_is_prime(n));
        }

        /// Soundness direction extended beyond the oracle range: any product
        /// of two factors >= 2 is composite by construction, hence not prime.
        #[test]
        fn products_of_factors_are_not_prime(a in 2u64..1_000, b in 2u64..1_000) {
            prop_assert!(!is_prime(a * b));
        }
    }
}
