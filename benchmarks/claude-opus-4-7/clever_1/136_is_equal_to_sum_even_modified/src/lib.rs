/// HumanEval/138 / CLEVER 136 — `is_equal_to_sum_even(n)`.  True iff
/// `n` can be written as the sum of exactly four positive even
/// integers.  Closed form: n is even AND n >= 8.  Override to `u64`
/// since the answer is always false for negative or small n.
pub fn is_equal_to_sum_even(n: u64) -> bool {
    n >= 8 && n % 2 == 0
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn known() {
        assert!(!is_equal_to_sum_even(4));
        assert!(is_equal_to_sum_even(8));   // 2+2+2+2
        assert!(!is_equal_to_sum_even(9));
        assert!(is_equal_to_sum_even(10));  // 2+2+2+4
        assert!(!is_equal_to_sum_even(7));
    }

    proptest! {
        /// Postcondition (semantic soundness + completeness on the valid
        /// domain): for every even n >= 8 the function returns true, and
        /// the value `n` really is the sum of four positive even
        /// integers, witnessed by `2 + 2 + 2 + (n - 6)`.
        #[test]
        fn accepts_even_at_least_8_with_witness(k in 4u64..100_000) {
            // k >= 4 ensures n = 2*k >= 8 and is even.
            let n = 2 * k;
            prop_assert!(is_equal_to_sum_even(n));

            // Exhibit a concrete decomposition.
            let (a, b, c, d): (u64, u64, u64, u64) = (2, 2, 2, n - 6);
            prop_assert!(a > 0 && b > 0 && c > 0 && d > 0);
            prop_assert_eq!(a % 2, 0);
            prop_assert_eq!(b % 2, 0);
            prop_assert_eq!(c % 2, 0);
            prop_assert_eq!(d % 2, 0);
            prop_assert_eq!(a + b + c + d, n);
        }

        /// Failure condition (parity): the sum of any four even integers
        /// is even, so every odd n must be rejected.
        #[test]
        fn rejects_odd(n in 0u64..200_000) {
            if n % 2 == 1 {
                prop_assert!(!is_equal_to_sum_even(n));
            }
        }
    }

    /// Failure condition (lower bound): the smallest sum of four
    /// positive even integers is 2+2+2+2 = 8, so every n < 8 must be
    /// rejected.  Only 8 values — exhaustive rather than randomised.
    #[test]
    fn rejects_below_minimum_sum() {
        for n in 0u64..8 {
            assert!(!is_equal_to_sum_even(n), "n = {n} should be rejected");
        }
    }
}
