/// Given a list of deposit and withdrawal operations on an account that
/// starts at zero, return true iff the balance ever falls below zero.
pub fn below_zero(operations: &[i64]) -> bool {
    let mut balance: i64 = 0;
    for &op in operations {
        balance += op;
        if balance < 0 {
            return true;
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Direct specification of the postcondition:
    /// returns `true` iff some non-empty prefix of `operations` sums to a
    /// negative number. Uses `i128` so the spec itself cannot overflow on
    /// any input the function under test can legally accept.
    fn spec_below_zero(operations: &[i64]) -> bool {
        let mut prefix: i128 = 0;
        for &op in operations {
            prefix += op as i128;
            if prefix < 0 {
                return true;
            }
        }
        false
    }

    /// Boundary: an empty sequence has no prefix sum, so the balance never
    /// falls below zero.
    #[test]
    fn empty_input_returns_false() {
        assert!(!below_zero(&[]));
    }

    /// Single element: a negative operation returns true.
    #[test]
    fn single_negative_operation_returns_true() {
        assert!(below_zero(&[-1]));
        assert!(below_zero(&[-1000000]));
    }

    /// Single element: a positive operation returns false.
    #[test]
    fn single_positive_operation_returns_false() {
        assert!(!below_zero(&[1]));
        assert!(!below_zero(&[1000000]));
    }

    /// All positive operations: balance never goes negative.
    #[test]
    fn all_positive_operations_returns_false() {
        assert!(!below_zero(&[1, 2, 3, 4, 5]));
        assert!(!below_zero(&[100, 50, 200]));
    }

    /// All negative operations: first operation makes balance negative.
    #[test]
    fn all_negative_operations_returns_true() {
        assert!(below_zero(&[-1, -2, -3]));
        assert!(below_zero(&[-100]));
    }

    /// Zero-sum prefixes: balance reaches zero but never goes negative.
    #[test]
    fn zero_sum_prefix_returns_false() {
        assert!(!below_zero(&[10, -10]));
        assert!(!below_zero(&[5, -5, 100, 100]));
        assert!(!below_zero(&[1, 1, 1, -3]));
    }

    /// Dip and recovery: balance goes negative then recovers; should return true
    /// because the balance did fall below zero at some point.
    #[test]
    fn dip_below_zero_returns_true() {
        assert!(below_zero(&[1, -10, 20])); // dips to -9
        assert!(below_zero(&[100, -200, 500])); // dips to -100
    }

    proptest! {
        /// Core contract (both directions of the iff):
        /// `below_zero(ops) == true` iff some prefix of `ops` sums to a
        /// negative number.
        ///
        /// Element magnitudes and length are bounded so the running `i64`
        /// balance inside `below_zero` cannot overflow (worst case
        /// |sum| <= 1024 * 1e12 < i64::MAX).
        #[test]
        fn matches_prefix_sum_spec(
            ops in prop::collection::vec(-1_000_000_000_000_i64..=1_000_000_000_000, 0..1024)
        ) {
            prop_assert_eq!(below_zero(&ops), spec_below_zero(&ops));
        }

        /// Positive operations only: should always return false.
        /// Tests that the function correctly handles sequences composed only
        /// of positive values, where the balance monotonically increases.
        #[test]
        fn positive_ops_always_false(
            ops in prop::collection::vec(1_i64..=1_000_000_000_000, 0..100)
        ) {
            prop_assert!(!below_zero(&ops));
        }

        /// First element with negative value: any sequence starting with
        /// a negative operation will immediately return true.
        #[test]
        fn first_negative_returns_true(
            first in i64::MIN..=-1,
            tail in prop::collection::vec(-1_000_000_000_000_i64..=1_000_000_000_000, 0..50)
        ) {
            let mut ops = vec![first];
            ops.extend(tail);
            prop_assert!(below_zero(&ops));
        }
    }
}
