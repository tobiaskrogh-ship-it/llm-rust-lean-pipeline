/// Check if in given list of numbers, are any two numbers closer to each
/// other than the given threshold.
///
/// Note: CLEVER's reference signature is `(numbers: List[float], threshold:
/// float) -> bool`. Translated to `i64` here because the Hax Lean prelude has
/// gaps in `f64` support (no `Impl.abs`, no `PartialOrd f64 f64`, no `Neg
/// f64`, and `Sub.sub` is emitted without type arguments for non-integer
/// types). Semantics are preserved up to integer arithmetic.
fn has_close_elements_at(numbers: &[i64], threshold: i64, k: u64) -> bool {
    let n = numbers.len() as u64;
    if k >= n * n {
        false
    } else {
        let i = (k / n) as usize;
        let j = (k % n) as usize;
        let diff = if numbers[i] > numbers[j] {
            numbers[i] - numbers[j]
        } else {
            numbers[j] - numbers[i]
        };
        if i != j && diff < threshold {
            true
        } else {
            has_close_elements_at(numbers, threshold, k + 1)
        }
    }
}

pub fn has_close_elements(numbers: &[i64], threshold: i64) -> bool {
    has_close_elements_at(numbers, threshold, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Brute-force reference oracle: a close pair exists iff some pair of
    /// distinct indices i, j satisfies |numbers[i] - numbers[j]| < threshold.
    fn close_pair_exists(numbers: &[i64], threshold: i64) -> bool {
        for i in 0..numbers.len() {
            for j in 0..numbers.len() {
                if i != j {
                    let diff = if numbers[i] > numbers[j] {
                        numbers[i] - numbers[j]
                    } else {
                        numbers[j] - numbers[i]
                    };
                    if diff < threshold {
                        return true;
                    }
                }
            }
        }
        false
    }

    // Bounded ranges keep |a - b| well inside i64 so the brute-force oracle
    // (and the function under test) can't overflow on subtraction.
    fn numbers_strategy() -> impl Strategy<Value = Vec<i64>> {
        proptest::collection::vec(-1_000_000i64..=1_000_000, 0..16)
    }

    fn threshold_strategy() -> impl Strategy<Value = i64> {
        -10i64..=2_500_000
    }

    proptest! {
        /// Soundness (postcondition, "true" direction): if the function
        /// reports a close pair, one must actually exist.  Catches buggy
        /// implementations that over-report (e.g. forgetting the `i != j`
        /// guard, or using `<=` instead of `<`).
        #[test]
        fn sound_no_false_positive(
            numbers in numbers_strategy(),
            threshold in threshold_strategy(),
        ) {
            if has_close_elements(&numbers, threshold) {
                prop_assert!(close_pair_exists(&numbers, threshold));
            }
        }

        /// Completeness (postcondition, "false" direction): if a close pair
        /// exists, the function must find it.  Catches implementations that
        /// give up early or fail to scan the whole index space.
        #[test]
        fn complete_no_false_negative(
            numbers in numbers_strategy(),
            threshold in threshold_strategy(),
        ) {
            if close_pair_exists(&numbers, threshold) {
                prop_assert!(has_close_elements(&numbers, threshold));
            }
        }

        /// Edge case for the recursion base: on an empty slice there is no
        /// pair at all, so the result must be `false` for every threshold.
        /// This pins down the `k >= n * n` base case at n = 0.
        #[test]
        fn empty_slice_is_false(threshold: i64) {
            prop_assert!(!has_close_elements(&[], threshold));
        }
    }
}
