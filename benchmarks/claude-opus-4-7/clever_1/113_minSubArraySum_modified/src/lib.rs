/// HumanEval/114 / CLEVER 113 — `minSubArraySum(nums)`.  Minimum sum
/// of any non-empty contiguous subarray.  Empty input: returns 0
/// (degenerate sentinel; spec assumes non-empty input).
fn run_at(l: &[i64], i: usize, cur: i64, best: i64) -> i64 {
    if i >= l.len() { best }
    else {
        let ext = cur + l[i];
        let nc = if ext < l[i] { ext } else { l[i] };
        let nb = if nc < best { nc } else { best };
        run_at(l, i + 1, nc, nb)
    }
}

#[allow(non_snake_case)]
pub fn minSubArraySum(nums: &[i64]) -> i64 {
    if nums.is_empty() { 0 } else { run_at(nums, 1, nums[0], nums[0]) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Sentinel (degenerate input): empty slice returns 0. The general
    /// "minimum over non-empty contiguous subarrays" spec is vacuous
    /// here, so this case must be stated explicitly. Catches any
    /// implementation that panics on empty input or returns a different
    /// sentinel.
    #[test]
    fn empty_input_returns_zero() {
        assert_eq!(minSubArraySum(&[]), 0);
    }

    proptest! {
        /// Postcondition on length-1 inputs: the only non-empty
        /// contiguous subarray of `[x]` is `[x]` itself, so the result
        /// must equal `x`. Catches off-by-one initialization (e.g.
        /// starting the recursion at index 0 with cur = 0, which would
        /// return min(0, x) instead of x for positive x).
        #[test]
        fn singleton_returns_element(x in -1_000_000i64..1_000_000) {
            prop_assert_eq!(minSubArraySum(&[x]), x);
        }

        /// Achievability (postcondition): the returned value is the
        /// sum of *some* non-empty contiguous subarray. Without this,
        /// an implementation could return `i64::MIN` (or any spuriously
        /// small value) and trivially satisfy the lower-bound property.
        /// A buggy variant that off-by-one extends one element past
        /// the end, or sums something other than a contiguous slice,
        /// would be caught here.
        #[test]
        fn result_is_achieved_by_some_subarray(
            nums in proptest::collection::vec(-1000i64..1000, 1..16)
        ) {
            let result = minSubArraySum(&nums);
            let mut found = false;
            for i in 0..nums.len() {
                let mut s: i64 = 0;
                for j in i..nums.len() {
                    s += nums[j];
                    if s == result { found = true; }
                }
            }
            prop_assert!(found, "no contiguous subarray of {:?} sums to {}", nums, result);
        }

        /// Minimality (postcondition): the returned value is a lower
        /// bound on every non-empty contiguous subarray sum. Together
        /// with `result_is_achieved_by_some_subarray`, this pins down
        /// the function exactly. A buggy implementation that only
        /// considered prefixes, only singletons, or skipped certain
        /// start indices would return a value strictly greater than
        /// some real subarray sum and fail here.
        #[test]
        fn result_lower_bounds_all_subarrays(
            nums in proptest::collection::vec(-1000i64..1000, 1..16)
        ) {
            let result = minSubArraySum(&nums);
            for i in 0..nums.len() {
                let mut s: i64 = 0;
                for j in i..nums.len() {
                    s += nums[j];
                    prop_assert!(
                        result <= s,
                        "result {} exceeds subarray sum {} for nums[{}..={}] in {:?}",
                        result, s, i, j, nums
                    );
                }
            }
        }
    }
}
