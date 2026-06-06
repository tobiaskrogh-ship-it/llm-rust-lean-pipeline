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
    #[test]
    fn known() {
        assert_eq!(minSubArraySum(&[2, 3, 4, 1, 2, 4]), 1);
        assert_eq!(minSubArraySum(&[-1, -2, -3]), -6);
        assert_eq!(minSubArraySum(&[-1, -2, -3, 2, -10, -5]), -19);
    }
}
