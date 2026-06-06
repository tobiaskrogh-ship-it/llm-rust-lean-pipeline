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
    #[test]
    fn known() {
        assert!(!is_equal_to_sum_even(4));
        assert!(is_equal_to_sum_even(8));   // 2+2+2+2
        assert!(!is_equal_to_sum_even(9));
        assert!(is_equal_to_sum_even(10));  // 2+2+2+4
        assert!(!is_equal_to_sum_even(7));
    }
}
