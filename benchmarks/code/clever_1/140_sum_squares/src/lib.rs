/// HumanEval/142 / CLEVER 140 — `sum_squares(lst)`.  Sum the elements
/// after transforming: square if index `i % 3 == 0`; cube if `i % 4 == 0`
/// and not `i % 3 == 0`; otherwise unchanged.
fn sum_at(l: &[i64], i: usize, acc: i64) -> i64 {
    if i >= l.len() { acc }
    else {
        let v = l[i];
        let term = if i % 3 == 0 { v * v }
                   else if i % 4 == 0 { v * v * v }
                   else { v };
        sum_at(l, i + 1, acc + term)
    }
}

pub fn sum_squares(lst: &[i64]) -> i64 {
    sum_at(lst, 0, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    #[test]
    fn known() {
        // index 0: 1² = 1; 1: 2; 2: 3; 3: 16; 4: 5³ = 125; 5: 6; 6: 49; 7: 8
        // sum: 1 + 2 + 3 + 16 + 125 + 6 + 49 + 8 = 210
        assert_eq!(sum_squares(&[1, 2, 3, 4, 5, 6, 7, 8]), 210);
        assert_eq!(sum_squares(&[]), 0);
        // index 0: 5² = 25
        assert_eq!(sum_squares(&[5]), 25);
    }
    proptest! {
        /// Full contract: result equals the index-dependent transform applied
        /// elementwise then summed.  Inputs are bounded so v*v*v stays well
        /// within i64 (|v|^3 ≤ 10^9, sum of ≤20 terms ≤ 2·10^10).
        #[test]
        fn matches_spec(l in proptest::collection::vec(-1000i64..=1000, 0..20)) {
            let expected: i64 = l.iter().enumerate().map(|(i, &v)| {
                if i % 3 == 0 { v * v }
                else if i % 4 == 0 { v * v * v }
                else { v }
            }).sum();
            prop_assert_eq!(sum_squares(&l), expected);
        }
    }
}
