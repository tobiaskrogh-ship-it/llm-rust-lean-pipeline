/// HumanEval/133 / CLEVER 132 — `sum_squares(lst)`.  Return the sum of
/// squares of the elements of `lst` (already integers; the "round up
/// to ceiling" step is a no-op).
fn sum_at(l: &[i64], i: usize, acc: i64) -> i64 {
    if i >= l.len() { acc } else { sum_at(l, i + 1, acc + l[i] * l[i]) }
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
        assert_eq!(sum_squares(&[1, 2, 3]), 14);
        assert_eq!(sum_squares(&[]), 0);
        assert_eq!(sum_squares(&[-1, -2, -3]), 14);
    }
    proptest! {
        #[test]
        fn matches(l in proptest::collection::vec(-1000i64..=1000, 0..20)) {
            let expected: i64 = l.iter().map(|v| v * v).sum();
            prop_assert_eq!(sum_squares(&l), expected);
        }
    }
}
