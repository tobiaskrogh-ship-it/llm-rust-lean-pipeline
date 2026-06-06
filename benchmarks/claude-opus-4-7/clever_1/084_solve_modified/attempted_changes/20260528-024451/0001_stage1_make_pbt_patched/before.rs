/// HumanEval/85 / CLEVER 084 — `solve(n)`.  Sum the even values at odd
/// indices of `n`.  Empty list yields 0.
fn sum_at(n: &[i64], i: usize, acc: i64) -> i64 {
    if i >= n.len() {
        acc
    } else if i % 2 == 1 && n[i] % 2 == 0 {
        sum_at(n, i + 1, acc + n[i])
    } else {
        sum_at(n, i + 1, acc)
    }
}

pub fn solve(n: &[i64]) -> i64 {
    sum_at(n, 0, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn naive(n: &[i64]) -> i64 {
        n.iter().enumerate()
            .filter(|(i, &v)| i % 2 == 1 && v % 2 == 0)
            .map(|(_, &v)| v)
            .sum()
    }

    #[test]
    fn small_cases() {
        assert_eq!(solve(&[]), 0);
        assert_eq!(solve(&[4, 2, 6, 7]), 2);
        assert_eq!(solve(&[1, 3, 5, 7]), 0);
    }

    proptest! {
        #[test]
        fn matches_brute(l in proptest::collection::vec(-1000i64..=1000, 0..32)) {
            prop_assert_eq!(solve(&l), naive(&l));
        }
    }
}
