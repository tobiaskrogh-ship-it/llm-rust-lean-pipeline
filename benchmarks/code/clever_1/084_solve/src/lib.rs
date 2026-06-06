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

    /// Reference spec: sum of `n[i]` for odd `i` where `n[i]` is even.
    fn naive(n: &[i64]) -> i64 {
        n.iter()
            .enumerate()
            .filter(|(i, v)| i % 2 == 1 && *v % 2 == 0)
            .map(|(_, v)| *v)
            .sum()
    }

    /// Boundary: empty list has no indices, so the sum is 0.
    #[test]
    fn empty_returns_zero() {
        assert_eq!(solve(&[]), 0);
    }

    /// Spot-checks documenting intended behaviour:
    ///   - `[4, 2, 6, 7]`: only index 1 holds an even value (`2`).
    ///   - `[1, 3, 5, 7]`: no odd-indexed value is even.
    ///   - `[2, 4, 6, 8]`: odd indices 1 and 3 hold `4` and `8`.
    #[test]
    fn known_examples() {
        assert_eq!(solve(&[4, 2, 6, 7]), 2);
        assert_eq!(solve(&[1, 3, 5, 7]), 0);
        assert_eq!(solve(&[2, 4, 6, 8]), 12);
    }

    proptest! {
        /// Postcondition: the result equals the reference spec on arbitrary
        /// small lists.  This single property pins down the function's
        /// observable behaviour for in-range inputs.
        #[test]
        fn matches_spec(l in proptest::collection::vec(-1000i64..=1000, 0..32)) {
            prop_assert_eq!(solve(&l), naive(&l));
        }

        /// Boundary: a singleton list has no odd index, so the result is 0
        /// regardless of the element's value.  Sharpens the postcondition
        /// at the smallest non-empty input.
        #[test]
        fn singleton_returns_zero(v in any::<i64>()) {
            prop_assert_eq!(solve(&[v]), 0);
        }
    }
}
