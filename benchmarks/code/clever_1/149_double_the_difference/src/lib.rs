/// HumanEval/151 / CLEVER 149 — `double_the_difference(numbers)`.  Sum
/// of squares of the positive odd integers in `numbers`.  Negative
/// values are ignored.  (All inputs are already integers here.)
fn sum_at(l: &[i64], i: usize, acc: i64) -> i64 {
    if i >= l.len() { acc }
    else if l[i] > 0 && l[i] % 2 == 1 { sum_at(l, i + 1, acc + l[i] * l[i]) }
    else { sum_at(l, i + 1, acc) }
}

pub fn double_the_difference(numbers: &[i64]) -> i64 {
    sum_at(numbers, 0, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn known() {
        assert_eq!(double_the_difference(&[]), 0);
        assert_eq!(double_the_difference(&[1, 3, 2, 0]), 10);     // 1 + 9
        assert_eq!(double_the_difference(&[-1, -2, 0]), 0);
        assert_eq!(double_the_difference(&[9, -2]), 81);
    }

    // Element magnitude is bounded so n*n fits in i64 and a moderate-length
    // list of squares does too:  100 * 10_000^2 = 10^10  <  i64::MAX  (~9.2e18).
    fn small_i64() -> impl Strategy<Value = i64> { -10_000i64..=10_000 }
    fn small_vec() -> impl Strategy<Value = Vec<i64>> {
        prop::collection::vec(small_i64(), 0..=100)
    }

    proptest! {
        // Postcondition on a positive odd singleton: the contribution is n*n.
        // Catches bugs where the wrong arithmetic (n, 2*n, |n|, …) is used.
        #[test]
        fn singleton_positive_odd(k in 0i64..=4_999) {
            let n = 2 * k + 1;                          // positive and odd
            prop_assert_eq!(double_the_difference(&[n]), n * n);
        }

        // Selection clause: non-positive elements contribute nothing.
        // Catches a missing `> 0` guard (which would let negative odds count).
        #[test]
        fn singleton_non_positive(n in -10_000i64..=0) {
            prop_assert_eq!(double_the_difference(&[n]), 0);
        }

        // Selection clause: even elements contribute nothing (independent of sign).
        // Catches a missing odd-parity check.
        #[test]
        fn singleton_even(k in -5_000i64..=5_000) {
            let n = 2 * k;                              // even, any sign
            prop_assert_eq!(double_the_difference(&[n]), 0);
        }

        // Structural postcondition: additive over list concatenation.
        // Together with the singleton clauses above and `known`'s empty case,
        // this pins down the function inductively on every list.
        #[test]
        fn additive_over_concat(xs in small_vec(), ys in small_vec()) {
            let mut zs = xs.clone();
            zs.extend(ys.iter().copied());
            prop_assert_eq!(
                double_the_difference(&zs),
                double_the_difference(&xs) + double_the_difference(&ys)
            );
        }
    }
}
