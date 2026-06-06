/// HumanEval/108 / CLEVER 107 — `count_nums(arr)`.  Count elements
/// whose *signed* digit sum is > 0.  For negative `n`, the leading
/// digit takes the sign (e.g. `-123 → -1 + 2 + 3 = 4`).
fn first_digit_at(n: i64) -> i64 {
    if n < 10 { n } else { first_digit_at(n / 10) }
}

fn digit_sum_at(n: i64, acc: i64) -> i64 {
    if n == 0 { acc } else { digit_sum_at(n / 10, acc + n % 10) }
}

fn signed_digit_sum(n: i64) -> i64 {
    if n == 0 { 0 }
    else if n > 0 { digit_sum_at(n, 0) }
    else {
        let m = -n;
        digit_sum_at(m, 0) - 2 * first_digit_at(m)
    }
}

fn count_at(arr: &[i64], i: usize, acc: i64) -> i64 {
    if i >= arr.len() { acc }
    else if signed_digit_sum(arr[i]) > 0 { count_at(arr, i + 1, acc + 1) }
    else { count_at(arr, i + 1, acc) }
}

pub fn count_nums(arr: &[i64]) -> i64 {
    count_at(arr, 0, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn known() {
        assert_eq!(count_nums(&[]), 0);
        assert_eq!(count_nums(&[-1, 11, -11]), 1);  // 11 only
        assert_eq!(count_nums(&[1, 1, 2]), 3);
    }

    // We restrict element magnitudes to avoid the `-i64::MIN` overflow inside
    // `signed_digit_sum`; the chosen range easily covers every interesting
    // digit-sum behaviour.
    proptest! {
        #![proptest_config(ProptestConfig::with_cases(64))]

        /// The result is a real count: non-negative and at most the slice length.
        #[test]
        fn count_is_bounded(
            arr in proptest::collection::vec(-1_000_000i64..=1_000_000, 0..30),
        ) {
            let c = count_nums(&arr);
            prop_assert!(c >= 0);
            prop_assert!(c <= arr.len() as i64);
        }

        /// Every strictly positive integer has positive signed digit sum,
        /// so a slice consisting only of positives is fully counted.
        #[test]
        fn all_positives_counted(
            arr in proptest::collection::vec(1i64..=1_000_000, 0..30),
        ) {
            prop_assert_eq!(count_nums(&arr), arr.len() as i64);
        }

        /// `signed_digit_sum(0) == 0`, so zeros never satisfy the `> 0` predicate.
        #[test]
        fn zeros_never_counted(n in 0usize..30) {
            let arr = vec![0i64; n];
            prop_assert_eq!(count_nums(&arr), 0);
        }

        /// For a single-digit negative `-d` (1 ≤ d ≤ 9) the signed digit sum
        /// is `d - 2d = -d < 0`, so such elements are never counted.
        #[test]
        fn small_negatives_never_counted(
            arr in proptest::collection::vec(-9i64..=-1, 0..30),
        ) {
            prop_assert_eq!(count_nums(&arr), 0);
        }

        /// Counting is additive over concatenation:
        /// `count_nums(a ++ b) == count_nums(a) + count_nums(b)`.
        #[test]
        fn count_is_additive(
            a in proptest::collection::vec(-1_000_000i64..=1_000_000, 0..20),
            b in proptest::collection::vec(-1_000_000i64..=1_000_000, 0..20),
        ) {
            let mut combined = a.clone();
            combined.extend_from_slice(&b);
            prop_assert_eq!(count_nums(&combined), count_nums(&a) + count_nums(&b));
        }
    }
}
