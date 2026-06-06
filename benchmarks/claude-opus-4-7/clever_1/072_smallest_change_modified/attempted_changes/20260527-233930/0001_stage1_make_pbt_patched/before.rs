/// HumanEval/73 / CLEVER 072 — `smallest_change(arr)`.  Return the
/// minimum number of single-element changes needed to make `arr` a
/// palindrome.  Each mismatch at position `(i, n-1-i)` (for `i < n/2`)
/// can be fixed with one change of either element.
fn count_mismatches_at(arr: &[i64], i: usize, acc: i64) -> i64 {
    let n = arr.len();
    if i >= n / 2 {
        acc
    } else if arr[i] != arr[n - 1 - i] {
        count_mismatches_at(arr, i + 1, acc + 1)
    } else {
        count_mismatches_at(arr, i + 1, acc)
    }
}

pub fn smallest_change(arr: &[i64]) -> i64 {
    count_mismatches_at(arr, 0, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn naive(arr: &[i64]) -> i64 {
        let n = arr.len();
        let mut count = 0i64;
        for i in 0..n / 2 {
            if arr[i] != arr[n - 1 - i] {
                count += 1;
            }
        }
        count
    }

    #[test]
    fn small_cases() {
        assert_eq!(smallest_change(&[]), 0);
        assert_eq!(smallest_change(&[1]), 0);
        assert_eq!(smallest_change(&[1, 1]), 0);
        assert_eq!(smallest_change(&[1, 2]), 1);          // [1,2] → 1 change
        assert_eq!(smallest_change(&[1, 2, 3, 2, 1]), 0); // already palindrome
        assert_eq!(smallest_change(&[1, 2, 3, 4, 5]), 2); // (1,5) (2,4) need fixing
        assert_eq!(smallest_change(&[1, 2, 3, 5, 4, 7, 9, 6]), 4);
    }

    proptest! {
        #[test]
        fn matches_brute_force(arr in proptest::collection::vec(-50i64..=50, 0..16)) {
            prop_assert_eq!(smallest_change(&arr), naive(&arr));
        }

        /// Result is at most floor(n/2): every pair needs at most one change.
        #[test]
        fn upper_bound(arr in proptest::collection::vec(-50i64..=50, 0..16)) {
            prop_assert!(smallest_change(&arr) <= (arr.len() / 2) as i64);
        }
    }
}
