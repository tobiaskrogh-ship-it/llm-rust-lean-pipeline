/// HumanEval/122 / CLEVER 121 — `add_elements(arr, k)`.  Sum of the
/// elements among the first `k` of `arr` whose absolute value has at
/// most 2 decimal digits (i.e. `-99 ≤ v ≤ 99`).
fn sum_at(arr: &[i64], k: i64, i: i64, acc: i64) -> i64 {
    if i >= k || (i as usize) >= arr.len() { acc }
    else {
        let v = arr[i as usize];
        let abs_v = if v < 0 { -v } else { v };
        if abs_v <= 99 { sum_at(arr, k, i + 1, acc + v) }
        else { sum_at(arr, k, i + 1, acc) }
    }
}

pub fn add_elements(arr: &[i64], k: i64) -> i64 {
    if k <= 0 { 0 } else { sum_at(arr, k, 0, 0) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn known() {
        assert_eq!(add_elements(&[111, 21, 3, 4000, 5, 6, 7, 8, 9], 4), 24); // 21 + 3
        assert_eq!(add_elements(&[1, 2, 3, 4], 3), 6);
    }

    proptest! {
        /// Contract: when `k <= 0`, the function returns `0` regardless of
        /// the array. This pins down the explicit `k <= 0` branch in
        /// `add_elements` independently of the recursive sum logic.
        #[test]
        fn nonpositive_k_returns_zero(
            arr in proptest::collection::vec(-1000i64..=1000, 0..256),
            k in i64::MIN..=0i64,
        ) {
            prop_assert_eq!(add_elements(&arr, k), 0);
        }

        /// Postcondition: for `k > 0`, the result equals the sum of the
        /// elements among the first `k` of `arr` whose absolute value is at
        /// most 99 (i.e. fits in at most two decimal digits).
        ///
        /// This single property pins down the entire intended behaviour for
        /// the active branch: the prefix bound `k`, the `|v| <= 99` filter
        /// (boundary at ±99 / ±100 is exercised by proptest edge-case
        /// shrinking), and that nothing else is added.
        #[test]
        fn matches_spec_for_positive_k(
            arr in proptest::collection::vec(-1000i64..=1000, 0..256),
            k in 1i64..512,
        ) {
            let expected: i64 = arr.iter()
                .take(k as usize)
                .filter(|&&v| v.abs() <= 99)
                .sum();
            prop_assert_eq!(add_elements(&arr, k), expected);
        }
    }
}
