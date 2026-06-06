/// HumanEval/135 / CLEVER 134 — `can_arrange(arr)`.  Return the largest
/// index `i` such that `arr[i] <= arr[i-1]`, or `-1` if no such index
/// exists.  Note the spec says "not greater than or equal to the
/// element immediately preceding it" → arr[i] < arr[i-1].  i64 because
/// of the -1 sentinel.
fn scan_at(arr: &[i64], i: usize, best: i64) -> i64 {
    if i >= arr.len() { best }
    else if arr[i] < arr[i - 1] { scan_at(arr, i + 1, i as i64) }
    else { scan_at(arr, i + 1, best) }
}

pub fn can_arrange(arr: &[i64]) -> i64 {
    if arr.len() < 2 { -1 } else { scan_at(arr, 1, -1) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn known() {
        assert_eq!(can_arrange(&[1, 2, 4, 3, 5]), 3);
        assert_eq!(can_arrange(&[1, 2, 3]), -1);
        assert_eq!(can_arrange(&[]), -1);
        assert_eq!(can_arrange(&[5]), -1);
    }

    proptest! {
        /// Claim 1: when the result is not -1, it is a valid index >= 1 and
        /// it really IS a descending position (arr[result] < arr[result-1]).
        /// Establishes both well-formedness of the index and the "is a
        /// descending position" half of the spec.
        #[test]
        fn result_is_a_descending_position(arr in proptest::collection::vec(any::<i64>(), 0..50)) {
            let r = can_arrange(&arr);
            if r != -1 {
                prop_assert!(r >= 1);
                prop_assert!((r as usize) < arr.len());
                let i = r as usize;
                prop_assert!(arr[i] < arr[i - 1]);
            }
        }

        /// Claim 2: maximality. When the result is not -1, no descending
        /// position exists strictly after it. Together with claim 1 this
        /// pins down which descending index is returned.
        #[test]
        fn result_is_the_largest_descending_position(arr in proptest::collection::vec(any::<i64>(), 0..50)) {
            let r = can_arrange(&arr);
            if r != -1 {
                let i = r as usize;
                for j in (i + 1)..arr.len() {
                    prop_assert!(arr[j] >= arr[j - 1]);
                }
            }
        }

        /// Claim 3: the result is -1 iff the array is non-strictly
        /// increasing. Covers the empty / singleton cases vacuously and
        /// is the only way -1 can be returned.
        #[test]
        fn minus_one_iff_non_decreasing(arr in proptest::collection::vec(any::<i64>(), 0..50)) {
            let r = can_arrange(&arr);
            let non_decreasing = (1..arr.len()).all(|j| arr[j] >= arr[j - 1]);
            prop_assert_eq!(r == -1, non_decreasing);
        }
    }
}
