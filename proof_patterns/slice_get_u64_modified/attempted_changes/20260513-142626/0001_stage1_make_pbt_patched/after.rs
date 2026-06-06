/// Returns `numbers[index]` if `index < numbers.len()`, else 0.
///
/// Minimal demonstration of slice indexing with explicit bound discharge:
/// the `numbers[index]` access extracts (via Hax) to the partial operator
/// `numbers[index]_?`, and the proof has to show the index is in bounds
/// in the then-branch.
pub fn slice_get(numbers: &[u64], index: usize) -> u64 {
    if index < numbers.len() {
        numbers[index]
    } else {
        0
    }
}

#[cfg(test)]
mod tests {
    use super::slice_get;
    use proptest::prelude::*;

    proptest! {
        // Postcondition (in-bounds): when `index < numbers.len()`, the function
        // returns exactly `numbers[index]`. We generate the index together with
        // the slice so it is always in range, exercising this branch only.
        #[test]
        fn in_bounds_returns_indexed_element(
            (numbers, index) in proptest::collection::vec(any::<u64>(), 1..32)
                .prop_flat_map(|v| {
                    let len = v.len();
                    (Just(v), 0..len)
                })
        ) {
            prop_assert_eq!(slice_get(&numbers, index), numbers[index]);
        }

        // Postcondition (out-of-bounds): when `index >= numbers.len()`, the
        // function returns the sentinel value 0. We force the index to be
        // out of range (including the empty-slice case where every index is
        // out of range).
        #[test]
        fn out_of_bounds_returns_zero(
            numbers in proptest::collection::vec(any::<u64>(), 0..32),
            extra in 0usize..1024,
        ) {
            let index = numbers.len().saturating_add(extra);
            prop_assert_eq!(slice_get(&numbers, index), 0);
        }
    }
}
