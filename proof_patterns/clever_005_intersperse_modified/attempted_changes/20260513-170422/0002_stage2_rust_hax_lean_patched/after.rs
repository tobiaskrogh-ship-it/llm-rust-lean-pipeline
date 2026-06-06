/// Insert `delimiter` between every two consecutive elements of `numbers`.
///
/// Note (Hax compatibility): the natural form uses `Vec::push` and a `for`
/// loop over the input slice. Both extract to identifiers absent from the
/// Hax Lean prelude — `alloc.vec.Impl_1.push` and
/// `core_models.iter.traits.iterator.Iterator.fold` /
/// `core_models.iter.traits.collect.IntoIterator.into_iter` over
/// `RustSlice i64`. The prelude *does* model `Vec::new` and
/// `Vec::extend_from_slice`, so we build the result by tail-recursion over
/// indices, appending one-element slices for each item / delimiter.
fn intersperse_at(numbers: &[i64], delimiter: i64, i: usize, acc: Vec<i64>) -> Vec<i64> {
    if i >= numbers.len() {
        acc
    } else {
        let mut acc = acc;
        if i > 0 {
            acc.extend_from_slice(&[delimiter]);
        }
        let n = numbers[i];
        acc.extend_from_slice(&[n]);
        intersperse_at(numbers, delimiter, i + 1, acc)
    }
}

pub fn intersperse(numbers: &[i64], delimiter: i64) -> Vec<i64> {
    intersperse_at(numbers, delimiter, 0, Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        // Postcondition clause 1 (length):
        // - empty input  -> empty output
        // - input of length n >= 1 -> output of length 2*n - 1
        #[test]
        fn length_matches_contract(numbers in prop::collection::vec(any::<i64>(), 0..32), delimiter in any::<i64>()) {
            let result = intersperse(&numbers, delimiter);
            let expected = if numbers.is_empty() { 0 } else { 2 * numbers.len() - 1 };
            prop_assert_eq!(result.len(), expected);
        }

        // Postcondition clause 2 (even indices preserve the input in order):
        // for every i in 0..numbers.len(), result[2*i] == numbers[i].
        #[test]
        fn even_indices_are_original_numbers(numbers in prop::collection::vec(any::<i64>(), 0..32), delimiter in any::<i64>()) {
            let result = intersperse(&numbers, delimiter);
            for i in 0..numbers.len() {
                prop_assert_eq!(result[2 * i], numbers[i]);
            }
        }

        // Postcondition clause 3 (odd indices are the delimiter):
        // for every i in 0..numbers.len().saturating_sub(1), result[2*i + 1] == delimiter.
        #[test]
        fn odd_indices_are_delimiter(numbers in prop::collection::vec(any::<i64>(), 0..32), delimiter in any::<i64>()) {
            let result = intersperse(&numbers, delimiter);
            for i in 0..numbers.len().saturating_sub(1) {
                prop_assert_eq!(result[2 * i + 1], delimiter);
            }
        }
    }
}
