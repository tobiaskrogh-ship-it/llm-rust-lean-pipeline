/// Insert `delimiter` between every two consecutive elements of `numbers`.
pub fn intersperse(numbers: &[i64], delimiter: i64) -> Vec<i64> {
    let mut result: Vec<i64> = Vec::new();
    let mut first = true;
    for &n in numbers {
        if !first {
            result.push(delimiter);
        }
        result.push(n);
        first = false;
    }
    result
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
