/// Insert `delimiter` between every two consecutive elements of `numbers`.
//
// Hax-compatibility rewrite (see `rewrite_patterns/vec_push_to_extend_from_slice_typed_chunk.rs`):
//   * `for &n in numbers` extracts to unmodeled `Iterator::fold` over a
//     slice's `IntoIterator` — rewrite as a tail-recursive index walk.
//   * `Vec::push` (`alloc.vec.Impl_1.push`) is undefined in the Hax Lean
//     prelude — use `extend_from_slice` with a *typed* `[i64; N]` let
//     binding so Hax's emitted `RustArray i64 N` carries the size in the
//     ascription and `unsize` elaborates cleanly.
fn intersperse_at(numbers: &[i64], delimiter: i64, i: usize, acc: Vec<i64>) -> Vec<i64> {
    if i >= numbers.len() {
        acc
    } else {
        let n = numbers[i];
        let mut acc = acc;
        if i == 0 {
            let chunk: [i64; 1] = [n];
            acc.extend_from_slice(&chunk);
        } else {
            let chunk: [i64; 2] = [delimiter, n];
            acc.extend_from_slice(&chunk);
        }
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
