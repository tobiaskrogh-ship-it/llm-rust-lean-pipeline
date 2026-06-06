/// Remove all elements that occur more than once in `numbers`. Elements
/// kept appear in their original input order.
fn count_at(numbers: &[i64], target: i64, i: usize, acc: i64) -> i64 {
    if i >= numbers.len() {
        acc
    } else if numbers[i] == target {
        count_at(numbers, target, i + 1, acc + 1)
    } else {
        count_at(numbers, target, i + 1, acc)
    }
}

fn build_at(numbers: &[i64], i: usize, mut acc: Vec<i64>) -> Vec<i64> {
    if i >= numbers.len() {
        acc
    } else if count_at(numbers, numbers[i], 0, 0) == 1 {
        acc.push(numbers[i]);
        build_at(numbers, i + 1, acc)
    } else {
        build_at(numbers, i + 1, acc)
    }
}

pub fn remove_duplicates(numbers: &[i64]) -> Vec<i64> {
    build_at(numbers, 0, Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Helper: number of occurrences of `target` in `slice`.
    fn count(slice: &[i64], target: i64) -> usize {
        slice.iter().filter(|&&x| x == target).count()
    }

    /// Helper: check that `sub` appears in `sup` as a subsequence
    /// (same elements, same relative order, possibly with extras in between).
    fn is_subsequence(sub: &[i64], sup: &[i64]) -> bool {
        let mut j = 0;
        for &x in sup {
            if j < sub.len() && sub[j] == x {
                j += 1;
            }
        }
        j == sub.len()
    }

    proptest! {
        // Postcondition (order preservation):
        // the result preserves the original input order, i.e. it is a
        // subsequence of `numbers`. A buggy implementation that sorted
        // or reordered the kept elements would fail this.
        #[test]
        fn output_is_subsequence_of_input(
            input in proptest::collection::vec(-5i64..5, 0..20)
        ) {
            let out = remove_duplicates(&input);
            prop_assert!(is_subsequence(&out, &input));
        }

        // Postcondition (soundness):
        // every element appearing in the output occurs exactly once in
        // the input. Rules out keeping any element that has a duplicate.
        #[test]
        fn every_output_element_appears_exactly_once_in_input(
            input in proptest::collection::vec(-5i64..5, 0..20)
        ) {
            let out = remove_duplicates(&input);
            for &x in &out {
                prop_assert_eq!(count(&input, x), 1);
            }
        }

        // Postcondition (completeness):
        // every input element whose total count is 1 must appear in the
        // output. Rules out trivially-correct implementations such as
        // returning `Vec::new()` that would otherwise satisfy soundness.
        #[test]
        fn every_unique_input_element_is_in_output(
            input in proptest::collection::vec(-5i64..5, 0..20)
        ) {
            let out = remove_duplicates(&input);
            for &x in &input {
                if count(&input, x) == 1 {
                    prop_assert!(out.contains(&x));
                }
            }
        }

        // Postcondition (output uniqueness):
        // the output itself contains no duplicates. While soundness ensures
        // each output element appears once in the input, this independently
        // verifies that each element appears at most once in the output.
        // This rules out buggy implementations that add the same unique
        // element to the output multiple times.
        #[test]
        fn output_contains_no_duplicates(
            input in proptest::collection::vec(-5i64..5, 0..20)
        ) {
            let out = remove_duplicates(&input);
            for &x in &out {
                prop_assert_eq!(count(&out, x), 1);
            }
        }

        // Precondition / Postcondition (empty input):
        // empty input yields empty output. Ensures the base case is correct.
        #[test]
        fn empty_input_yields_empty_output(
            _unused in proptest::option::of(proptest::num::i64::ANY)
        ) {
            let out = remove_duplicates(&[]);
            prop_assert!(out.is_empty());
        }

        // Postcondition (all duplicates):
        // if every input element appears more than once,
        // the output must be empty.
        #[test]
        fn all_duplicates_yields_empty_output(
            input in proptest::collection::vec(-5i64..5, 0..10)
        ) {
            // Duplicate each element so nothing appears exactly once
            let mut duplicated = Vec::new();
            for x in input {
                duplicated.push(x);
                duplicated.push(x);
            }
            let out = remove_duplicates(&duplicated);
            prop_assert!(out.is_empty());
        }

        // Postcondition (all unique):
        // if every input element appears exactly once,
        // the output is identical to the input (order-preserving copy).
        #[test]
        fn all_unique_elements_yields_input_copy(
            input in proptest::collection::vec(-5i64..5, 0..20)
        ) {
            // Only keep elements that appear once in the input
            let unique_only: Vec<i64> = input.iter()
                .filter(|&&x| count(&input, x) == 1)
                .copied()
                .collect();
            let out = remove_duplicates(&input);
            prop_assert_eq!(out, unique_only);
        }
    }
}
