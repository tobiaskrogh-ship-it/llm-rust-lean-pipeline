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
///
/// The size-1 array literal `&[x]` extracts via Hax as
/// `rust_primitives.unsize (RustArray.ofVec #v[x])`, and Lean's
/// elaborator needs to unify the array size (a `usize` parameter on
/// `RustArray`) with the Nat-1 of the vector literal. When `x` is a
/// do-bound variable from an effectful expression (e.g. `numbers[i]_?`),
/// the size metavariable is abstracted over the do-bound name and
/// elaboration fails with `Application type mismatch ... Vector i64 1`.
/// Routing the element through a regular function parameter (here
/// `push_one` / `push_two`) breaks that abstraction: inside the helper,
/// the element is a plain parameter and the size unifies cleanly to
/// `(1 : usize)` / `(2 : usize)`.
fn push_one(acc: Vec<i64>, x: i64) -> Vec<i64> {
    let mut acc = acc;
    acc.extend_from_slice(&[x]);
    acc
}

fn push_two(acc: Vec<i64>, x: i64, y: i64) -> Vec<i64> {
    let mut acc = acc;
    acc.extend_from_slice(&[x, y]);
    acc
}

fn intersperse_at(numbers: &[i64], delimiter: i64, i: usize, acc: Vec<i64>) -> Vec<i64> {
    if i >= numbers.len() {
        acc
    } else {
        let n = numbers[i];
        let acc = if i == 0 {
            push_one(acc, n)
        } else {
            push_two(acc, delimiter, n)
        };
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
