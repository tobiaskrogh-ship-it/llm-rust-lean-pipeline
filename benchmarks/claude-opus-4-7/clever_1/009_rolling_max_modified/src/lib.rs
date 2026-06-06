/// From a given list of integers, generate a list of the rolling maximum
/// element found until each position in the sequence.
/// (CLEVER's signature column for problem 9 lists `sum_product(...) -> (int, int)`
/// but its docstring describes rolling-max. We follow the docstring.)
///
/// Hax-compatibility rewrite notes:
///   * `for &n in numbers` desugars to `Iterator::fold` over
///     `IntoIterator (RustSlice i64)`, neither modeled by the Hax Lean
///     prelude. Converted to index-based tail recursion per
///     `rewrite_patterns/for_loop_over_slice_to_recursion.rs` (also
///     preferred over `while` per the recursion-preference rule).
///   * `Vec::push` (`alloc.vec.Impl_1.push`) is undefined in the prelude;
///     `Vec::extend_from_slice` IS defined and is used here with a typed
///     let-bound `[i64; 1]` chunk so the array size appears in the type
///     ascription and Hax can resolve `unsize`'s `RustArray` size
///     parameter. See `rewrite_patterns/vec_push_to_extend_from_slice_typed_chunk.rs`.
///   * `i64::MIN` (`core_models.num.Impl_*.MIN`) is undefined in the
///     prelude. Replaced by special-casing `i == 0` inside the recursion:
///     at the first index the running maximum is unconditionally set to
///     the element itself, so no sentinel "minus infinity" is needed.
///     See `rewrite_patterns/primitive_int_assoc_const.rs`.
fn rolling_max_at(numbers: &[i64], i: usize, max_so_far: i64, acc: Vec<i64>) -> Vec<i64> {
    if i >= numbers.len() {
        acc
    } else {
        let n = numbers[i];
        let new_max = if i == 0 || n > max_so_far { n } else { max_so_far };
        let mut acc = acc;
        // Typed let binding so Hax emits the size in the type annotation
        // (`RustArray i64 1`) and `unsize` can elaborate the size param.
        let chunk: [i64; 1] = [new_max];
        acc.extend_from_slice(&chunk);
        rolling_max_at(numbers, i + 1, new_max, acc)
    }
}

pub fn rolling_max(numbers: &[i64]) -> Vec<i64> {
    rolling_max_at(numbers, 0, 0, Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Boundary case: empty input produces empty output.
    /// (Captures the postcondition on the degenerate input where the
    /// general "prefix-max at each index" property is vacuously true,
    /// but still constrains the implementation to return an empty Vec
    /// rather than panicking or fabricating elements.)
    #[test]
    fn empty_input_yields_empty_output() {
        let out = rolling_max(&[]);
        assert!(out.is_empty());
    }

    proptest! {
        /// Postcondition (length): the output has exactly the same
        /// length as the input. A buggy implementation that drops or
        /// duplicates elements would be caught here.
        #[test]
        fn output_length_equals_input_length(numbers in proptest::collection::vec(any::<i64>(), 0..64)) {
            let out = rolling_max(&numbers);
            prop_assert_eq!(out.len(), numbers.len());
        }

        /// Core postcondition: for every index `i`, `result[i]` equals
        /// the maximum of `numbers[0..=i]`. This is the defining
        /// specification of the rolling maximum; an implementation
        /// that returned any other valid-looking sequence (e.g. the
        /// rolling minimum, the input unchanged, or a one-off shift)
        /// would fail this test.
        #[test]
        fn each_element_is_prefix_max(numbers in proptest::collection::vec(any::<i64>(), 1..64)) {
            let out = rolling_max(&numbers);
            for i in 0..numbers.len() {
                let expected = *numbers[0..=i].iter().max().unwrap();
                prop_assert_eq!(out[i], expected);
            }
        }
    }
}
