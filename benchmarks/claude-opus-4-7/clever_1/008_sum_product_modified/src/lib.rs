/// For a given list of integers, return a tuple of (sum, product).
/// Empty sum is 0; empty product is 1.
//
// `for &n in numbers { ... }` extracts to
// `core_models.iter.traits.iterator.Iterator.fold` over
// `core_models.iter.traits.collect.IntoIterator (RustSlice i64)`, neither
// of which is modeled in the Hax Lean prelude. Per the
// recursion-preference rule (see `iter_chain_to_recursion.rs` and
// `while_loop_to_recursion.rs`), walk the slice by index in a private
// tail-recursive helper; the public function just seeds it with the
// identity elements `(0, 1)`.
fn sum_product_at(numbers: &[i64], i: usize, sum: i64, product: i64) -> (i64, i64) {
    if i >= numbers.len() {
        (sum, product)
    } else {
        sum_product_at(numbers, i + 1, sum + numbers[i], product * numbers[i])
    }
}

pub fn sum_product(numbers: &[i64]) -> (i64, i64) {
    sum_product_at(numbers, 0, 0, 1)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Base case from the doc comment: empty input gives (0, 1).
    /// This pins down the identity elements; without it both 0/1 and any
    /// other "neutral" initial values would satisfy the recursive postconditions
    /// vacuously on the empty slice.
    #[test]
    fn empty_input_returns_zero_and_one() {
        assert_eq!(sum_product(&[]), (0, 1));
    }

    proptest! {
        /// Postcondition 1: the first component equals the sum of the elements.
        /// Bounds chosen so that neither sum nor product can overflow i64:
        /// |sum| <= 10 * 100 = 1000, |product| <= 100^10 = 1e20 — wait, too big.
        /// Use value range [-8, 8] and len <= 10 so |product| <= 8^10 ~ 1.07e9.
        #[test]
        fn sum_component_matches_iter_sum(
            xs in proptest::collection::vec(-8i64..=8, 0..=10)
        ) {
            let (s, _p) = sum_product(&xs);
            let expected: i64 = xs.iter().sum();
            prop_assert_eq!(s, expected);
        }

        /// Postcondition 2: the second component equals the product of the
        /// elements. Independent of the sum claim — a buggy implementation
        /// could compute sum correctly but accumulate product wrong (e.g.
        /// initialize product to 0, or skip the first element).
        #[test]
        fn product_component_matches_iter_product(
            xs in proptest::collection::vec(-8i64..=8, 0..=10)
        ) {
            let (_s, p) = sum_product(&xs);
            let expected: i64 = xs.iter().product();
            prop_assert_eq!(p, expected);
        }
    }
}
