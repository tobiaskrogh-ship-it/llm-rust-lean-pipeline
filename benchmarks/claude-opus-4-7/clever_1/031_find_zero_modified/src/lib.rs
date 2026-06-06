/// Polynomial root-finding stub. The original HumanEval task requires
/// real-valued root-finding (bisection / Newton's method on floats);
/// CLEVER's Note(George) acknowledges Real is not a computable type and
/// that integer roots are not guaranteed. This stub returns 0 (the
/// constant-coefficient slot, where many low-order polynomials have a
/// root) so the crate compiles and can carry placeholder obligations.
/// A real implementation would require integer bisection over a bounded
/// range with a sign-change predicate.
pub fn find_zero(xs: &[i64]) -> i64 {
    let _ = xs;
    0
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    // Postcondition: `find_zero` returns exactly 0 for any input slice.
    // Because proptest will not panic before reaching this assertion,
    // this also captures totality on non-empty inputs.
    proptest! {
        #[test]
        fn returns_zero_for_any_input(
            xs in proptest::collection::vec(any::<i64>(), 0..32)
        ) {
            prop_assert_eq!(find_zero(&xs), 0);
        }
    }

    // Totality edge case: the empty slice does not panic, and the
    // return value still satisfies the postcondition. Pinned as an
    // explicit unit test because proptest's vector generator does not
    // guarantee that the empty case is sampled on every run.
    #[test]
    fn returns_zero_on_empty_slice() {
        assert_eq!(find_zero(&[]), 0);
    }
}
