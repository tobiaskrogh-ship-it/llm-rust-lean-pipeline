/// HumanEval/60 — `sum_to_n(n)`.  Return `1 + 2 + ... + n` for `n ≥ 1`;
/// the convention adopted here is `0` for `n ≤ 0`.
///
/// Implemented with tail recursion threading the partial sum through
/// the accumulator (per the project's recursion-preference rule).
fn sum_to_n_at(n: i64, k: i64, acc: i64) -> i64 {
    if k > n {
        acc
    } else {
        sum_to_n_at(n, k + 1, acc + k)
    }
}

pub fn sum_to_n(n: i64) -> i64 {
    if n < 1 {
        0
    } else {
        sum_to_n_at(n, 1, 0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Boundary clause: non-positive inputs collapse to zero.
    #[test]
    fn non_positive_inputs_yield_zero() {
        for n in -5..=0 {
            assert_eq!(sum_to_n(n), 0);
        }
    }

    proptest! {
        /// Postcondition (n ≥ 1): the result equals the closed form
        /// `n(n+1)/2`.  Fully determines the correct value, so any
        /// implementation deviating from `1 + 2 + … + n` is caught.
        /// Bounded to keep the Rust recursion depth well inside test-thread
        /// stack limits (Rust doesn't TCO; the Hax extraction does).
        #[test]
        fn matches_closed_form(n in 1i64..=5_000) {
            prop_assert_eq!(sum_to_n(n), n * (n + 1) / 2);
        }
    }
}
