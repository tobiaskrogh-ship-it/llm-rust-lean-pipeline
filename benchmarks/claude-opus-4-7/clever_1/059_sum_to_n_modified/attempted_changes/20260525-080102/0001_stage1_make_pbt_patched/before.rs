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
        /// Postcondition: matches the closed-form `n(n+1)/2`.
        /// Bounded to keep the Rust recursion depth well inside test-thread
        /// stack limits (Rust doesn't TCO; the Hax extraction does).
        #[test]
        fn matches_closed_form(n in 1i64..=5_000) {
            prop_assert_eq!(sum_to_n(n), n * (n + 1) / 2);
        }

        /// Recurrence: `sum_to_n(n) = sum_to_n(n - 1) + n` for `n ≥ 1`.
        /// Catches off-by-one and base-case errors that the closed-form
        /// check can mask (e.g. always returning `n*(n+1)/2 + 1`).
        #[test]
        fn recurrence_step(n in 2i64..=2_000) {
            prop_assert_eq!(sum_to_n(n), sum_to_n(n - 1) + n);
        }
    }
}
