/// HumanEval/60 / CLEVER 059 — `sum_to_n(n)`.  Return `1 + 2 + ... + n`.
/// By convention `sum_to_n(0) = 0`.
///
/// Tail-recursive accumulator (per the project's recursion-preference rule).
fn sum_to_n_at(n: u64, k: u64, acc: u64) -> u64 {
    if k > n {
        acc
    } else {
        sum_to_n_at(n, k + 1, acc + k)
    }
}

pub fn sum_to_n(n: u64) -> u64 {
    if n == 0 {
        0
    } else {
        sum_to_n_at(n, 1, 0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn zero_yields_zero() {
        assert_eq!(sum_to_n(0), 0);
    }

    proptest! {
        /// Postcondition: matches the closed-form `n(n+1)/2`.
        /// Bounded to keep the Rust recursion depth well inside test-thread
        /// stack limits (Rust doesn't TCO; the Hax extraction does).
        #[test]
        fn matches_closed_form(n in 1u64..=5_000) {
            prop_assert_eq!(sum_to_n(n), n * (n + 1) / 2);
        }
    }
}
