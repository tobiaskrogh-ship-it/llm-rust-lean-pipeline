/// HumanEval/63 — `fibfib(n)`.  3-step Fibonacci-like sequence:
///   fibfib(0) = 0, fibfib(1) = 0, fibfib(2) = 1,
///   fibfib(n) = fibfib(n-1) + fibfib(n-2) + fibfib(n-3) for n ≥ 3.
///
/// Implemented with tail recursion sliding a 3-window (per the
/// project's recursion-preference rule).  Negative inputs collapse to 0.
fn fibfib_at(n: i64, a: i64, b: i64, c: i64, k: i64) -> i64 {
    if k >= n {
        a
    } else {
        fibfib_at(n, b, c, a + b + c, k + 1)
    }
}

pub fn fibfib(n: i64) -> i64 {
    if n < 0 {
        0
    } else {
        fibfib_at(n, 0, 0, 1, 0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Postcondition — base cases.  Without this anchor any later
    /// recurrence test could be satisfied by an all-zero implementation.
    #[test]
    fn base_cases() {
        assert_eq!(fibfib(0), 0);
        assert_eq!(fibfib(1), 0);
        assert_eq!(fibfib(2), 1);
        assert_eq!(fibfib(3), 1);
        assert_eq!(fibfib(4), 2);
        assert_eq!(fibfib(5), 4);
        assert_eq!(fibfib(6), 7);
    }

    proptest! {
        /// Postcondition — recurrence for `n ≥ 3`.
        /// Bound kept well below the i64 overflow threshold (`fibfib`
        /// grows ~1.84^n; i64 fits up to roughly n = 75).
        #[test]
        fn recurrence_on_nonneg_range(n in 3i64..=60) {
            prop_assert_eq!(fibfib(n), fibfib(n - 1) + fibfib(n - 2) + fibfib(n - 3));
        }
    }
}
