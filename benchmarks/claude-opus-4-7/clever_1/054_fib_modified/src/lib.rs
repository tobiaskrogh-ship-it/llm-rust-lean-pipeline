/// HumanEval/55 / CLEVER 054 — `fib(n)`.  Standard Fibonacci:
/// `fib(0) = 0`, `fib(1) = 1`, `fib(n) = fib(n-1) + fib(n-2)` for `n ≥ 2`.
///
/// O(n) tail recursion sliding a 2-window (per the project's
/// recursion-preference rule).
fn fib_at(n: u64, a: u64, b: u64, k: u64) -> u64 {
    if k >= n {
        a
    } else {
        fib_at(n, b, a + b, k + 1)
    }
}

pub fn fib(n: u64) -> u64 {
    fib_at(n, 0, 1, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Postcondition — base cases (pinned explicitly so the recurrence
    /// test can't be satisfied by an all-zero implementation).
    #[test]
    fn base_cases() {
        assert_eq!(fib(0), 0);
        assert_eq!(fib(1), 1);
        assert_eq!(fib(2), 1);
        assert_eq!(fib(3), 2);
        assert_eq!(fib(4), 3);
        assert_eq!(fib(5), 5);
    }

    proptest! {
        /// Postcondition — recurrence for `n ≥ 2`.
        /// Bound kept well below the u64 overflow threshold.
        #[test]
        fn recurrence(n in 2u64..=80) {
            prop_assert_eq!(fib(n), fib(n - 1) + fib(n - 2));
        }
    }
}
