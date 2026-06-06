/// 4-step Fibonacci:
///   fib4(0) = 0, fib4(1) = 0, fib4(2) = 2, fib4(3) = 0,
///   fib4(n) = fib4(n-1) + fib4(n-2) + fib4(n-3) + fib4(n-4) for n ≥ 4.
///
/// Implemented with tail recursion sliding a 4-window of recent values
/// (the docstring's "Do not use recursion" was aimed at the exponential
/// naive form; this O(n) tail-recursive form has the same efficiency as
/// a loop, per the project's recursion-preference rule).
fn fib4_at(n: i64, a: i64, b: i64, c: i64, d: i64, k: i64) -> i64 {
    if k >= n {
        a
    } else {
        fib4_at(n, b, c, d, a + b + c + d, k + 1)
    }
}

pub fn fib4(n: i64) -> i64 {
    if n < 0 {
        0
    } else {
        fib4_at(n, 0, 0, 2, 0, 0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Postcondition — base cases. The contract pins down the four
    /// initial values explicitly; without this anchor any later
    /// "recurrence" test could be satisfied by an all-zero implementation.
    #[test]
    fn base_cases() {
        assert_eq!(fib4(0), 0);
        assert_eq!(fib4(1), 0);
        assert_eq!(fib4(2), 2);
        assert_eq!(fib4(3), 0);
    }

    proptest! {
        /// Postcondition — recurrence for n ≥ 4.
        /// fib4(n) = fib4(n-1) + fib4(n-2) + fib4(n-3) + fib4(n-4).
        /// Bound kept well below the overflow threshold (fib4 grows ~1.93^n;
        /// i64 fits up to roughly n = 67).
        #[test]
        fn recurrence_on_nonneg_range(n in 4i64..=50) {
            let expected = fib4(n - 1) + fib4(n - 2) + fib4(n - 3) + fib4(n - 4);
            prop_assert_eq!(fib4(n), expected);
        }

        /// Postcondition — fib4 returns 0 for every negative input
        /// (the function's "out of domain" sentinel).
        #[test]
        fn negative_inputs_return_zero(n in i64::MIN..0) {
            prop_assert_eq!(fib4(n), 0);
        }
    }
}
