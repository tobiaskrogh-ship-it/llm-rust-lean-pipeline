/// HumanEval/63 / CLEVER 062 — `fibfib(n)`.  3-step Fibonacci-like:
///   fibfib(0) = 0, fibfib(1) = 0, fibfib(2) = 1,
///   fibfib(n) = fibfib(n-1) + fibfib(n-2) + fibfib(n-3) for n ≥ 3.
///
/// Tail-recursive 3-window slide (per the recursion-preference rule).
fn fibfib_at(n: u64, a: u64, b: u64, c: u64, k: u64) -> u64 {
    if k >= n {
        a
    } else {
        fibfib_at(n, b, c, a + b + c, k + 1)
    }
}

pub fn fibfib(n: u64) -> u64 {
    fibfib_at(n, 0, 0, 1, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

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
        #[test]
        fn recurrence(n in 3u64..=60) {
            prop_assert_eq!(fibfib(n), fibfib(n - 1) + fibfib(n - 2) + fibfib(n - 3));
        }
    }
}
