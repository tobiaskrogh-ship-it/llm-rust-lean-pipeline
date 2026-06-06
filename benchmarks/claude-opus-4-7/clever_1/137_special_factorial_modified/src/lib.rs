/// HumanEval/139 / CLEVER 137 — `special_factorial(n)`.  Brazilian
/// factorial: `n! * (n-1)! * (n-2)! * ... * 1!` for `n >= 1`.
/// Convention: returns 1 for n == 0.
fn factorial_at(k: u64, cur: u64, acc: u64) -> u64 {
    if cur > k { acc } else { factorial_at(k, cur + 1, acc * cur) }
}

fn build_at(n: u64, k: u64, acc: u64) -> u64 {
    if k > n { acc }
    else { build_at(n, k + 1, acc * factorial_at(k, 1, 1)) }
}

pub fn special_factorial(n: u64) -> u64 {
    if n == 0 { 1 } else { build_at(n, 1, 1) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn known() {
        assert_eq!(special_factorial(0), 1);
        assert_eq!(special_factorial(1), 1);            // 1!
        assert_eq!(special_factorial(2), 2);            // 1! * 2!
        assert_eq!(special_factorial(3), 12);           // 1! * 2! * 3!
        assert_eq!(special_factorial(4), 288);          // 1 * 2 * 6 * 24
    }

    /// Independent reference implementation: ordinary factorial.
    fn factorial_ref(k: u64) -> u64 {
        (1..=k).product()
    }

    /// Independent reference implementation: Brazilian factorial as the
    /// product `1! * 2! * ... * n!` with the empty-product convention
    /// `special_factorial_ref(0) = 1`.
    fn special_factorial_ref(n: u64) -> u64 {
        (1..=n).map(factorial_ref).product()
    }

    proptest! {
        /// Convention clause: `special_factorial(0) = 1`. Stated separately
        /// from the recurrence because it is a defining base case rather than
        /// something derivable from the product spec.
        #[test]
        fn base_case_zero(_ in 0u64..1) {
            prop_assert_eq!(special_factorial(0), 1);
        }

        /// Postcondition: for every `n` in the non-overflowing range
        /// `0 ..= 8`, `special_factorial(n)` equals the product
        /// `1! * 2! * ... * n!`. `sf(9)` already overflows `u64`, so we cap
        /// the range at 8 — beyond that, the contract is silent.
        #[test]
        fn matches_product_of_factorials(n in 0u64..=8) {
            prop_assert_eq!(special_factorial(n), special_factorial_ref(n));
        }
    }
}
