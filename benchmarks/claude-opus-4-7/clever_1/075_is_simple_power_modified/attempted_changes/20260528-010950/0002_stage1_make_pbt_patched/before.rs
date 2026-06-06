/// HumanEval/76 / CLEVER 075 — `is_simple_power(x, n)`.  Return true iff
/// there exists `k ≥ 0` with `n^k == x`.  Conventions:
/// `is_simple_power(1, n) == true` (since `n^0 = 1`);
/// `is_simple_power(x, 1) == (x == 1)`.
///
/// Tail-recursively multiplies a running power of `n` until it meets
/// or exceeds `x`; `cur ≤ x` is the termination measure.
fn power_walks_to(x: u64, n: u64, cur: u64) -> bool {
    if cur == x {
        true
    } else if cur > x {
        false
    } else {
        power_walks_to(x, n, cur * n)
    }
}

pub fn is_simple_power(x: u64, n: u64) -> bool {
    if x == 1 {
        true
    } else if x == 0 || n == 0 {
        false
    } else if n == 1 {
        false
    } else {
        power_walks_to(x, n, n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn naive(x: u64, n: u64) -> bool {
        if x == 1 { return true; }
        if x == 0 || n == 0 { return false; }
        if n == 1 { return x == 1; }
        let mut cur: u128 = 1;
        while cur < x as u128 {
            cur *= n as u128;
        }
        cur == x as u128
    }

    #[test]
    fn small_cases() {
        assert!(is_simple_power(1, 4));     // n^0 = 1
        assert!(is_simple_power(2, 2));
        assert!(is_simple_power(8, 2));
        assert!(is_simple_power(64, 4));
        assert!(is_simple_power(81, 3));
        assert!(!is_simple_power(3, 2));
        assert!(!is_simple_power(5, 3));
        assert!(!is_simple_power(7, 4));
    }

    proptest! {
        // Bounded bidirectional check against a naive reference implementation.
        #[test]
        fn matches_oracle(x in 1u64..=(1u64 << 30), n in 1u64..=20) {
            prop_assert_eq!(is_simple_power(x, n), naive(x, n));
        }

        // Convention: x = 1 is a "simple power" of every n (since n^0 = 1).
        #[test]
        fn one_is_always_simple_power(n in any::<u64>()) {
            prop_assert!(is_simple_power(1, n));
        }

        // Edge case: 0 is never a simple power of any n.
        #[test]
        fn zero_is_never_simple_power(n in any::<u64>()) {
            prop_assert!(!is_simple_power(0, n));
        }

        // Special case n = 1: the only "simple power" of 1 is 1 itself
        // (since 1^k = 1 for all k, so any x != 1 fails).
        #[test]
        fn base_one_simple_power_iff_x_is_one(x in any::<u64>()) {
            prop_assert_eq!(is_simple_power(x, 1), x == 1);
        }

        // Edge case n = 0: the only "simple power" is 1 (via the 0^0 = 1 convention).
        #[test]
        fn base_zero_simple_power_iff_x_is_one(x in any::<u64>()) {
            prop_assert_eq!(is_simple_power(x, 0), x == 1);
        }

        // Positive direction: every actual power n^k (for n >= 2) is recognized.
        #[test]
        fn actual_powers_recognized(n in 2u64..=1000, k in 0u32..=6) {
            let x = (n as u128).pow(k);
            prop_assume!(x <= u64::MAX as u128);
            prop_assert!(is_simple_power(x as u64, n));
        }

        // Negative direction: numbers strictly between consecutive powers
        // n^k and n^(k+1) are not simple powers of n.
        #[test]
        fn between_powers_not_recognized(
            n in 2u64..=1000,
            k in 0u32..=5,
            off in 1u64..,
        ) {
            let lo = (n as u128).pow(k);
            let hi = (n as u128).pow(k + 1);
            prop_assume!(hi <= u64::MAX as u128);
            prop_assume!((off as u128) < hi - lo);
            let x = (lo as u64) + off;
            prop_assert!(!is_simple_power(x, n));
        }
    }
}
