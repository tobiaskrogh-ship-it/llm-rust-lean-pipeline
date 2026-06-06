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
        #[test]
        fn matches_oracle(x in 1u64..=(1u64 << 30), n in 1u64..=20) {
            prop_assert_eq!(is_simple_power(x, n), naive(x, n));
        }
    }
}
