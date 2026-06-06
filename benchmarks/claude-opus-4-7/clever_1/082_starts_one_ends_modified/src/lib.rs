/// HumanEval/83 / CLEVER 082 — `starts_one_ends(n)`.  Return the count
/// of `n`-digit positive integers that start *or* end with `1`.
///
/// Closed form: for `n == 0` the convention is `0`; for `n == 1` only
/// `1` itself qualifies; for `n ≥ 2`, inclusion–exclusion gives
/// `18 * 10^(n-2)`.
fn pow10_at(k: u64, acc: u64) -> u64 {
    if k == 0 {
        acc
    } else {
        pow10_at(k - 1, acc * 10)
    }
}

pub fn starts_one_ends(n: u64) -> u64 {
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        18 * pow10_at(n - 2, 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn naive(n: u64) -> u64 {
        if n == 0 { return 0; }
        if n == 1 { return 1; }
        let mut low = 1u64;
        for _ in 1..n { low *= 10; }
        let high = low * 10;
        let mut count = 0u64;
        for x in low..high {
            let starts = x / low == 1;
            let ends = x % 10 == 1;
            if starts || ends { count += 1; }
        }
        count
    }

    // Contract base cases pinned to exact values (independent of the
    // brute-force reference, so a bug shared by both would still surface).
    #[test]
    fn small_cases() {
        assert_eq!(starts_one_ends(0), 0);
        assert_eq!(starts_one_ends(1), 1);
        assert_eq!(starts_one_ends(2), 18);
        assert_eq!(starts_one_ends(3), 180);
        assert_eq!(starts_one_ends(4), 1800);
    }

    proptest! {
        // Cross-check the closed form against an independent enumeration
        // of the contract ("count n-digit positives starting or ending
        // with 1"). Range 0..=6 covers both base cases and the inductive
        // case at sizes where brute force is cheap.
        #[test]
        fn matches_brute_force(n in 0u64..=6) {
            prop_assert_eq!(starts_one_ends(n), naive(n));
        }
    }
}
