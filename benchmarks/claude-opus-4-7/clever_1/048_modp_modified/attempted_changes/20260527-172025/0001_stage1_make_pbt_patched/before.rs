/// HumanEval/49 / CLEVER 048 — `modp(n, p)`.  Return `2^n mod p`.
/// `p == 0` is treated as a degenerate input and yields `0`.
///
/// Iterative O(n) tail recursion; the accumulator stays in `[0, p)` so
/// `acc * 2 < 2 * p`.  For `p < 2^63` no overflow.
fn pow2_mod_at(n: u64, p: u64, acc: u64, k: u64) -> u64 {
    if k >= n {
        acc
    } else {
        pow2_mod_at(n, p, (acc * 2) % p, k + 1)
    }
}

pub fn modp(n: u64, p: u64) -> u64 {
    if p == 0 {
        0
    } else {
        pow2_mod_at(n, p, 1 % p, 0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn naive(n: u64, p: u64) -> u64 {
        if p == 0 { return 0; }
        let mut acc: u128 = 1 % p as u128;
        for _ in 0..n {
            acc = (acc * 2) % p as u128;
        }
        acc as u64
    }

    #[test]
    fn small_cases() {
        assert_eq!(modp(0, 5), 1);
        assert_eq!(modp(0, 1), 0);
        assert_eq!(modp(3, 5), 3);
        assert_eq!(modp(10, 7), 2);
    }

    #[test]
    fn p_one_yields_zero() {
        for n in 0..10u64 { assert_eq!(modp(n, 1), 0); }
    }

    proptest! {
        #[test]
        fn matches_oracle(n in 0u64..=200, p in 1u64..=(1u64 << 30)) {
            prop_assert_eq!(modp(n, p), naive(n, p));
        }

        #[test]
        fn in_range(n in 0u64..=200, p in 1u64..=(1u64 << 30)) {
            let r = modp(n, p);
            prop_assert!(r < p);
        }
    }
}
