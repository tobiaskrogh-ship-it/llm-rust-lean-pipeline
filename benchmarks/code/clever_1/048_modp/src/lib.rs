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

    /// Oracle: `2^n mod p` computed with `u128` to avoid intermediate overflow.
    /// Matches `modp`'s degenerate convention `p == 0 → 0`.
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

    proptest! {
        /// Main postcondition: for `p > 0`, `modp(n, p)` equals `2^n mod p`
        /// (captured by the u128 naive oracle).  Implies `modp(n, p) < p`.
        #[test]
        fn matches_oracle(n in 0u64..=200, p in 1u64..=(1u64 << 30)) {
            prop_assert_eq!(modp(n, p), naive(n, p));
        }

        /// Degenerate convention: `p == 0` yields `0` regardless of `n`.
        #[test]
        fn p_zero_yields_zero(n in 0u64..=200) {
            prop_assert_eq!(modp(n, 0), 0);
        }
    }
}
