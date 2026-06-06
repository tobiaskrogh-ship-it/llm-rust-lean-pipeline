/// Return the list of prime factors of n in non-decreasing order,
/// repeated by multiplicity. (n ≥ 2; for n ≤ 1 returns an empty list.)
fn factorize_at(n: i64, p: i64, mut acc: Vec<i64>) -> Vec<i64> {
    if n <= 1 {
        acc
    } else if p * p > n {
        acc.push(n);
        acc
    } else if n % p == 0 {
        acc.push(p);
        factorize_at(n / p, p, acc)
    } else {
        factorize_at(n, p + 1, acc)
    }
}

pub fn factorize(n: i64) -> Vec<i64> {
    if n <= 1 {
        Vec::new()
    } else {
        factorize_at(n, 2, Vec::new())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Reference primality check by trial division. Used only to validate
    /// the elements returned by `factorize`.
    fn is_prime(x: i64) -> bool {
        if x < 2 {
            return false;
        }
        if x == 2 {
            return true;
        }
        if x % 2 == 0 {
            return false;
        }
        let mut i: i64 = 3;
        while i.saturating_mul(i) <= x {
            if x % i == 0 {
                return false;
            }
            i += 2;
        }
        true
    }

    /// Contract (failure / edge case): for any `n <= 1`, `factorize` returns
    /// an empty vector. This pins down the documented behaviour on the
    /// "no factorization" side of the precondition.
    #[test]
    fn empty_for_n_le_one() {
        for n in -5i64..=1 {
            assert!(
                factorize(n).is_empty(),
                "factorize({}) should be empty",
                n
            );
        }
    }

    proptest! {
        /// Postcondition (1/3): the product of the returned factors equals `n`.
        /// Independent of the other two claims — e.g. returning `[2, 3]` for
        /// `n = 12` would satisfy primality and ordering but fail this test.
        #[test]
        fn product_of_factors_equals_n(n in 2i64..1_000_000) {
            let factors = factorize(n);
            let product: i64 = factors.iter().product();
            prop_assert_eq!(product, n);
        }

        /// Postcondition (2/3): every returned factor is prime.
        /// Independent — e.g. returning `[1, n]` would satisfy product = n
        /// and ordering but fail primality.
        #[test]
        fn every_factor_is_prime(n in 2i64..1_000_000) {
            let factors = factorize(n);
            for f in &factors {
                prop_assert!(is_prime(*f), "factor {} of {} is not prime", f, n);
            }
        }

        /// Postcondition (3/3): factors are returned in non-decreasing order.
        /// Independent — e.g. returning `[3, 2]` for `n = 6` would satisfy
        /// product = n and primality but fail ordering.
        #[test]
        fn factors_non_decreasing(n in 2i64..1_000_000) {
            let factors = factorize(n);
            for w in factors.windows(2) {
                prop_assert!(w[0] <= w[1], "factors not sorted for n={}: {:?}", n, factors);
            }
        }
    }
}
