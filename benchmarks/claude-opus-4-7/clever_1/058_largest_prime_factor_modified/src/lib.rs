/// HumanEval/59 / CLEVER 058 — `largest_prime_factor(n)`.  Return the
/// largest prime factor of `n` (`n > 1`).  For `n ≤ 1` the function
/// returns `1` as a degenerate sentinel.
///
/// Strategy: repeatedly extract the smallest prime divisor and divide
/// it out fully.  When `n` reaches `1`, the last divisor extracted is
/// the largest prime factor.
fn smallest_divisor_at(m: u64, d: u64) -> u64 {
    if d * d > m {
        m
    } else if m % d == 0 {
        d
    } else {
        smallest_divisor_at(m, d + 1)
    }
}

fn strip_factor(n: u64, p: u64) -> u64 {
    if n % p == 0 {
        strip_factor(n / p, p)
    } else {
        n
    }
}

fn largest_prime_at(n: u64, current_largest: u64) -> u64 {
    if n <= 1 {
        current_largest
    } else {
        let p = smallest_divisor_at(n, 2);
        let stripped = strip_factor(n, p);
        largest_prime_at(stripped, p)
    }
}

pub fn largest_prime_factor(n: u64) -> u64 {
    if n <= 1 {
        1
    } else {
        largest_prime_at(n, 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Trial-division primality test, used as an independent oracle for
    /// the primality and "no larger prime divisor" contract clauses.
    fn is_prime_oracle(n: u64) -> bool {
        if n < 2 {
            return false;
        }
        if n == 2 {
            return true;
        }
        if n % 2 == 0 {
            return false;
        }
        let mut d = 3u64;
        while d * d <= n {
            if n % d == 0 {
                return false;
            }
            d += 2;
        }
        true
    }

    /// Precondition handling: for n ≤ 1 the function returns the
    /// degenerate sentinel `1`.
    #[test]
    fn degenerate_n_le_one() {
        assert_eq!(largest_prime_factor(0), 1);
        assert_eq!(largest_prime_factor(1), 1);
    }

    proptest! {
        /// Postcondition 1 (divisibility): for n > 1 the returned value
        /// divides n.
        #[test]
        fn result_divides_n(n in 2u64..=(1u64 << 18)) {
            let p = largest_prime_factor(n);
            prop_assert_eq!(n % p, 0);
        }

        /// Postcondition 2 (primality): for n > 1 the returned value is
        /// itself a prime number.
        #[test]
        fn result_is_prime(n in 2u64..=(1u64 << 18)) {
            let p = largest_prime_factor(n);
            prop_assert!(is_prime_oracle(p));
        }

        /// Postcondition 3 (maximality): for n > 1 no prime strictly
        /// greater than the returned value divides n.  This is the
        /// "largest" half of the contract — independent of the
        /// "divides" and "is prime" halves above (a buggy
        /// implementation could return *some* prime divisor without
        /// it being the maximum one).
        ///
        /// Range is capped because the inner loop is O(n).
        #[test]
        fn no_larger_prime_divides_n(n in 2u64..=2_000u64) {
            let p = largest_prime_factor(n);
            let mut q = p + 1;
            while q <= n {
                if is_prime_oracle(q) {
                    prop_assert!(n % q != 0,
                        "found a larger prime divisor: n={}, returned p={}, witness q={}",
                        n, p, q);
                }
                q += 1;
            }
        }
    }
}
