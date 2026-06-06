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

    fn naive(n: u64) -> u64 {
        if n <= 1 { return 1; }
        let mut m = n;
        let mut largest = 1u64;
        let mut d = 2u64;
        while d * d <= m {
            while m % d == 0 {
                largest = d;
                m /= d;
            }
            d += 1;
        }
        if m > 1 { largest = m; }
        largest
    }

    #[test]
    fn small_cases() {
        assert_eq!(largest_prime_factor(2), 2);
        assert_eq!(largest_prime_factor(3), 3);
        assert_eq!(largest_prime_factor(4), 2);
        assert_eq!(largest_prime_factor(12), 3);
        assert_eq!(largest_prime_factor(15), 5);
        assert_eq!(largest_prime_factor(100), 5);
        assert_eq!(largest_prime_factor(13195), 29);
    }

    proptest! {
        /// Bounded to keep recursion well inside test-thread stack.
        #[test]
        fn matches_oracle(n in 2u64..=(1u64 << 18)) {
            prop_assert_eq!(largest_prime_factor(n), naive(n));
        }

        #[test]
        fn divides_n(n in 2u64..=(1u64 << 18)) {
            let p = largest_prime_factor(n);
            prop_assert!(n % p == 0);
        }
    }
}
