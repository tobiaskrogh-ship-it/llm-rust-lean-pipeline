/// HumanEval/75 / CLEVER 074 — `is_multiply_prime(a)`.  Return true iff
/// `a` is a product of exactly three primes (with repetition).
/// Examples: `8 = 2*2*2`, `30 = 2*3*5`, `12 = 2*2*3` → true;
/// `4 = 2*2`, `6 = 2*3`, `24 = 2*2*2*3` → false.
fn smallest_prime_at(m: u64, d: u64) -> u64 {
    if d * d > m {
        m
    } else if m % d == 0 {
        d
    } else {
        smallest_prime_at(m, d + 1)
    }
}

pub fn is_multiply_prime(a: u64) -> bool {
    if a < 8 {
        false
    } else {
        let p1 = smallest_prime_at(a, 2);
        let q1 = a / p1;
        if q1 < 2 {
            false
        } else {
            let p2 = smallest_prime_at(q1, 2);
            let q2 = q1 / p2;
            if q2 < 2 {
                false
            } else {
                let p3 = smallest_prime_at(q2, 2);
                p3 == q2
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn naive(n: u64) -> bool {
        if n < 2 { return false; }
        let mut m = n;
        let mut count = 0u64;
        let mut d = 2u64;
        while d * d <= m {
            while m % d == 0 {
                count += 1;
                m /= d;
                if count > 3 { return false; }
            }
            d += 1;
        }
        if m > 1 { count += 1; }
        count == 3
    }

    #[test]
    fn small_cases() {
        assert!(is_multiply_prime(8));     // 2*2*2
        assert!(is_multiply_prime(12));    // 2*2*3
        assert!(is_multiply_prime(27));    // 3*3*3
        assert!(is_multiply_prime(30));    // 2*3*5
        assert!(is_multiply_prime(105));   // 3*5*7
        assert!(!is_multiply_prime(1));
        assert!(!is_multiply_prime(2));
        assert!(!is_multiply_prime(4));
        assert!(!is_multiply_prime(6));
        assert!(!is_multiply_prime(7));
        assert!(!is_multiply_prime(24));
    }

    proptest! {
        #[test]
        fn matches_oracle(a in 1u64..=(1u64 << 18)) {
            prop_assert_eq!(is_multiply_prime(a), naive(a));
        }
    }
}
