/// HumanEval/150 / CLEVER 148 — `x_or_y(n, x, y)`.  Return `x` if `n` is
/// prime, else `y`.  Canonical CLEVER signature has a typo
/// (`int n: i64, int x: i64, int y: i64`); we interpret it as the
/// natural three-argument shape.  i64 to match canonical despite
/// non-negative spec for `n` (so we don't lose flexibility on x, y).
fn is_prime_at(n: i64, d: i64) -> bool {
    if d * d > n { true }
    else if n % d == 0 { false }
    else { is_prime_at(n, d + 1) }
}

fn is_prime(n: i64) -> bool {
    if n < 2 { false } else { is_prime_at(n, 2) }
}

pub fn x_or_y(n: i64, x: i64, y: i64) -> i64 {
    if is_prime(n) { x } else { y }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    // Trusted iterative reference for primality. Independent shape from the
    // recursive trial-division used by `is_prime` / `is_prime_at`, so a bug
    // shared between impl and reference is unlikely.
    fn ref_is_prime(n: i64) -> bool {
        if n < 2 {
            return false;
        }
        let mut d = 2i64;
        while d * d <= n {
            if n % d == 0 {
                return false;
            }
            d += 1;
        }
        true
    }

    #[test]
    fn known() {
        assert_eq!(x_or_y(7, 34, 12), 34);
        assert_eq!(x_or_y(15, 8, 5), 5);
        assert_eq!(x_or_y(2, 1, 0), 1);
        assert_eq!(x_or_y(1, 7, 9), 9);
    }

    // Edge-case unit tests pinning down the `n < 2` early-return branch of
    // `is_prime`. These values never reach `is_prime_at` in the impl, so
    // they exercise a code path distinct from the property tests below.
    #[test]
    fn n_below_two_returns_y() {
        assert_eq!(x_or_y(1, 100, 200), 200);
        assert_eq!(x_or_y(0, 100, 200), 200);
        assert_eq!(x_or_y(-1, 100, 200), 200);
        assert_eq!(x_or_y(-1_000, 100, 200), 200);
    }

    proptest! {
        // Postcondition (prime case): when `n` is prime, x_or_y returns x.
        // Range -100..=5_000 keeps the trial-division recursion shallow
        // (depth ~sqrt(n) ≤ 71) and avoids overflow in `d * d`.
        #[test]
        fn returns_x_when_n_is_prime(n in -100i64..=5_000, x: i64, y: i64) {
            if ref_is_prime(n) {
                prop_assert_eq!(x_or_y(n, x, y), x);
            }
        }

        // Postcondition (non-prime case): when `n` is not prime — including
        // n < 2, where the impl short-circuits — x_or_y returns y.
        // Independent of the prime case: a buggy impl that always returned x
        // would pass `returns_x_when_n_is_prime` but fail this.
        #[test]
        fn returns_y_when_n_is_not_prime(n in -100i64..=5_000, x: i64, y: i64) {
            if !ref_is_prime(n) {
                prop_assert_eq!(x_or_y(n, x, y), y);
            }
        }
    }
}
