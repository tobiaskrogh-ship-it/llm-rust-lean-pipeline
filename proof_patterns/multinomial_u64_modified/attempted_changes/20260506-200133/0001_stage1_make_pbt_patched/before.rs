//! Extracted from `num-integer` 0.1.46 (`num_integer::multinomial`),
//! monomorphized to `u64`.
//!
//! The function depends on `binomial`, which depends on `multiply_and_divide`,
//! which depends on `gcd`. All four are inlined here as private helpers,
//! monomorphized to `u64`.

/// Calculates the Greatest Common Divisor (GCD) of two `u64` values, using
/// Stein's binary algorithm. Inlined from
/// `<u64 as Integer>::gcd` (via the `impl_integer_for_usize!` macro).
fn gcd(x: u64, y: u64) -> u64 {
    let mut m = x;
    let mut n = y;
    if m == 0 || n == 0 {
        return m | n;
    }

    // find common factors of 2
    let shift = (m | n).trailing_zeros();

    // divide n and m by 2 until odd
    m >>= m.trailing_zeros();
    n >>= n.trailing_zeros();

    while m != n {
        if m > n {
            m -= n;
            m >>= m.trailing_zeros();
        } else {
            n -= m;
            n >>= n.trailing_zeros();
        }
    }
    m << shift
}

/// Calculate `r * a / b`, avoiding overflows and fractions.
///
/// Assumes that `b` divides `r * a` evenly.
fn multiply_and_divide(r: u64, a: u64, b: u64) -> u64 {
    let g = gcd(r, b);
    r / g * (a / (b / g))
}

/// Calculate the binomial coefficient.
fn binomial(mut n: u64, k: u64) -> u64 {
    if k > n {
        return 0;
    }
    if k > n - k {
        return binomial(n, n - k);
    }
    let mut r: u64 = 1;
    let mut d: u64 = 1;
    loop {
        if d > k {
            break;
        }
        r = multiply_and_divide(r, n, d);
        n -= 1;
        d += 1;
    }
    r
}

/// Calculate the multinomial coefficient.
pub fn multinomial(k: &[u64]) -> u64 {
    let mut r: u64 = 1;
    let mut p: u64 = 0;
    for i in k {
        p = p + *i;
        r = r * binomial(p, *i);
    }
    r
}

#[cfg(test)]
mod tests {
    use super::{binomial, multinomial};

    #[test]
    fn test_multinomial() {
        macro_rules! check_binomial {
            ($t:ty, $k:expr) => {{
                let n: $t = $k.iter().fold(0, |acc, &x| acc + x);
                let k: &[$t] = $k;
                assert_eq!(k.len(), 2);
                assert_eq!(multinomial(k), binomial(n, k[0]));
            }};
        }

        check_binomial!(u64, &[2, 98]);
        check_binomial!(u64, &[11, 24]);
        check_binomial!(u64, &[4, 10]);

        macro_rules! check_multinomial {
            ($t:ty, $k:expr, $r:expr) => {{
                let k: &[$t] = $k;
                let expected: $t = $r;
                assert_eq!(multinomial(k), expected);
            }};
        }

        check_multinomial!(u64, &[2, 1, 2], 30);
        check_multinomial!(u64, &[2, 3, 0], 10);

        check_multinomial!(u64, &[], 1);
        check_multinomial!(u64, &[0], 1);
        check_multinomial!(u64, &[12345], 1);
    }
}
