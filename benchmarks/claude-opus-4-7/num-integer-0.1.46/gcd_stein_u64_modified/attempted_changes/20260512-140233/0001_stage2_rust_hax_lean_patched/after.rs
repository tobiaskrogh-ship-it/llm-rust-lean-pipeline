// Hax-compatible reimplementation of `u64::trailing_zeros` via a shift-
// and-count `while` loop. The stdlib method extracts to a missing
// identifier (`core_models.num.Impl_9.trailing_zeros`) in the Hax Lean
// prelude; see rewrite_patterns/u64_trailing_zeros_method.rs.
fn trailing_zeros_u64(x: u64) -> u32 {
    if x == 0 {
        return 64;
    }
    let mut y = x;
    let mut count: u32 = 0;
    while y & 1 == 0 {
        y >>= 1;
        count = count + 1;
    }
    count
}

// Monomorphic u64 version of `Integer::gcd` from num-integer 0.1.46
// (the unsigned-impl branch, src/lib.rs:870-895). Stein's binary
// algorithm: pull out common factors of 2 first, then iteratively
// subtract the smaller from the larger and divide out trailing zeros
// until both equal.
pub fn gcd_stein(a: u64, b: u64) -> u64 {
    let mut m = a;
    let mut n = b;
    if m == 0 || n == 0 {
        return m | n;
    }

    // find common factors of 2
    let shift = trailing_zeros_u64(m | n);

    // divide n and m by 2 until odd
    m >>= trailing_zeros_u64(m);
    n >>= trailing_zeros_u64(n);

    while m != n {
        if m > n {
            m -= n;
            m >>= trailing_zeros_u64(m);
        } else {
            n -= m;
            n >>= trailing_zeros_u64(n);
        }
    }
    m << shift
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Hand-computed values from num-integer's own test_gcd
    /// (src/lib.rs:974-981, monomorphized to u64).
    #[test]
    fn known_values() {
        assert_eq!(gcd_stein(10, 2), 2);
        assert_eq!(gcd_stein(10, 3), 1);
        assert_eq!(gcd_stein(0, 3), 3);
        assert_eq!(gcd_stein(3, 3), 3);
        assert_eq!(gcd_stein(56, 42), 14);
    }

    /// Boundary: gcd(0, 0) = 0 by convention (the source's `m | n`
    /// shortcut returns 0).
    #[test]
    fn zero_zero_is_zero() {
        assert_eq!(gcd_stein(0, 0), 0);
    }

    /// Postcondition (common divisor): the result divides both inputs.
    #[test]
    fn result_divides_both_inputs() {
        for a in 0u64..=30 {
            for b in 0u64..=30 {
                let g = gcd_stein(a, b);
                if g == 0 {
                    assert_eq!(a, 0);
                    assert_eq!(b, 0);
                } else {
                    assert_eq!(a % g, 0, "gcd_stein({a}, {b}) = {g} does not divide a");
                    assert_eq!(b % g, 0, "gcd_stein({a}, {b}) = {g} does not divide b");
                }
            }
        }
    }

    /// Postcondition (greatest): no integer larger than the result
    /// divides both inputs. Independent contract claim from
    /// `result_divides_both_inputs`. Range starts at 0 so the
    /// zero-shortcut path (`gcd_stein(0, n) = n` for n > 0) is also
    /// pinned down: combined with `result_divides_both_inputs` (which
    /// forces g | n, so g <= n) the greatest test forces g = n.
    #[test]
    fn result_is_greatest() {
        for a in 0u64..=30 {
            for b in 0u64..=30 {
                let g = gcd_stein(a, b);
                for d in (g + 1)..=a.max(b) {
                    assert!(
                        !(a % d == 0 && b % d == 0),
                        "gcd_stein({a}, {b}) = {g} but {d} also divides both"
                    );
                }
            }
        }
    }
}
