// Monomorphic u64 version of `Integer::gcd` from num-integer 0.1.46
// (the unsigned-impl branch, src/lib.rs:870-895). Stein's binary
// algorithm: pull out common factors of 2 first, then iteratively
// subtract the smaller from the larger and divide out trailing zeros
// until both equal.
//
// Rewrites for Hax compatibility:
//   * `u64::trailing_zeros()` extracts to
//     `core_models.num.Impl_9.trailing_zeros`, which the Hax Lean
//     prelude does not model. Replaced with a primitive
//     shift-and-count helper `trailing_zeros_u64` (per the canonical
//     `u64_trailing_zeros_method.rs` archive pattern, mirroring
//     `proof_patterns/trailing_zeros_u64_modified`).
//   * The `while m != n { ... }` outer subtract-and-strip loop is
//     rewritten as tail recursion in `gcd_stein_loop`, per the
//     recursion-preference rule. The loop iterates at most ~64 times
//     on `u64` (each iteration either halves a value via
//     `>> trailing_zeros_u64(...)` or subtracts equals), well within
//     the ~10^5 safe recursion-depth rule-of-thumb. Both odd-invariant
//     and termination measure carry cleanly as recursion parameters.

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

fn gcd_stein_loop(m: u64, n: u64) -> u64 {
    if m == n {
        m
    } else if m > n {
        let d = m - n;
        gcd_stein_loop(d >> trailing_zeros_u64(d), n)
    } else {
        let d = n - m;
        gcd_stein_loop(m, d >> trailing_zeros_u64(d))
    }
}

pub fn gcd_stein(a: u64, b: u64) -> u64 {
    if a == 0 || b == 0 {
        return a | b;
    }

    // find common factors of 2
    let shift = trailing_zeros_u64(a | b);

    // divide n and m by 2 until odd
    let m = a >> trailing_zeros_u64(a);
    let n = b >> trailing_zeros_u64(b);

    gcd_stein_loop(m, n) << shift
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
