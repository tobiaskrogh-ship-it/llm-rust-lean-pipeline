// Monomorphic u64 version of `Integer::gcd` from num-integer 0.1.46
// (the unsigned-impl branch, src/lib.rs:870-895). Stein's binary
// algorithm: pull out common factors of 2 first, then iteratively
// subtract the smaller from the larger and divide out trailing zeros
// until both equal.
//
// Hax-compatibility rewrite:
// - `.trailing_zeros()` extracts to `core_models.num.Impl_9.trailing_zeros`,
//   which `lake build` reports as an unknown identifier. Replaced by
//   inline while-loops that strip the low zero bit one at a time.
// - Every `while` carries a `hax_lib::loop_decreases!` so the extracted
//   Lean uses a real termination measure (otherwise Hax fills in `0`,
//   making `rust_primitives.hax.while_loop.spec` unusable downstream).
pub fn gcd_stein(a: u64, b: u64) -> u64 {
    let mut m = a;
    let mut n = b;
    if m == 0 || n == 0 {
        return m | n;
    }

    // find common factors of 2: inline `(m | n).trailing_zeros()`.
    // `(m | n)` is non-zero here because both `m` and `n` are non-zero,
    // so the loop terminates with `t` odd.
    let mut t = m | n;
    let mut shift: u32 = 0;
    while t & 1 == 0 {
        hax_lib::loop_decreases!(t);
        t >>= 1;
        shift += 1;
    }

    // divide m by 2 until odd: inline `m >>= m.trailing_zeros()`.
    while m & 1 == 0 {
        hax_lib::loop_decreases!(m);
        m >>= 1;
    }

    // divide n by 2 until odd: inline `n >>= n.trailing_zeros()`.
    while n & 1 == 0 {
        hax_lib::loop_decreases!(n);
        n >>= 1;
    }

    while m != n {
        // Termination measure: at this point both `m` and `n` are odd
        // (the inner loops strip trailing zeros), so `m | n` is bounded
        // and strictly decreases each outer iteration. The larger of
        // `m`/`n` is reduced by subtraction and then shifted right at
        // least once (subtracting two odds yields an even, so at least
        // one trailing-zero strip happens), which retires bits of the
        // OR.
        // Bitwise OR is panic-free (unlike `m + n` whose u64 sum can
        // overflow — `grind` rejected that as not `_pureTermination`)
        // and contains no if/match (which `hax_construct_pure` rejects
        // with "mvcgen generated more than one goal containing the
        // metavariable").
        hax_lib::loop_decreases!(m | n);
        if m > n {
            m -= n;
            while m & 1 == 0 {
                hax_lib::loop_decreases!(m);
                m >>= 1;
            }
        } else {
            n -= m;
            while n & 1 == 0 {
                hax_lib::loop_decreases!(n);
                n >>= 1;
            }
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
    /// `result_divides_both_inputs`.
    #[test]
    fn result_is_greatest() {
        for a in 1u64..=30 {
            for b in 1u64..=30 {
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
