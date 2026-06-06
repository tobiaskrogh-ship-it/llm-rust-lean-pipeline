// Monomorphic u64 version of `num_integer::gcd_lcm` from num-integer 0.1.46.
//
// Source: src/lib.rs:432-434 dispatches `pub fn gcd_lcm<T: Integer>(x: T, y: T) -> (T, T)`
// to the trait method, which for unsigned integers is implemented at
// src/lib.rs:918-925:
//
//     fn gcd_lcm(&self, other: &Self) -> (Self, Self) {
//         if self.is_zero() && other.is_zero() {
//             return (Self::zero(), Self::zero());
//         }
//         let gcd = self.gcd(other);
//         let lcm = *self * (*other / gcd);
//         (gcd, lcm)
//     }
//
// The Stein's-algorithm `gcd` it calls is at src/lib.rs:868-895; it's
// inlined here as a private helper so this crate has no external deps.
//
// The free function and the trait method body are merged into one
// concrete `gcd_lcm: (u64, u64) -> (u64, u64)`.

pub fn gcd_lcm(x: u64, y: u64) -> (u64, u64) {
    if x == 0 && y == 0 {
        return (0, 0);
    }
    let g = gcd(x, y);
    let l = x * (y / g);
    (g, l)
}

// Inlined replacement for `u64::trailing_zeros`. The intrinsic method has no
// model in the Hax Lean prelude (extraction emits an unresolved reference to
// `core_models.num.Impl_9.trailing_zeros`); a shift-and-count `while` loop
// over primitive bitwise ops does have a model. See archive pattern
// `rewrite_patterns/u64_trailing_zeros_method.rs`.
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

// Inlined from the `Integer for u64` impl at src/lib.rs:870-895
// (Stein's binary GCD algorithm). The four `.trailing_zeros()` calls
// in the source have been replaced with `trailing_zeros_u64(...)`
// to dodge the missing Hax model; semantics are preserved.
fn gcd(x: u64, y: u64) -> u64 {
    // Use Stein's algorithm
    let mut m = x;
    let mut n = y;
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
    // Tests transferred from num-integer 0.1.46:
    //   - the `gcd_lcm` doc-test on the `Integer` trait (src/lib.rs:130-136),
    //   - `test_gcd_lcm` from the `impl_integer_for_usize!` macro at
    //     src/lib.rs:1010-1017.
    // `i.gcd_lcm(&j)` is rewritten to `gcd_lcm(i, j)`. In the original
    // unsigned impl, `i.lcm(&j)` is `i.gcd_lcm(&j).1`, so the second
    // tuple component of the comparison is tautological once gcd_lcm
    // is the system under test; the meaningful check is that the gcd
    // component agrees with the standalone Stein's-algorithm gcd.
    use super::*;

    #[test]
    fn test_gcd_lcm_doc() {
        assert_eq!(gcd_lcm(10, 4), (2, 20));
        assert_eq!(gcd_lcm(8, 9), (1, 72));
    }

    #[test]
    fn test_gcd_lcm() {
        for i in 0..256u64 {
            for j in 0..256u64 {
                let lcm_ij = gcd_lcm(i, j).1;
                assert_eq!(gcd_lcm(i, j), (gcd(i, j), lcm_ij));
            }
        }
    }

    // ---------------------------------------------------------------------
    // Property-based tests pinning down the gcd_lcm contract.
    //
    // Contract recap:
    //   * Postcondition (gcd half): the first component of the result is
    //     the *greatest* common divisor of x and y, with gcd_lcm(0, 0)
    //     special-cased to (0, 0).
    //   * Postcondition (lcm half): the second component is the least
    //     common multiple, equivalently determined by g * l = x * y when
    //     g is the true gcd; lcm(_, 0) = lcm(0, _) = 0.
    //   * Failure condition: panics on overflow when lcm(x, y) > u64::MAX
    //     (debug mode) — input ranges below stay well inside u64.
    //
    // Properties tested:
    //   - `gcd_is_a_common_divisor`         : g | x and g | y.
    //   - `gcd_is_the_greatest_common_divisor` : every common divisor
    //                                            divides g (independent
    //                                            of the divisibility claim
    //                                            above — a buggy impl
    //                                            returning 1 would still
    //                                            divide both inputs).
    //   - `gcd_times_lcm_equals_x_times_y`  : algebraic identity that,
    //                                          combined with the gcd
    //                                          properties, uniquely fixes
    //                                          the lcm value.
    //   - `zero_input_edge_cases`           : the three zero-input cases
    //                                          ((0,0), (x,0), (0,y)).
    //
    // Properties intentionally not tested (derivable, hence redundant):
    //   - `x | lcm` and `y | lcm` (follow from g | x, g | y, and
    //     g * l = x * y, because then l = (x/g) * y = x * (y/g)).
    //   - `lcm` is the *least* common multiple (follows from g being
    //     the greatest common divisor together with g * l = x * y).
    //   - Symmetry gcd_lcm(x, y) == gcd_lcm(y, x) (follows from gcd
    //     and lcm being uniquely characterised by their definitions).
    //   - Idempotence gcd_lcm(x, x) == (x, x) (likewise derived).
    //   - `gcd_lcm(1, y) == (1, y)` and similar identity-style facts.

    // Postcondition: the gcd component divides both inputs (when not
    // both are zero, in which case the contract pins gcd = 0).
    #[test]
    fn gcd_is_a_common_divisor() {
        for x in 0..128u64 {
            for y in 0..128u64 {
                let (g, _) = gcd_lcm(x, y);
                if x == 0 && y == 0 {
                    assert_eq!(g, 0);
                } else {
                    assert!(g >= 1, "gcd_lcm({x},{y}).0 = {g} should be >= 1");
                    assert_eq!(x % g, 0, "gcd_lcm({x},{y}).0 = {g} does not divide {x}");
                    assert_eq!(y % g, 0, "gcd_lcm({x},{y}).0 = {g} does not divide {y}");
                }
            }
        }
    }

    // Postcondition: the gcd component is the *greatest* common divisor.
    // Independent from the divisibility claim — a wrong impl returning a
    // smaller common divisor (e.g. always 1 for coprime-looking inputs)
    // would pass `gcd_is_a_common_divisor` but fail this test.
    #[test]
    fn gcd_is_the_greatest_common_divisor() {
        for x in 1..64u64 {
            for y in 1..64u64 {
                let (g, _) = gcd_lcm(x, y);
                for d in 1..=x.min(y) {
                    if x % d == 0 && y % d == 0 {
                        assert_eq!(
                            g % d,
                            0,
                            "{d} is a common divisor of {x} and {y} but does not divide gcd = {g}"
                        );
                    }
                }
            }
        }
    }

    // Postcondition: gcd * lcm == x * y. Together with the "greatest"
    // property above, this uniquely determines the lcm component for
    // every input (the (0, 0) case satisfies the identity trivially and
    // is additionally pinned by `zero_input_edge_cases`). Input range
    // chosen so x * y stays inside u64 (no overflow possible here).
    #[test]
    fn gcd_times_lcm_equals_x_times_y() {
        for x in 0..128u64 {
            for y in 0..128u64 {
                let (g, l) = gcd_lcm(x, y);
                assert_eq!(g * l, x * y, "gcd_lcm({x},{y}) = ({g},{l}); g*l != x*y");
            }
        }
    }

    // Postcondition: zero-input edge cases.
    //   gcd_lcm(0, 0) = (0, 0)   [explicit special case in source]
    //   gcd_lcm(x, 0) = (x, 0)   [generic branch: gcd(x,0) = x, lcm = 0]
    //   gcd_lcm(0, y) = (y, 0)   [generic branch: gcd(0,y) = y, lcm = 0]
    #[test]
    fn zero_input_edge_cases() {
        assert_eq!(gcd_lcm(0, 0), (0, 0));
        for x in 1..256u64 {
            assert_eq!(gcd_lcm(x, 0), (x, 0));
            assert_eq!(gcd_lcm(0, x), (x, 0));
        }
    }
}
