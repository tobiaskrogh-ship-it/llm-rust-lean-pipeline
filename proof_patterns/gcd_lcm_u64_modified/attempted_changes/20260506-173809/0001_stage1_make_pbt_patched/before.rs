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

// Inlined from the `Integer for u64` impl at src/lib.rs:870-895
// (Stein's binary GCD algorithm).
fn gcd(x: u64, y: u64) -> u64 {
    // Use Stein's algorithm
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
}
