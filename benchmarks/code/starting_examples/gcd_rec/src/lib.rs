pub fn gcd_rec(a: u64, b: u64) -> u64 {
    if b == 0 {
        a
    } else {
        gcd_rec(b, a % b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Boundary: `gcd(0, 0) = 0` by convention.
    #[test]
    fn zero_zero_is_zero() {
        assert_eq!(gcd_rec(0, 0), 0);
    }

    /// Boundary: `gcd(a, 0) = a` and `gcd(0, b) = b`. Anchors the recursion.
    #[test]
    fn zero_input_returns_other() {
        for x in 1u64..=20 {
            assert_eq!(gcd_rec(x, 0), x);
            assert_eq!(gcd_rec(0, x), x);
        }
    }

    /// Hand-computed reference values. Guards against the function returning
    /// *some* common divisor that isn't the greatest, and against off-by-one
    /// errors at the boundary `a == b`.
    #[test]
    fn known_values() {
        assert_eq!(gcd_rec(12, 18), 6);
        assert_eq!(gcd_rec(48, 18), 6);
        assert_eq!(gcd_rec(17, 5), 1); // coprime
        assert_eq!(gcd_rec(100, 75), 25);
        assert_eq!(gcd_rec(7, 7), 7); // a == b
    }

    /// Postcondition (common divisor): the result divides both inputs.
    /// The single exception is `gcd(0, 0) = 0`; otherwise the result is
    /// positive and must divide both `a` and `b` exactly.
    #[test]
    fn result_divides_both_inputs() {
        for a in 0u64..=30 {
            for b in 0u64..=30 {
                let g = gcd_rec(a, b);
                if g == 0 {
                    assert_eq!(a, 0);
                    assert_eq!(b, 0);
                } else {
                    assert_eq!(a % g, 0, "gcd_rec({a}, {b}) = {g} does not divide a");
                    assert_eq!(b % g, 0, "gcd_rec({a}, {b}) = {g} does not divide b");
                }
            }
        }
    }

    /// Postcondition (greatest): no integer larger than `gcd_rec(a, b)` divides
    /// both `a` and `b`. This is the property a buggy implementation returning
    /// merely *some* common divisor (e.g. always 1) would fail. Independent
    /// from `result_divides_both_inputs` — that test alone admits any common
    /// divisor; this one pins down the *greatest* part of the contract.
    #[test]
    fn result_is_greatest_common_divisor() {
        for a in 1u64..=30 {
            for b in 1u64..=30 {
                let g = gcd_rec(a, b);
                for d in (g + 1)..=a.max(b) {
                    assert!(
                        !(a % d == 0 && b % d == 0),
                        "gcd_rec({a}, {b}) = {g} but {d} also divides both"
                    );
                }
            }
        }
    }
}
