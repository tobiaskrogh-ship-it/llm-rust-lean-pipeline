pub fn gcd_while(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        // No `loop_invariant!`: the natural GCD invariant
        // `gcd(a, b) == gcd(a0, b0)` (or the equivalent residue invariant
        // `b == 0 || a % b == a0 % b0`) is unprovable at the Rust level —
        // Hax's pureP/grind synthesis cannot lift `%` (a partial op in
        // `RustM`) to a pure `Prop`. Termination on `b` is similarly not
        // expressible without entering `RustM`. The proof stage will
        // discharge both invariance and termination in Lean using
        // `Spec.MonoLoopCombinator.while_loop`.
        //
        // No `loop_decreases!` either: without `#[hax_lib::requires(...)]`
        // no auto-spec is generated, so a Rust-level decreases hint has
        // nothing to attach to.
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Boundary: `gcd(0, 0) = 0` by convention.
    #[test]
    fn zero_zero_is_zero() {
        assert_eq!(gcd_while(0, 0), 0);
    }

    /// Boundary: `gcd(a, 0) = a` and `gcd(0, b) = b`. The loop exits
    /// immediately when `b = 0` and returns `a`.
    #[test]
    fn zero_input_returns_other() {
        for x in 1u64..=20 {
            assert_eq!(gcd_while(x, 0), x);
            assert_eq!(gcd_while(0, x), x);
        }
    }

    /// Hand-computed reference values. Guards against the function returning
    /// *some* common divisor that isn't the greatest, and against off-by-one
    /// errors at the boundary `a == b`.
    #[test]
    fn known_values() {
        assert_eq!(gcd_while(12, 18), 6);
        assert_eq!(gcd_while(48, 18), 6);
        assert_eq!(gcd_while(17, 5), 1); // coprime
        assert_eq!(gcd_while(100, 75), 25);
        assert_eq!(gcd_while(7, 7), 7); // a == b
    }

    /// Postcondition (common divisor): the result divides both inputs.
    /// The single exception is `gcd(0, 0) = 0`; otherwise the result is
    /// positive and must divide both `a` and `b` exactly.
    #[test]
    fn result_divides_both_inputs() {
        for a in 0u64..=30 {
            for b in 0u64..=30 {
                let g = gcd_while(a, b);
                if g == 0 {
                    assert_eq!(a, 0);
                    assert_eq!(b, 0);
                } else {
                    assert_eq!(a % g, 0, "gcd_while({a}, {b}) = {g} does not divide a");
                    assert_eq!(b % g, 0, "gcd_while({a}, {b}) = {g} does not divide b");
                }
            }
        }
    }

    /// Postcondition (greatest): no integer larger than `gcd_while(a, b)`
    /// divides both `a` and `b`. Independent from `result_divides_both_inputs`
    /// — that test alone admits any common divisor; this one pins down the
    /// *greatest* part of the contract.
    #[test]
    fn result_is_greatest_common_divisor() {
        for a in 1u64..=30 {
            for b in 1u64..=30 {
                let g = gcd_while(a, b);
                for d in (g + 1)..=a.max(b) {
                    assert!(
                        !(a % d == 0 && b % d == 0),
                        "gcd_while({a}, {b}) = {g} but {d} also divides both"
                    );
                }
            }
        }
    }
}
