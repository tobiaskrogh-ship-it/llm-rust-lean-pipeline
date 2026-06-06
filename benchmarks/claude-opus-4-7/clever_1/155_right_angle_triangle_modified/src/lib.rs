/// HumanEval/157 / CLEVER 155 — `right_angle_triangle(a, b, c)`.
/// Return true iff one of the three squared-side equations holds:
/// `a² + b² == c²`, `a² + c² == b²`, or `b² + c² == a²`.
pub fn right_angle_triangle(a: u64, b: u64, c: u64) -> bool {
    let a2 = a * a;
    let b2 = b * b;
    let c2 = c * c;
    // Use `if`/`else` rather than `||` chained over the three additions:
    // Hax's `do`-block extraction is eager and evaluates every `←` bind
    // (including `a2 +? c2` and `b2 +? c2`) before the `||?` combinator,
    // so the extracted Lean diverges (`RustM.fail .integerOverflow`) on
    // inputs where the first disjunct is true but a later addition
    // overflows — e.g. `(a, b, c) = (2^32 - 1, 0, 2^32 - 1)`:
    // `a² + b² == c²` holds, but `a² + c² = 2·(2^32 - 1)²` overflows u64.
    // Rust short-circuits and returns `true` there; the rewrite preserves
    // that through extraction. See
    // `rewrite_patterns/short_circuit_and_with_partial_op.rs`.
    if a2 + b2 == c2 {
        true
    } else if a2 + c2 == b2 {
        true
    } else {
        b2 + c2 == a2
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn known() {
        assert!(right_angle_triangle(3, 4, 5));
        assert!(right_angle_triangle(5, 12, 13));
        assert!(right_angle_triangle(13, 5, 12));     // any permutation
        assert!(!right_angle_triangle(1, 2, 3));
        assert!(!right_angle_triangle(2, 2, 2));
    }

    proptest! {
        /// Contract: the predicate is symmetric in its three arguments.
        /// The three disjuncts of the formula cover the three cyclic
        /// orderings, so the result must depend only on the multiset
        /// `{a, b, c}` — every permutation gives the same answer.
        /// Bounds keep `a² + b²` well within `u64::MAX`.
        #[test]
        fn permutation_invariant(
            a in 0u64..1_000_000_000,
            b in 0u64..1_000_000_000,
            c in 0u64..1_000_000_000,
        ) {
            let r = right_angle_triangle(a, b, c);
            prop_assert_eq!(r, right_angle_triangle(a, c, b));
            prop_assert_eq!(r, right_angle_triangle(b, a, c));
            prop_assert_eq!(r, right_angle_triangle(b, c, a));
            prop_assert_eq!(r, right_angle_triangle(c, a, b));
            prop_assert_eq!(r, right_angle_triangle(c, b, a));
        }

        /// Contract (postcondition, positive direction): any Pythagorean
        /// triple must be recognised. Euclid's formula generates one for
        /// every pair `m > n ≥ 1`: `(m² − n², 2mn, m² + n²)`. Small bounds
        /// keep `m² + n²` and its square well below `u64::MAX`.
        #[test]
        fn euclid_generated_triples_recognised(
            m in 2u64..30_000,
            n in 1u64..30_000,
        ) {
            prop_assume!(m > n);
            let a = m * m - n * n;
            let b = 2 * m * n;
            let c = m * m + n * n;
            prop_assert!(right_angle_triangle(a, b, c));
        }

        /// Contract (postcondition, negative direction): an equilateral
        /// triangle with a positive side is never right. `2a² == a²` only
        /// when `a == 0`, so this pins down the constant on the right-hand
        /// side of the equation and would catch implementations that, for
        /// example, used `==` against `2·c²` or similar.
        #[test]
        fn equilateral_positive_is_not_right(a in 1u64..1_000_000_000) {
            prop_assert!(!right_angle_triangle(a, a, a));
        }

        /// Contract (boundary): a side of length zero makes the formula
        /// reduce to `n² == n²`, so the function returns `true` for
        /// `(0, n, n)` and its permutations. This pins down behaviour at
        /// the lower edge of the input domain (and would catch an
        /// implementation that special-cased zero to reject it).
        #[test]
        fn zero_side_with_equal_others_is_right(n in 0u64..1_000_000_000) {
            prop_assert!(right_angle_triangle(0, n, n));
            prop_assert!(right_angle_triangle(n, 0, n));
            prop_assert!(right_angle_triangle(n, n, 0));
        }
    }

    /// Contract (failure mode): the function performs unchecked `u64`
    /// multiplication, so sufficiently large inputs overflow and — in
    /// debug builds — panic. This documents that the implicit
    /// precondition `a*a, b*b, c*c, a²+b², …` must all fit in `u64`.
    #[test]
    #[should_panic]
    fn overflow_panics_in_debug() {
        // u64::MAX squared overflows immediately on `a * a`.
        let _ = right_angle_triangle(u64::MAX, 1, 1);
    }
}
