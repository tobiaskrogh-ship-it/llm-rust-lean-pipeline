/// HumanEval/97 / CLEVER 096 — `multiply(a, b)`.  Product of the decimal
/// unit digits of `|a|` and `|b|`.  Inputs are arbitrary integers (i64).
pub fn multiply(a: i64, b: i64) -> i64 {
    let aa = if a < 0 { -a } else { a };
    let bb = if b < 0 { -b } else { b };
    (aa % 10) * (bb % 10)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    // Concrete sanity checks, including edge cases that random sampling
    // is unlikely to hit (zero, multiples of ten, both signs).
    #[test]
    fn known() {
        assert_eq!(multiply(148, 412), 8 * 2);
        assert_eq!(multiply(-19, 28), 9 * 8);
        assert_eq!(multiply(0, 0), 0);
        assert_eq!(multiply(0, 7), 0);
        assert_eq!(multiply(10, 10), 0);
        assert_eq!(multiply(-10, 25), 0);
    }

    proptest! {
        // Main postcondition: `multiply(a, b)` equals the product of the
        // unit digits of `|a|` and `|b|`.  This is the entire functional
        // contract of `multiply`; every other property we might list
        // (boundedness `0 ≤ r ≤ 81`, sign-invariance, commutativity,
        // last-digit dependence) is an algebraic consequence of this
        // equation and is therefore intentionally omitted.
        //
        // Domain: full `i64` except `i64::MIN`.  Negating `i64::MIN`
        // overflows, so the function (and any oracle using `.abs()`)
        // panics there — that input is a precondition violation.
        #[test]
        fn matches_unit_digit_product(
            a in (i64::MIN + 1)..=i64::MAX,
            b in (i64::MIN + 1)..=i64::MAX,
        ) {
            let aa = a.abs();
            let bb = b.abs();
            prop_assert_eq!(multiply(a, b), (aa % 10) * (bb % 10));
        }
    }
}
