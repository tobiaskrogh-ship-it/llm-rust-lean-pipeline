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
    #[test]
    fn known() {
        assert_eq!(multiply(148, 412), 8 * 2);
        assert_eq!(multiply(-19, 28), 9 * 8);
    }
    proptest! {
        #[test]
        fn matches(a in -(1i64<<30)..=(1i64<<30), b in -(1i64<<30)..=(1i64<<30)) {
            let aa = a.abs(); let bb = b.abs();
            prop_assert_eq!(multiply(a, b), (aa % 10) * (bb % 10));
        }
    }
}
