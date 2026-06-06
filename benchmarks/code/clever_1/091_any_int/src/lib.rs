/// HumanEval/92 / CLEVER 091 — `any_int(a, b, c)`.  Return true iff one
/// of `a, b, c` equals the sum of the other two.  Inputs are integers;
/// `i64` allows negative inputs the spec mentions ("all numbers are integers").
pub fn any_int(a: i64, b: i64, c: i64) -> bool {
    a == b + c || b == a + c || c == a + b
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    #[test]
    fn known() {
        assert!(any_int(5, 2, 3));
        assert!(any_int(3, 2, 1));
        assert!(!any_int(3, 2, 2));
        assert!(any_int(-1, 1, 0));
    }
    proptest! {
        #[test]
        fn defining(a in -50i64..=50, b in -50i64..=50, c in -50i64..=50) {
            prop_assert_eq!(any_int(a, b, c), a == b + c || b == a + c || c == a + b);
        }
    }
}
