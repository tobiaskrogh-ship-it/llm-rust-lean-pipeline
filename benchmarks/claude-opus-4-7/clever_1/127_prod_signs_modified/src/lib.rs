/// HumanEval/128 / CLEVER 127 — `prod_signs(arr)`.  Return `sum(|v|) *
/// product(sgn(v))` where `sgn(0) = 0`, `sgn(>0) = 1`, `sgn(<0) = -1`.
/// Return `None` for empty input.
fn run_at(arr: &[i64], i: usize, sum_abs: i64, sign: i64) -> i64 {
    if i >= arr.len() { sum_abs * sign }
    else {
        let v = arr[i];
        let av = if v < 0 { -v } else { v };
        let s = if v == 0 { 0 } else if v > 0 { 1 } else { -1 };
        run_at(arr, i + 1, sum_abs + av, sign * s)
    }
}

pub fn prod_signs(arr: &[i64]) -> Option<i64> {
    if arr.is_empty() { None } else { Some(run_at(arr, 0, 0, 1)) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn known() {
        assert_eq!(prod_signs(&[]), None);
        assert_eq!(prod_signs(&[1, 2, 2, -4]), Some(-9));    // (1+2+2+4)*-1
        assert_eq!(prod_signs(&[0, 1]), Some(0));            // 0 zeroes the sign
        assert_eq!(prod_signs(&[1, 1, 1]), Some(3));
    }

    proptest! {
        /// Failure clause: the function returns `None` exactly on empty input.
        /// (We don't randomize this; the failure condition is a single fact.)
        #[test]
        fn empty_input_returns_none(_seed in any::<u8>()) {
            prop_assert_eq!(prod_signs(&[]), None);
        }

        /// Postcondition: on any non-empty input, the result equals
        /// `sum(|v|) * product(sgn(v))` computed by an independent reference.
        /// This is the entire spec for non-empty inputs, so a single property
        /// suffices: it catches wrong magnitude, wrong sign, off-by-one in
        /// the recursion, swapped accumulators, or a wrong initial sign.
        ///
        /// Values are kept in [-50, 50] with length <= 15 so that
        /// `sum_abs <= 750` and the product fits in i64 without overflow
        /// (and we never hit `i64::MIN`, where negation would overflow).
        #[test]
        fn matches_spec_formula(arr in prop::collection::vec(-50i64..=50, 1..=15)) {
            let sum_abs: i64 = arr.iter().map(|v| v.abs()).sum();
            let sign_product: i64 = arr.iter().map(|v| v.signum()).product();
            let expected = sum_abs * sign_product;
            prop_assert_eq!(prod_signs(&arr), Some(expected));
        }
    }
}
