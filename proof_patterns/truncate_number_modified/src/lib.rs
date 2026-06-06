/// Given a non-negative integer interpreted as a fixed-point number with
/// 3 fractional digits (so `1000` represents the float `1.0`), return the
/// fractional part — i.e. the value strictly less than `1000`.
///
/// Note: CLEVER's reference signature is `(number: float) -> float`,
/// returning `number - floor(number)`. Translated to a `u64` fixed-point
/// formulation because the Hax Lean prelude has gaps in `f64` support
/// (missing `Impl.abs`, `PartialOrd`, `Neg`, and a broken `Sub.sub` for
/// non-integer types). The body has no iteration, so no recursive form
/// applies — the function is a single arithmetic expression.
pub fn truncate_number(number: u64) -> u64 {
    number % 1000
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        /// Postcondition (bound): the returned fractional part is strictly
        /// less than 1000 — the "less than one whole unit" half of the
        /// fixed-point fractional-part contract.
        #[test]
        fn result_is_strictly_less_than_one_thousand(n in any::<u64>()) {
            prop_assert!(truncate_number(n) < 1000);
        }

        /// Postcondition (congruence): `number - result` is a multiple of
        /// 1000, i.e. the result agrees with `number` modulo 1000. This is
        /// the independent half of the contract — together with the bound
        /// above it uniquely pins down `number % 1000`. Phrased as
        /// `number == (number / 1000) * 1000 + result` to avoid relying on
        /// the same `%` operator the implementation uses.
        #[test]
        fn result_reconstructs_input_with_integer_quotient(n in any::<u64>()) {
            let r = truncate_number(n);
            prop_assert_eq!((n / 1000) * 1000 + r, n);
        }
    }
}
