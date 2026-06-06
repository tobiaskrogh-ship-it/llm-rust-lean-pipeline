/// HumanEval/53 — `add(x, y)`.  Return `x + y`.
///
/// Note: CLEVER's reference uses arbitrary-precision `int`.  Mapped to
/// `i64` here.  In debug builds the addition panics on overflow; in
/// release it wraps.  Both behaviours are faithful to the spec on the
/// non-overflowing domain that the property tests exercise.
pub fn add_two(x: i64, y: i64) -> i64 {
    x + y
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        /// Postcondition: result equals the mathematical sum.
        #[test]
        fn equals_mathematical_sum(
            x in -(1i64 << 31)..=(1i64 << 31),
            y in -(1i64 << 31)..=(1i64 << 31),
        ) {
            prop_assert_eq!(add_two(x, y), x + y);
        }

        /// Commutativity. A buggy implementation that did `x - y` would
        /// fail this on any `x != y`.
        #[test]
        fn commutative(
            x in -(1i64 << 31)..=(1i64 << 31),
            y in -(1i64 << 31)..=(1i64 << 31),
        ) {
            prop_assert_eq!(add_two(x, y), add_two(y, x));
        }

        /// Identity at zero on the left.
        #[test]
        fn zero_left_identity(x: i64) {
            prop_assert_eq!(add_two(0, x), x);
        }

        /// Identity at zero on the right.
        #[test]
        fn zero_right_identity(x: i64) {
            prop_assert_eq!(add_two(x, 0), x);
        }
    }
}
