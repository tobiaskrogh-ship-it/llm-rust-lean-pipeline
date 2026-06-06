/// HumanEval/53 — `add(x, y)`.  Return `x + y`.
///
/// Note: CLEVER's reference uses arbitrary-precision `int`.  Mapped to
/// `i64` here.  In debug builds the addition panics on overflow; in
/// release it wraps.  Both behaviours are faithful to the spec on the
/// non-overflowing domain that the property tests exercise.
pub fn add(x: i64, y: i64) -> i64 {
    x + y
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        /// Postcondition: on inputs whose sum fits in `i64`, the result
        /// equals the mathematical sum `x + y`.
        ///
        /// This is the entire contract of `add`.  Range is chosen so
        /// that `x + y` cannot overflow `i64`, matching the "non-overflowing
        /// domain" the doc comment exercises.  Any implementation that
        /// returns a wrong value on any sampled input — including obvious
        /// buggy variants like `x - y`, `x * y`, `x ^ y`, or off-by-one
        /// shifts — fails this test.
        ///
        /// Derived algebraic facts (commutativity, associativity,
        /// left/right zero identity, monotonicity in either argument)
        /// follow from this postcondition together with standard
        /// properties of integer addition, so they are intentionally
        /// not asserted separately.
        #[test]
        fn equals_mathematical_sum(
            x in -(1i64 << 31)..=(1i64 << 31),
            y in -(1i64 << 31)..=(1i64 << 31),
        ) {
            prop_assert_eq!(add(x, y), x + y);
        }
    }
}
