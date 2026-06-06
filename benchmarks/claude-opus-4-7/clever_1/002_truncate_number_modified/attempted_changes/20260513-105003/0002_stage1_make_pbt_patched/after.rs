/// Given a positive floating point number, return its decimal part
/// (the leftover after subtracting the largest integer smaller than it).
pub fn truncate_number(number: f64) -> f64 {
    number - number.floor()
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    // Strategy: positive, finite f64s within a range where f64 still has
    // sub-integer precision (above ~2^52 every f64 is already an integer,
    // which makes the contract trivially satisfied and uninteresting).
    fn positive_finite() -> impl Strategy<Value = f64> {
        // Exclude 0.0 (the precondition says "positive"), keep things finite
        // and below 2^52 so the fractional part is meaningful.
        1e-300f64..(1u64 << 52) as f64
    }

    proptest! {
        /// Postcondition (bounds): the result is always in `[0, 1)`.
        ///
        /// A buggy implementation that returned `number - number.ceil()`
        /// (a negative value) or `number.floor()` (>= 1 for number >= 1)
        /// would be caught here.
        #[test]
        fn result_is_in_unit_interval(number in positive_finite()) {
            let r = truncate_number(number);
            prop_assert!(r >= 0.0, "result {} is negative", r);
            prop_assert!(r < 1.0, "result {} is not below 1", r);
        }

        /// Postcondition (reconstruction): `number - result` is an integer,
        /// and equals `number.floor()`. Combined with the bounds test above
        /// this uniquely characterises the fractional part.
        ///
        /// A buggy implementation returning e.g. `number * 0.5` or
        /// `number - number.trunc() - 0.1` would be caught here.
        #[test]
        fn reconstructs_floor(number in positive_finite()) {
            let r = truncate_number(number);
            let recovered = number - r;
            prop_assert_eq!(recovered, number.floor());
            prop_assert_eq!(recovered.floor(), recovered); // integral
        }
    }
}
