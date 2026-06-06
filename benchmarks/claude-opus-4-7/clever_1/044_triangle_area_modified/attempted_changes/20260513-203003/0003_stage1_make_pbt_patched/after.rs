/// Area of a triangle given base length `a` and height `h`.
/// Integer arithmetic — fractional results are truncated to floor.
pub fn triangle_area(a: i64, h: i64) -> i64 {
    a * h / 2
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        // Postcondition: when `a * h` does not overflow, `triangle_area(a, h)`
        // returns the truncated integer half of the product `a * h`.
        // This pins down the numerical contract of the function.
        // Inputs are bounded to 2^31 so the product always fits in i64.
        #[test]
        fn returns_truncated_half_of_product(
            a in -(1i64 << 31)..=(1i64 << 31),
            h in -(1i64 << 31)..=(1i64 << 31),
        ) {
            let product = a * h;
            prop_assert_eq!(triangle_area(a, h), product / 2);
        }

        // Failure condition: when `a * h` would overflow `i64`,
        // calling `triangle_area` panics (debug builds; `cargo test`
        // runs in debug mode by default).
        #[test]
        fn panics_when_product_overflows(a: i64, h: i64) {
            prop_assume!(a.checked_mul(h).is_none());
            let result = std::panic::catch_unwind(|| triangle_area(a, h));
            prop_assert!(result.is_err());
        }
    }
}
