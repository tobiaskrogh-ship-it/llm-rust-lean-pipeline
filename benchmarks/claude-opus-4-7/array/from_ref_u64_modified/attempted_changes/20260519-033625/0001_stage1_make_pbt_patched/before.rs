//! Extracted from `core::array::from_ref` (src/array/mod.rs:166), monomorphized to `u64`.

/// Converts a reference to `T` into a reference to an array of length 1 (without copying).
pub const fn from_ref(s: &u64) -> &[u64; 1] {
    // SAFETY: Converting `&T` to `&[T; 1]` is sound.
    unsafe { &*(s as *const u64).cast::<[u64; 1]>() }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from core's `tests/array.rs::array_from_ref`,
    // monomorphized to `u64` (the original used `String`/`&str`).
    #[test]
    fn array_from_ref() {
        let value: u64 = 42;
        let arr: &[u64; 1] = from_ref(&value);
        assert_eq!(&[value], arr);

        const VALUE: &u64 = &123;
        const ARR: &[u64; 1] = from_ref(VALUE);
        assert_eq!(&[*VALUE], ARR);
        assert!(core::ptr::eq(VALUE, &ARR[0]));
    }
}
