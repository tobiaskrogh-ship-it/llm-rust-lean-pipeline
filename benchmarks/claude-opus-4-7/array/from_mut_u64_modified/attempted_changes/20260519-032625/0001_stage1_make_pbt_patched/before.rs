//! Extracted from `core::array::from_mut` (src/array/mod.rs:174), monomorphized to `u64`.

/// Converts a mutable reference to `T` into a mutable reference to an array of length 1 (without copying).
pub const fn from_mut(s: &mut u64) -> &mut [u64; 1] {
    // SAFETY: Converting `&mut T` to `&mut [T; 1]` is sound.
    unsafe { &mut *(s as *mut u64).cast::<[u64; 1]>() }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from core's `tests/array.rs::array_from_mut`,
    // monomorphized to `u64`. The original mutated a `String` via
    // `push_str("!")`; the equivalent observable mutation for `u64`
    // is an in-place write through the returned array reference.
    #[test]
    fn array_from_mut() {
        let mut value: u64 = 10;
        let arr: &mut [u64; 1] = from_mut(&mut value);
        arr[0] += 1;
        assert_eq!(value, 11);
    }
}
