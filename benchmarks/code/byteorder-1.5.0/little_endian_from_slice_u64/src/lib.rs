//! Extracted from `byteorder` 1.5.0:
//! `impl ByteOrder for LittleEndian { fn from_slice_u64(numbers: &mut [u64]) { .. } }`
//! at src/lib.rs:2262.
//!
//! `LittleEndian` is a zero-sized marker type in the source, so the `&self`
//! receiver is dropped here and the method is exposed as a free function.

#[inline]
pub fn from_slice_u64(numbers: &mut [u64]) {
    if cfg!(target_endian = "big") {
        for n in numbers {
            *n = n.to_le();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from the doc-test on the `ByteOrder::from_slice_u64`
    // trait method (src/lib.rs:1653-1659), monomorphized to the
    // `LittleEndian` impl: `BigEndian::from_slice_u64` -> local
    // `from_slice_u64`, and `to_be` -> `to_le`.
    #[test]
    fn doctest_little_endian() {
        let mut numbers = [5, 65000];
        from_slice_u64(&mut numbers);
        assert_eq!(numbers, [5u64.to_le(), 65000u64.to_le()]);
    }
}
