//! Extracted from `byteorder` 1.5.0:
//! `impl ByteOrder for BigEndian { fn from_slice_u64(numbers: &mut [u64]) { .. } }`
//!
//! The receiver `BigEndian` is a zero-sized marker type, and the original
//! signature does not take `&self` (the trait method has no receiver). So the
//! free-function form drops nothing structural — we just lift the method body.

/// Converts the given slice of unsigned 64 bit integers to big endian.
///
/// If the host platform is already big endian, this is a no-op.
#[inline]
pub fn from_slice_u64(numbers: &mut [u64]) {
    if cfg!(target_endian = "little") {
        for n in numbers {
            *n = n.to_be();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from the doc-test on `ByteOrder::from_slice_u64` in
    // byteorder-1.5.0/src/lib.rs lines 1653-1659.
    #[test]
    fn doc_example_big_endian() {
        let mut numbers = [5, 65000];
        from_slice_u64(&mut numbers);
        assert_eq!(numbers, [5u64.to_be(), 65000u64.to_be()]);
    }
}
