//! Extracted from `byteorder` 1.5.0 — `LittleEndian::write_u64_into`.
//!
//! This function writes a slice of `u64` values into a destination byte
//! slice using little-endian encoding. Its body is the inlined expansion
//! of the `write_slice!` macro from the source crate, specialized to
//! `u64` / `to_le_bytes`.
//!
//! `LittleEndian` is a zero-sized marker type in the source crate, so the
//! receiver has been dropped and the function is exposed as a free `pub fn`.

/// Writes unsigned 64 bit integers from `src` into `dst` in little-endian
/// order.
///
/// # Panics
///
/// Panics when `dst.len() != 8 * src.len()`.
pub fn write_u64_into(src: &[u64], dst: &mut [u8]) {
    const SIZE: usize = core::mem::size_of::<u64>();
    // Check types:
    let src: &[u64] = src;
    let dst: &mut [u8] = dst;
    assert_eq!(src.len() * SIZE, dst.len());
    for (src, dst) in src.iter().zip(dst.chunks_exact_mut(SIZE)) {
        dst.copy_from_slice(&src.to_le_bytes());
    }
}

#[cfg(test)]
mod tests {
    use super::write_u64_into;

    // Transferred from the doc-test of `ByteOrder::write_u64_into`
    // (src/lib.rs around line 1365 in the source crate). The original used
    // `LittleEndian::read_u64_into` to round-trip the data; here we
    // decode each 8-byte chunk inline via `u64::from_le_bytes`.
    #[test]
    fn doc_round_trip_little_endian() {
        let mut bytes = [0u8; 32];
        let numbers_given: [u64; 4] = [1, 2, 0xf00f, 0xffee];
        write_u64_into(&numbers_given, &mut bytes);

        let mut numbers_got = [0u64; 4];
        for (i, chunk) in bytes.chunks_exact(8).enumerate() {
            numbers_got[i] = u64::from_le_bytes(chunk.try_into().unwrap());
        }
        assert_eq!(numbers_given, numbers_got);
    }

    // Transferred from the `slice_lengths!` macro invocation
    // `slice_len_too_small_u64` (write_little_endian arm) in
    // src/lib.rs around line 3195 of the source crate.
    #[test]
    #[should_panic]
    fn slice_len_too_small_u64_write_little_endian() {
        let mut bytes = [0u8; 15];
        let numbers: [u64; 2] = [0, 0];
        write_u64_into(&numbers, &mut bytes);
    }

    // Transferred from the `slice_lengths!` macro invocation
    // `slice_len_too_big_u64` (write_little_endian arm) in
    // src/lib.rs around line 3202 of the source crate.
    #[test]
    #[should_panic]
    fn slice_len_too_big_u64_write_little_endian() {
        let mut bytes = [0u8; 17];
        let numbers: [u64; 2] = [0, 0];
        write_u64_into(&numbers, &mut bytes);
    }
}
