//! Extracted from `byteorder` 1.5.0:
//! `<LittleEndian as ByteOrder>::read_u64` in `src/lib.rs` (line 2138).
//!
//! The original is an associated function on the `LittleEndian` marker enum
//! (no `&self`), so we drop the receiver and lift it to a free `pub fn`.

/// Reads an unsigned 64 bit integer from `buf` in little-endian order.
///
/// # Panics
///
/// Panics when `buf.len() < 8`.
#[inline]
pub fn read_u64(buf: &[u8]) -> u64 {
    u64::from_le_bytes(buf[..8].try_into().unwrap())
}

#[cfg(test)]
mod tests {
    use super::read_u64;

    // Transferred from the doc-test on `ByteOrder::read_u64`
    // (byteorder/src/lib.rs:302-308). The original wrote `1_000_000` with
    // `LittleEndian::write_u64` and then read it back; here we construct the
    // same little-endian byte buffer with `u64::to_le_bytes` instead and call
    // the extracted free function.
    #[test]
    fn doctest_read_u64() {
        let buf = 1_000_000u64.to_le_bytes();
        assert_eq!(1_000_000, read_u64(&buf));
    }

    // Transferred from `regression173_array_impl`
    // (byteorder/src/lib.rs:3260-3299), reduced to the `LittleEndian::read_u64`
    // line, which is the only assertion this extracted function can exercise.
    #[test]
    fn regression173_array_impl() {
        let xs = [0; 100];
        let x = read_u64(&xs);
        assert_eq!(x, 0);
    }

    // Transferred from `too_small!(small_u64, 7, 0, read_u64, write_u64)`
    // (byteorder/src/lib.rs:3022), specifically the `read_little_endian` arm
    // (lib.rs:2953-2957) which asserts that `LittleEndian::read_u64` panics
    // when given a buffer of length 7.
    #[test]
    #[should_panic]
    fn small_u64_read_little_endian() {
        let buf = [0; 7];
        read_u64(&buf);
    }
}
