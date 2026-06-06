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
    (buf[0] as u64)
        | ((buf[1] as u64) << 8)
        | ((buf[2] as u64) << 16)
        | ((buf[3] as u64) << 24)
        | ((buf[4] as u64) << 32)
        | ((buf[5] as u64) << 40)
        | ((buf[6] as u64) << 48)
        | ((buf[7] as u64) << 56)
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

    use proptest::prelude::*;

    proptest! {
        // Postcondition: when `buf.len() >= 8`, `read_u64` returns the
        // little-endian interpretation of the first 8 bytes of `buf`.
        //
        // The expected value is re-derived with an explicit shift/or over byte
        // positions `0..8` — an independent formulation of "little-endian" that
        // does not reuse `from_le_bytes`/`to_le_bytes`. A big-endian, byte-
        // swapped, or wrong-width implementation fails this. Generating buffers
        // *longer* than 8 bytes (length `8..=64`) also pins down that bytes at
        // index >= 8 are irrelevant, i.e. exactly the first 8 bytes are read.
        #[test]
        fn prop_little_endian_decode_of_first_8_bytes(
            buf in prop::collection::vec(any::<u8>(), 8..=64),
        ) {
            let expected =
                (0..8).fold(0u64, |acc, i| acc | ((buf[i] as u64) << (8 * i)));
            prop_assert_eq!(read_u64(&buf), expected);
        }

        // Failure condition: `read_u64` panics whenever `buf.len() < 8`
        // (the documented `# Panics` clause / precondition `buf.len() >= 8`).
        // Covers every short length `0..=7` with arbitrary contents.
        #[test]
        fn prop_panics_when_buffer_too_short(
            buf in prop::collection::vec(any::<u8>(), 0..8),
        ) {
            let result = std::panic::catch_unwind(
                std::panic::AssertUnwindSafe(|| read_u64(&buf)),
            );
            prop_assert!(result.is_err());
        }
    }
}
