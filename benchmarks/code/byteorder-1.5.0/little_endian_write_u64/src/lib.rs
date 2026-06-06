//! Extracted from `byteorder` 1.5.0:
//! `impl ByteOrder for LittleEndian { fn write_u64(buf: &mut [u8], n: u64) }`
//! at src/lib.rs:2174.
//!
//! The original is an associated function (no `&self` receiver) on the
//! zero-sized marker type `LittleEndian`, so it is rewritten here as a free
//! function with the same signature and body.

/// Writes an unsigned 64-bit integer `n` to `buf` in little-endian order.
///
/// # Panics
///
/// Panics when `buf.len() < 8`.
#[inline]
pub fn write_u64(buf: &mut [u8], n: u64) {
    buf[..8].copy_from_slice(&n.to_le_bytes());
}

#[cfg(test)]
mod tests {
    use super::write_u64;

    // Transferred from the doc-comment on
    // `trait ByteOrder { fn write_u64(...) }` in src/lib.rs:464.
    // The original round-trips through `LittleEndian::read_u64`; since we
    // only extracted the writer, we verify the bytes against
    // `u64::from_le_bytes` (the documented serialization).
    #[test]
    fn doc_example_round_trip() {
        let mut buf = [0; 8];
        write_u64(&mut buf, 1_000_000);
        assert_eq!(1_000_000, u64::from_le_bytes(buf));
    }

    // Transferred from the `too_small!(small_u64, 7, 0, read_u64, write_u64)`
    // expansion at src/lib.rs:3022 — specifically the `write_little_endian`
    // arm (src/lib.rs:2974-2978): writing into a 7-byte buffer must panic.
    #[test]
    #[should_panic]
    fn write_little_endian_too_small() {
        let mut buf = [0; 7];
        write_u64(&mut buf, 0);
    }
}
