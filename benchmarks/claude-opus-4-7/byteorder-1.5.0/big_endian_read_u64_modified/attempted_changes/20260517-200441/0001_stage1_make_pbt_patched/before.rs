//! Extracted `BigEndian::read_u64` from `byteorder` 1.5.0.
//!
//! Source: src/lib.rs lines 1949-1952, inside `impl ByteOrder for BigEndian`.
//!
//! `BigEndian` is a zero-sized marker type (`pub enum BigEndian {}`) and
//! `read_u64` is an associated function (no `&self` receiver), so the
//! extraction simply drops to a free `pub fn` with an identical body.

/// Reads an unsigned 64 bit integer from `buf` in big-endian byte order.
///
/// # Panics
///
/// Panics when `buf.len() < 8`.
#[inline]
pub fn read_u64(buf: &[u8]) -> u64 {
    u64::from_be_bytes(buf[..8].try_into().unwrap())
}

#[cfg(test)]
mod tests {
    use super::read_u64;

    // Transferred from byteorder src/lib.rs `regression173_array_impl`
    // (the `BigEndian::read_u64` portion).
    #[test]
    fn regression173_array_impl() {
        let xs = [0; 100];
        let x = read_u64(&xs);
        assert_eq!(x, 0);
    }

    // Transferred from byteorder src/lib.rs:
    //   too_small!(small_u64, 7, 0, read_u64, write_u64);
    // which expands to a `read_big_endian` test that panics when the buffer
    // is one byte short.
    #[test]
    #[should_panic]
    fn small_u64_read_big_endian() {
        let buf = [0; 7];
        read_u64(&buf);
    }
}
