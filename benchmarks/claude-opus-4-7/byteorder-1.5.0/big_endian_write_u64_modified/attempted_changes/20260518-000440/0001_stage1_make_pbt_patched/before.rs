//! Extracted from `byteorder` 1.5.0: `BigEndian::write_u64`.
//!
//! Source: src/lib.rs:1987-1990, inside `impl ByteOrder for BigEndian`.
//! `BigEndian` is a zero-sized marker type and `write_u64` takes no `&self`
//! receiver, so the function is rewritten as a free `pub fn` with identical
//! signature and body.

#[inline]
pub fn write_u64(buf: &mut [u8], n: u64) {
    buf[..8].copy_from_slice(&n.to_be_bytes());
}

#[cfg(test)]
mod tests {
    use super::write_u64;

    // Transferred from src/lib.rs: `too_small!(small_u64, 7, 0, read_u64, write_u64);`
    // expansion of the `write_big_endian` arm. The `too_small!` macro generates
    // a `#[should_panic]` test that calls `BigEndian::write_u64(&mut [0; 7], 0)`
    // to ensure the function panics when the buffer is too small.
    #[test]
    #[should_panic]
    fn write_big_endian() {
        let mut buf = [0; 7];
        write_u64(&mut buf, 0);
    }
}
