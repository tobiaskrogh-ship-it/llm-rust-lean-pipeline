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
    use std::panic;

    /// Independent reference for the big-endian decoding of the first eight
    /// bytes: the most significant byte is `buf[0]`, the least significant is
    /// `buf[7]`. Only the first eight bytes participate.
    fn be_first_eight(buf: &[u8]) -> u64 {
        let mut acc: u64 = 0;
        for i in 0..8 {
            acc = (acc << 8) | (buf[i] as u64);
        }
        acc
    }

    /// Deterministic xorshift64 PRNG so the "property" exploration is
    /// reproducible (no external proptest/quickcheck dependency, which would
    /// also not survive downstream hax extraction).
    fn next(state: &mut u64) -> u64 {
        let mut x = *state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        *state = x;
        x
    }

    /// Postcondition: for every buffer of length >= 8, `read_u64` returns the
    /// big-endian value built from exactly the first eight bytes, in order
    /// (`buf[0]` most significant ... `buf[7]` least significant), and ignores
    /// every byte at index >= 8.
    ///
    /// This single property pins down three independent claims at once:
    ///   * which bytes are read (the first eight, not some other window),
    ///   * the byte order (big-endian, distinguishing it from little-endian
    ///     and from byte-swapped variants — the structured single-byte cases
    ///     below would all collide under a wrong order),
    ///   * that trailing bytes (index >= 8) do not affect the result
    ///     (exercised by the buffers longer than 8 with non-zero tails).
    #[test]
    fn postcondition_big_endian_of_first_eight_bytes() {
        // Structured edge cases.
        let mut cases: Vec<Vec<u8>> = Vec::new();
        cases.push(vec![0u8; 8]); // minimum length, all zero
        cases.push(vec![0xFFu8; 8]); // all ones -> u64::MAX
        cases.push(vec![0u8; 32]); // long, all zero
        cases.push(vec![0xFFu8; 32]); // long, all ones, non-zero tail
        // One byte set at each of the eight significant positions, with a
        // distinctive non-zero tail to catch off-by-one window / endianness.
        for pos in 0..8 {
            let mut b = vec![0u8; 16];
            b[pos] = 0xAB;
            for t in 8..16 {
                b[t] = 0x5C; // garbage tail that must be ignored
            }
            cases.push(b);
        }
        // Ascending and descending byte patterns (every byte distinct).
        cases.push((0u8..20).collect());
        cases.push((0u8..20).rev().collect());

        // Pseudo-random buffers of varying length >= 8.
        let mut state: u64 = 0x9E37_79B9_7F4A_7C15;
        for _ in 0..512 {
            let len = 8 + (next(&mut state) % 17) as usize; // 8 ..= 24
            let mut b = vec![0u8; len];
            for byte in b.iter_mut() {
                *byte = (next(&mut state) & 0xFF) as u8;
            }
            cases.push(b);
        }

        for buf in &cases {
            assert_eq!(
                read_u64(buf),
                be_first_eight(buf),
                "mismatch for buffer {:?}",
                buf
            );
        }
    }

    /// Precondition / failure condition: `read_u64` panics for every buffer
    /// shorter than eight bytes (lengths 0 through 7), and does *not* panic at
    /// the boundary length 8. This pins the precondition exactly at
    /// `buf.len() >= 8` — a buggy implementation slicing a different prefix
    /// (e.g. `buf[..4]`) would survive some short buffers and be caught here.
    #[test]
    fn panics_iff_buffer_shorter_than_eight() {
        let hook = panic::take_hook();
        panic::set_hook(Box::new(|_| {})); // silence expected-panic noise

        for len in 0usize..8 {
            let buf = vec![0u8; len];
            let r = panic::catch_unwind(|| read_u64(&buf));
            assert!(r.is_err(), "expected panic for length {len}");
        }
        // Boundary: length exactly 8 must succeed.
        let ok = panic::catch_unwind(|| read_u64(&[0u8; 8]));
        assert!(ok.is_ok(), "length 8 must not panic");

        panic::set_hook(hook);
    }
}
