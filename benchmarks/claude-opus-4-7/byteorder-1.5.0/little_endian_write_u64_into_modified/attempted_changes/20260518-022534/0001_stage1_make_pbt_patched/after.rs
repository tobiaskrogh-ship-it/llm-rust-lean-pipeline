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

    /// Deterministic xorshift64 PRNG so the "property" inputs are
    /// reproducible without pulling in an external proptest/quickcheck
    /// dependency (which would also be noise for the downstream
    /// extraction pipeline).
    fn next_u64(state: &mut u64) -> u64 {
        let mut x = *state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        *state = x;
        x
    }

    /// POSTCONDITION (the full functional contract).
    ///
    /// For any `src` and a correctly sized `dst`, after the call every
    /// destination byte is exactly the little-endian serialization of the
    /// corresponding source element:
    ///
    ///   dst[8*i + j] == (src[i] >> (8*j)) as u8     for all i, j
    ///
    /// The index set `{ 8*i + j : i < src.len(), j < 8 }` is exactly
    /// `0 .. dst.len()`, so this single check also asserts that *every*
    /// byte of `dst` is written (we pre-fill `dst` with a sentinel that
    /// must be completely overwritten) and pins the encoding to
    /// little-endian. It also necessarily covers that a validly sized
    /// call does not panic, including the empty edge case (`len == 0`,
    /// where the loop body never runs).
    #[test]
    fn postcondition_little_endian_layout_covers_all_bytes() {
        let mut rng: u64 = 0x9E37_79B9_7F4A_7C15;
        for len in 0usize..=64 {
            let src: Vec<u64> = (0..len).map(|_| next_u64(&mut rng)).collect();
            // Sentinel pattern: every byte must be overwritten.
            let mut dst = vec![0xAAu8; len * 8];

            write_u64_into(&src, &mut dst);

            assert_eq!(dst.len(), src.len() * 8);
            for i in 0..len {
                for j in 0..8 {
                    let expected = (src[i] >> (8 * j)) as u8;
                    assert_eq!(
                        dst[i * 8 + j],
                        expected,
                        "byte {} (element {}, offset {}) wrong for len {}",
                        i * 8 + j,
                        i,
                        j,
                        len,
                    );
                }
            }
        }
    }

    /// FAILURE CONDITION / PRECONDITION.
    ///
    /// The function panics for every length pair that violates
    /// `dst.len() == 8 * src.len()`, and only for those. We sweep a grid
    /// of `(src_len, dst_len)` pairs and assert: mismatch => panic,
    /// match => no panic.
    #[test]
    fn panics_exactly_when_length_relation_violated() {
        // Silence the default panic output for the deliberate panics.
        let prev = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));

        for src_len in 0usize..=10 {
            for dst_len in 0usize..=88 {
                let src = vec![0u64; src_len];
                let result = std::panic::catch_unwind(move || {
                    let mut dst = vec![0u8; dst_len];
                    write_u64_into(&src, &mut dst);
                });
                let satisfies_precondition = dst_len == src_len * 8;
                assert_eq!(
                    result.is_ok(),
                    satisfies_precondition,
                    "src_len = {}, dst_len = {}: expected panic == {}",
                    src_len,
                    dst_len,
                    !satisfies_precondition,
                );
            }
        }

        std::panic::set_hook(prev);
    }
}
