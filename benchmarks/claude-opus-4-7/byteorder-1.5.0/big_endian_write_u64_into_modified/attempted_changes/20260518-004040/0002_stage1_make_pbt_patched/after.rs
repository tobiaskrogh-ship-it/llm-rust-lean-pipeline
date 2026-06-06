//! Extracted from `byteorder` 1.5.0: `BigEndian::write_u64_into`.
//!
//! The original method is defined inside `impl ByteOrder for BigEndian` in
//! `src/lib.rs` and is implemented via the private `write_slice!` macro.
//! The macro body is inlined verbatim below.

/// Writes unsigned 64 bit integers from `src` into `dst` in big-endian order.
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
        dst.copy_from_slice(&src.to_be_bytes());
    }
}

#[cfg(test)]
mod tests {
    use super::write_u64_into;
    use proptest::prelude::*;

    proptest! {
        // Postcondition: when the length precondition holds
        // (`dst.len() == 8 * src.len()`), the call succeeds and every output
        // byte is the big-endian encoding of the corresponding input word.
        //
        // Big-endian is spelled out independently here (most-significant byte
        // first, via bit shifts) rather than reusing `u64::to_be_bytes`, so a
        // buggy little-endian / byte-swapped implementation would be caught.
        // The `0..` length range also exercises the empty-slice boundary of
        // the precondition (0 == 8 * 0, must not panic, must write nothing).
        #[test]
        fn prop_writes_big_endian_bytes(
            src in prop::collection::vec(any::<u64>(), 0..32usize),
        ) {
            let mut dst = vec![0u8; src.len() * 8];
            write_u64_into(&src, &mut dst);

            prop_assert_eq!(dst.len(), src.len() * 8);
            for (i, &value) in src.iter().enumerate() {
                for j in 0..8usize {
                    let expected = ((value >> (8 * (7 - j))) & 0xff) as u8;
                    prop_assert_eq!(
                        dst[i * 8 + j],
                        expected,
                        "word {} byte {}",
                        i,
                        j
                    );
                }
            }
        }

        // Failure condition: the function panics for any length pairing that
        // violates `dst.len() == 8 * src.len()`. Generalizes the two fixed
        // `#[should_panic]` cases below (too small / too big) to arbitrary
        // mismatched lengths, including the `dst` shorter and longer cases.
        #[test]
        fn prop_panics_on_length_mismatch(
            src in prop::collection::vec(any::<u64>(), 0..16usize),
            dst_len in 0..200usize,
        ) {
            prop_assume!(dst_len != src.len() * 8);
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let mut dst = vec![0u8; dst_len];
                write_u64_into(&src, &mut dst);
            }));
            prop_assert!(result.is_err());
        }
    }

    // Transferred from byteorder src/lib.rs `slice_lengths!(slice_len_too_small_u64, ..., 15, [0, 0])`.
    // Only the BigEndian write variant is transferred — the rest of the
    // generated module exercises read_u64_into / LittleEndian / NativeEndian
    // which are not part of this extraction.
    #[test]
    #[should_panic]
    fn slice_len_too_small_u64_write_big_endian() {
        let mut bytes = [0; 15];
        let numbers: [u64; 2] = [0, 0];
        write_u64_into(&numbers, &mut bytes);
    }

    // Transferred from byteorder src/lib.rs `slice_lengths!(slice_len_too_big_u64, ..., 17, [0, 0])`.
    #[test]
    #[should_panic]
    fn slice_len_too_big_u64_write_big_endian() {
        let mut bytes = [0; 17];
        let numbers: [u64; 2] = [0, 0];
        write_u64_into(&numbers, &mut bytes);
    }
}
