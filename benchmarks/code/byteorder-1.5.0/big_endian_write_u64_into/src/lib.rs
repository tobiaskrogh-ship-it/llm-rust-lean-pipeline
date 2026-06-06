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
