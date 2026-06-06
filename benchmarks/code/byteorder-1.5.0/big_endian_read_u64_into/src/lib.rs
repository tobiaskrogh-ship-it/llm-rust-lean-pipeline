//! Extracted from `byteorder` 1.5.0:
//! `<byteorder::BigEndian as byteorder::ByteOrder>::read_u64_into`.
//!
//! The original method body uses a `read_slice!` macro that expands to the
//! loop below. Since the impl pins the type universe to big-endian / `u64`,
//! we materialize the expansion directly as a free function.

pub fn read_u64_into(src: &[u8], dst: &mut [u64]) {
    const SIZE: usize = core::mem::size_of::<u64>();
    // Check types (preserved from the original macro for parity):
    let src: &[u8] = src;
    let dst: &mut [u64] = dst;
    assert_eq!(src.len(), dst.len() * SIZE);
    for (src, dst) in src.chunks_exact(SIZE).zip(dst.iter_mut()) {
        *dst = u64::from_be_bytes(src.try_into().unwrap());
    }
}

#[cfg(test)]
mod tests {
    use super::read_u64_into;

    // Transferred from `slice_lengths!(slice_len_too_small_u64, read_u64_into, ..., 15, [0, 0])`
    // in byteorder/src/lib.rs (≈3195). Only the BigEndian read arm is
    // transferable here; the LittleEndian/NativeEndian arms and the write
    // arms refer to functions we did not extract.
    mod slice_len_too_small_u64 {
        use super::read_u64_into;

        #[test]
        #[should_panic]
        fn read_big_endian() {
            let bytes = [0; 15];
            let mut numbers = [0u64, 0];
            read_u64_into(&bytes, &mut numbers);
        }
    }

    // Transferred from `slice_lengths!(slice_len_too_big_u64, read_u64_into, ..., 17, [0, 0])`.
    mod slice_len_too_big_u64 {
        use super::read_u64_into;

        #[test]
        #[should_panic]
        fn read_big_endian() {
            let bytes = [0; 17];
            let mut numbers = [0u64, 0];
            read_u64_into(&bytes, &mut numbers);
        }
    }

}
