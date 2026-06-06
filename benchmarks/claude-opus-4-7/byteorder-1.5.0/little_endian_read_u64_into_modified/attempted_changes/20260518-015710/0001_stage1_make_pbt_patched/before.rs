//! Extracted from `byteorder` 1.5.0:
//! `<LittleEndian as ByteOrder>::read_u64_into` (src/lib.rs:2214).
//!
//! `LittleEndian` is an empty enum (zero-sized marker), so the associated
//! function is rewritten as a free `pub fn`. The body is the expansion of
//! the source's private `read_slice!` macro instantiated with
//! `(src, dst, u64, from_le_bytes)`.

/// Reads unsigned 64 bit little-endian integers from `src` into `dst`.
///
/// # Panics
///
/// Panics when `src.len() != 8*dst.len()`.
#[inline]
pub fn read_u64_into(src: &[u8], dst: &mut [u64]) {
    const SIZE: usize = core::mem::size_of::<u64>();
    // Check types:
    let src: &[u8] = src;
    let dst: &mut [u64] = dst;
    assert_eq!(src.len(), dst.len() * SIZE);
    for (src, dst) in src.chunks_exact(SIZE).zip(dst.iter_mut()) {
        *dst = <u64>::from_le_bytes(src.try_into().unwrap());
    }
}

#[cfg(test)]
mod tests {
    use super::read_u64_into;

    // Doc-test from `ByteOrder::read_u64_into` (src/lib.rs:1032..1042).
    // The original used `LittleEndian::write_u64_into` to build the byte
    // buffer; we inline that step with `u64::to_le_bytes` so the test is
    // self-contained.
    #[test]
    fn doc_example_little_endian_roundtrip() {
        let numbers_given: [u64; 4] = [1, 2, 0xf00f, 0xffee];
        let mut bytes = [0u8; 32];
        for (n, chunk) in numbers_given.iter().zip(bytes.chunks_exact_mut(8)) {
            chunk.copy_from_slice(&n.to_le_bytes());
        }

        let mut numbers_got = [0u64; 4];
        read_u64_into(&bytes, &mut numbers_got);
        assert_eq!(numbers_given, numbers_got);
    }

    // From the `slice_lengths!(slice_len_too_small_u64, read_u64_into, ...,
    // 15, [0, 0])` invocation (src/lib.rs:3195..3201). Only the LittleEndian
    // `read_*` arm is transferable here; the BigEndian/NativeEndian and
    // write_* arms are out of scope for this extraction.
    #[test]
    #[should_panic]
    fn slice_len_too_small_u64_read_little_endian() {
        let bytes = [0u8; 15];
        let mut numbers = [0u64; 2];
        read_u64_into(&bytes, &mut numbers);
    }

    // From `slice_lengths!(slice_len_too_big_u64, read_u64_into, ..., 17,
    // [0, 0])` (src/lib.rs:3202..3208).
    #[test]
    #[should_panic]
    fn slice_len_too_big_u64_read_little_endian() {
        let bytes = [0u8; 17];
        let mut numbers = [0u64; 2];
        read_u64_into(&bytes, &mut numbers);
    }
}
