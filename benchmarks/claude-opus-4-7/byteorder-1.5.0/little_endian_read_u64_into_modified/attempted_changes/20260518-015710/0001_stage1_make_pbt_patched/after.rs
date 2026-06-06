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

    // ---- Property-based tests ----
    //
    // Deterministic, dependency-free generator so the suite is reproducible
    // (and friendly to downstream proof extraction).
    struct Lcg(u64);
    impl Lcg {
        fn new(seed: u64) -> Self {
            Lcg(seed)
        }
        fn next_u64(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.0
        }
        fn next_byte(&mut self) -> u8 {
            (self.next_u64() >> 56) as u8
        }
        // Uniform-ish value in `0..bound`; `bound` is always > 0 here.
        fn next_below(&mut self, bound: usize) -> usize {
            (self.next_u64() as usize) % bound
        }
    }

    // Postcondition: for a valid call (`src.len() == 8 * dst.len()`), every
    // output element equals the little-endian decoding of its 8-byte chunk,
    // i.e. byte `j` of chunk `i` contributes bits `[8j, 8j+8)` of `dst[i]`.
    //
    // The expected value is computed by hand (not via `u64::from_le_bytes`),
    // so this independently pins down: the little-endian byte order, the
    // chunk-to-element alignment, and that every element is written. A
    // big-endian, off-by-one, or element-skipping implementation would fail.
    // `count == 0` is exercised as the valid empty-slice edge case.
    #[test]
    fn prop_little_endian_decode_postcondition() {
        let mut rng = Lcg::new(0x1234_5678_9abc_def0);
        for _ in 0..256 {
            let count = rng.next_below(9); // 0..=8 output integers
            let mut src = vec![0u8; count * 8];
            for b in src.iter_mut() {
                *b = rng.next_byte();
            }
            let mut dst = vec![0u64; count];
            read_u64_into(&src, &mut dst);

            for i in 0..count {
                let mut expected = 0u64;
                for j in 0..8 {
                    expected |= (src[8 * i + j] as u64) << (8 * j);
                }
                assert_eq!(dst[i], expected, "mismatch at output index {i}");
            }
        }
    }

    // Failure condition: the function panics whenever the length invariant
    // `src.len() == 8 * dst.len()` is violated (the leading `assert_eq!`).
    // Covers mismatches in both directions and the empty-vs-nonempty cases.
    #[test]
    fn prop_length_mismatch_panics() {
        let mut rng = Lcg::new(0x0fed_cba9_8765_4321);
        // Silence the panic hook so the expected panics don't spam stderr.
        let prev_hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));

        for _ in 0..256 {
            let src_len = rng.next_below(40);
            let dst_len = rng.next_below(8);
            if src_len == dst_len * 8 {
                continue; // a valid call — not what this test covers
            }
            let src = vec![0u8; src_len];
            let mut dst = vec![0u64; dst_len];
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                read_u64_into(&src, &mut dst);
            }));
            assert!(
                result.is_err(),
                "expected panic for src_len={src_len}, dst_len={dst_len}"
            );
        }

        std::panic::set_hook(prev_hook);
    }
}
