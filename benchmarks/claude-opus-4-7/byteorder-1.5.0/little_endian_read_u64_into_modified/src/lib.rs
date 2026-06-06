//! Extracted from `byteorder` 1.5.0:
//! `<LittleEndian as ByteOrder>::read_u64_into` (src/lib.rs:2214).
//!
//! `LittleEndian` is an empty enum (zero-sized marker), so the associated
//! function is rewritten as a free `pub fn`. The body is the expansion of
//! the source's private `read_slice!` macro instantiated with
//! `(src, dst, u64, from_le_bytes)`.
//
// Hax-compatibility rewrite notes (driven by `cargo hax into lean` /
// `lake build` against the pinned Hax Lean prelude; mirrors the verified
// `big_endian_read_u64_into_modified` reference, adjusted for the
// little-endian byte order):
//
//   * `core::mem::size_of::<u64>()` is a generic intrinsic with no Hax
//     model; replaced by the literal `8` (the fixed `u64` byte width).
//     (`rewrite_patterns/mem_size_of_to_literal.rs`.)
//
//   * `assert_eq!(a, b)` desugars to `core::panicking::assert_failed`,
//     which is NOT defined in the Hax Lean prelude (only
//     `core_models.panicking.{panic,panic_explicit,panic_fmt}` and
//     `rust_primitives.hax_lib.assert` are). Replaced by
//     `hax_lib::assert!(a == b)`, which proxies to `core::assert!` in
//     normal builds (so the `#[should_panic]` / `catch_unwind`
//     length-mismatch tests still panic on the same condition) and
//     extracts to the modeled `rust_primitives.hax_lib.assert` under
//     Hax. The panic condition is bit-for-bit identical to the original:
//     panic iff `src.len() != dst.len() * 8`.
//     (`rewrite_patterns/assert_eq_macro_to_hax_assert.rs`.)
//
//   * `src.chunks_exact(SIZE).zip(dst.iter_mut())` is an iterator
//     combinator chain over slices (`core_models.iter.*` /
//     `IntoIterator` / `Iterator::fold`), none modeled by the Hax Lean
//     prelude. Converted to index-based tail recursion (`build_values`),
//     preferred over a `while` loop per the recursion-preference rule.
//     Decreasing measure `count - i`; extracted as `partial_fixpoint`.
//     (`rewrite_patterns/for_loop_over_slice_to_recursion.rs`.)
//
//   * `u64::from_le_bytes(src.try_into().unwrap())` bundles range
//     slicing + slice->array `TryInto` + `Result::unwrap` +
//     `from_le_bytes` — all outside the modeled fragment
//     (`core_models.num.Impl_*.from_le_bytes` is undefined). Replaced by
//     direct little-endian assembly with widening `u8 as u64` casts +
//     shifts + `|` (all modeled), per
//     `rewrite_patterns/from_be_bytes_slice_try_into.rs` (little-endian
//     variant: byte 0 is least significant).
//
//   * In-place per-element store into the `&mut [u64]` slice
//     (`*dst = ...`) extracts to
//     `rust_primitives.hax.monomorphized_update_at.update_at_usize`,
//     which the prelude types only for `RustArray`, never `RustSlice`.
//     Fixed (per `rewrite_patterns/slice_element_store_to_copy_from_slice.rs`
//     and the verified `big_endian_read_u64_into_modified` reference) by
//     building the fully decoded buffer in a fresh `Vec<u64>` (recursion
//     + `Vec::extend_from_slice` with a *typed* `[u64; 1]` chunk, both
//     modeled) and writing it back with the modeled
//     `<[u64]>::copy_from_slice`. `copy_from_slice` requires equal
//     lengths, which holds by construction (`build_values` emits exactly
//     one element per chunk, and after the assert there are exactly
//     `dst.len()` chunks), so the empty-slice no-op behaviour is
//     unchanged.

/// Little-endian decode of the 8 bytes at `src[base .. base + 8]`.
//
// Replaces `u64::from_le_bytes(src[base..base+8].try_into().unwrap())`.
// Byte at the lowest index is the LEAST significant (little-endian);
// `src[base + k]` contributes bits `[8k, 8k+8)`, matching the test's
// hand-written oracle `expected |= (src[8*i+j] as u64) << (8*j)`. Each
// `src[base + k]` is the modeled partial index operator, so an
// out-of-bounds access panics exactly where the original
// `chunks_exact(8)` walk would have stopped short on a too-small `src`.
fn read_le_u64(src: &[u8], base: usize) -> u64 {
    (src[base] as u64)
        | ((src[base + 1] as u64) << 8)
        | ((src[base + 2] as u64) << 16)
        | ((src[base + 3] as u64) << 24)
        | ((src[base + 4] as u64) << 32)
        | ((src[base + 5] as u64) << 40)
        | ((src[base + 6] as u64) << 48)
        | ((src[base + 7] as u64) << 56)
}

/// Build the decoded image of `dst`: element `i` is the little-endian
/// decode of `src[8*i .. 8*i + 8]`, for `i` in `0 .. count`, appended to
/// `acc`.
//
// Index-based tail recursion (preferred over `while` per the
// recursion-preference rule); decreasing measure `count - i`. `Vec::push`
// (`alloc.vec.Impl_1.push`) is undefined in the Hax prelude, so the
// element is appended via `Vec::extend_from_slice`
// (`alloc.vec.Impl_2.extend_from_slice`, modeled) using a *typed*
// `let chunk: [u64; 1]` binding so the array size appears in the type
// ascription and Hax can resolve `unsize`'s `RustArray` size parameter
// (cf. `rewrite_patterns/vec_push_to_extend_from_slice_typed_chunk.rs`).
fn build_values(src: &[u8], i: usize, count: usize, acc: Vec<u64>) -> Vec<u64> {
    if i >= count {
        acc
    } else {
        let mut acc = acc;
        let chunk: [u64; 1] = [read_le_u64(src, i * 8)];
        acc.extend_from_slice(&chunk);
        build_values(src, i + 1, count, acc)
    }
}

/// Reads unsigned 64 bit little-endian integers from `src` into `dst`.
///
/// # Panics
///
/// Panics when `src.len() != 8*dst.len()`.
pub fn read_u64_into(src: &[u8], dst: &mut [u64]) {
    // Precondition `src.len() == dst.len() * 8`, preserved from the
    // original `assert_eq!`. `hax_lib::assert!` panics in normal builds
    // (proxied to `core::assert!`, so the `#[should_panic]` /
    // `catch_unwind` tests still pass) and extracts to the modeled
    // `rust_primitives.hax_lib.assert` under Hax.
    hax_lib::assert!(src.len() == dst.len() * 8);
    let count = dst.len();
    let values = build_values(src, 0, count, Vec::new());
    dst.copy_from_slice(&values);
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
