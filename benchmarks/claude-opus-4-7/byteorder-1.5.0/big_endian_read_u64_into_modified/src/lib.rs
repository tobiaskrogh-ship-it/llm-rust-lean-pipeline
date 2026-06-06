//! Extracted from `byteorder` 1.5.0:
//! `<byteorder::BigEndian as byteorder::ByteOrder>::read_u64_into`.
//!
//! The original method body uses a `read_slice!` macro that expands to the
//! loop below. Since the impl pins the type universe to big-endian / `u64`,
//! we materialize the expansion directly as a free function.
//
// Hax-compatibility rewrite notes (driven by `cargo hax into lean` /
// `lake build` against the pinned Hax Lean prelude):
//
//   * `core::mem::size_of::<u64>()` is a generic intrinsic with no Hax
//     model; replaced by the literal `8` (the fixed `u64` byte width).
//
//   * `assert_eq!(a, b)` desugars to `core::panicking::assert_failed`,
//     which is NOT defined in the Hax Lean prelude (only
//     `core_models.panicking.{panic,panic_explicit,panic_fmt}` and
//     `rust_primitives.hax_lib.assert` are). Replaced by
//     `hax_lib::assert!(a == b)`, which proxies to `core::assert!` in
//     normal builds (so the `#[should_panic]` length-mismatch tests
//     still panic) and extracts to the modeled
//     `rust_primitives.hax_lib.assert` (fails with `.assertionFailure`
//     when the condition is false) under Hax. The panic condition is
//     bit-for-bit identical to the original: panic iff
//     `src.len() != dst.len() * 8`.
//
//   * `src.chunks_exact(SIZE).zip(dst.iter_mut())` is an iterator
//     combinator chain over slices (`core_models.iter.*` /
//     `IntoIterator` / `Iterator::fold`), none modeled by the Hax Lean
//     prelude. Converted to index-based tail recursion (`build_values`),
//     preferred over a `while` loop per the recursion-preference rule.
//     Decreasing measure `count - i`; extracted as `partial_fixpoint`.
//
//   * `u64::from_be_bytes(src.try_into().unwrap())` bundles range
//     slicing + slice->array `TryInto` + `Result::unwrap` +
//     `from_be_bytes` — all outside the modeled fragment
//     (`core_models.num.Impl_*.from_be_bytes` is undefined). Replaced by
//     direct big-endian assembly with widening `u8 as u64` casts +
//     shifts + `|` (all modeled), per
//     `rewrite_patterns/from_be_bytes_slice_try_into.rs`.
//
//   * In-place per-element store into the `&mut [u64]` slice
//     (`*dst = ...`) extracts to
//     `rust_primitives.hax.monomorphized_update_at.update_at_usize`,
//     which the prelude types only for `RustArray`, never `RustSlice`.
//     Fixed (per `rewrite_patterns/slice_element_store_to_copy_from_slice.rs`
//     and the verified `big_endian_from_slice_u64` reference) by building
//     the fully decoded buffer in a fresh `Vec<u64>` (recursion +
//     `Vec::extend_from_slice` with a *typed* `[u64; 1]` chunk, both
//     modeled) and writing it back with the modeled
//     `<[u64]>::copy_from_slice`. `copy_from_slice` requires equal
//     lengths, which holds by construction (`build_values` emits exactly
//     one element per chunk, and after the assert there are exactly
//     `dst.len()` chunks), so the empty-slice no-op test still passes.

/// Big-endian decode of the 8 bytes at `src[base .. base + 8]`.
//
// Replaces `u64::from_be_bytes(src[base..base+8].try_into().unwrap())`.
// Byte at the lowest index is the most significant (big-endian). Each
// `src[base + k]` is the modeled partial index operator, so an
// out-of-bounds access panics exactly where the original
// `chunks_exact(8)` walk would have stopped short on a too-small `src`.
fn read_be_u64(src: &[u8], base: usize) -> u64 {
    ((src[base] as u64) << 56)
        | ((src[base + 1] as u64) << 48)
        | ((src[base + 2] as u64) << 40)
        | ((src[base + 3] as u64) << 32)
        | ((src[base + 4] as u64) << 24)
        | ((src[base + 5] as u64) << 16)
        | ((src[base + 6] as u64) << 8)
        | (src[base + 7] as u64)
}

/// Build the decoded image of `dst`: element `i` is the big-endian
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
        let chunk: [u64; 1] = [read_be_u64(src, i * 8)];
        acc.extend_from_slice(&chunk);
        build_values(src, i + 1, count, acc)
    }
}

pub fn read_u64_into(src: &[u8], dst: &mut [u64]) {
    // Precondition `src.len() == dst.len() * 8`, preserved from the
    // original `assert_eq!`. `hax_lib::assert!` panics in normal builds
    // (proxied to `core::assert!`, so the `#[should_panic]` tests still
    // pass) and extracts to the modeled `rust_primitives.hax_lib.assert`
    // under Hax.
    hax_lib::assert!(src.len() == dst.len() * 8);
    let count = dst.len();
    let values = build_values(src, 0, count, Vec::new());
    dst.copy_from_slice(&values);
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

    // Postcondition: when called with a valid length, every output element is
    // the big-endian decoding of the corresponding 8-byte chunk of `src`.
    mod postcondition {
        use super::read_u64_into;

        // dst[i] == big-endian(src[8*i .. 8*i+8]) for all i. The input is
        // built from a known `values` vector via the trusted std oracle
        // `u64::to_be_bytes`, so the assertion `dst == values` fails for any
        // implementation that uses the wrong endianness, maps chunks to the
        // wrong element, reverses element order, or skips elements. Ranges
        // over several lengths (including 0) and byte patterns to behave as a
        // property over the valid-input domain.
        #[test]
        fn decodes_each_chunk_big_endian() {
            let patterns: [u64; 6] = [
                0,
                1,
                0x0000_0000_0000_00FF,
                0xFF00_0000_0000_0000,
                0x0123_4567_89AB_CDEF,
                u64::MAX,
            ];
            for n in 0..=4usize {
                // values[k] depends on k, so per-element ordering is exercised.
                let mut values = Vec::with_capacity(n);
                for k in 0..n {
                    values.push(patterns[k % patterns.len()] ^ (k as u64));
                }
                let mut src = Vec::with_capacity(n * 8);
                for v in &values {
                    src.extend_from_slice(&v.to_be_bytes());
                }
                let mut dst = vec![0u64; n];
                read_u64_into(&src, &mut dst);
                assert_eq!(dst, values);
            }
        }

        // Independent semantic claim: the decoding is big-endian (most
        // significant byte first) and chunk i lands in dst[i]. The oracle here
        // is hand-written and does not rely on `to_be_bytes`, so it pins the
        // byte orientation even if that std helper were itself wrong.
        #[test]
        fn big_endian_orientation_explicit() {
            let mut one = [0u64];
            read_u64_into(&[0, 0, 0, 0, 0, 0, 0, 1], &mut one);
            assert_eq!(one[0], 1);

            let mut hi = [0u64];
            read_u64_into(&[1, 0, 0, 0, 0, 0, 0, 0], &mut hi);
            assert_eq!(hi[0], 0x0100_0000_0000_0000);

            let mut two = [0u64; 2];
            read_u64_into(&[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2], &mut two);
            assert_eq!(two, [1, 2]);

            let mut mixed = [0u64];
            read_u64_into(&[0xDE, 0xAD, 0xBE, 0xEF, 0x01, 0x23, 0x45, 0x67], &mut mixed);
            assert_eq!(mixed[0], 0xDEAD_BEEF_0123_4567);
        }
    }

    // Precondition: the exact relation `src.len() == dst.len() * SIZE`.
    mod precondition {
        use super::read_u64_into;

        // Boundary of the precondition: 0 == 0 * SIZE holds, so empty slices
        // are a valid no-op call, not a panic.
        #[test]
        fn empty_slices_is_noop() {
            let src: [u8; 0] = [];
            let mut dst: [u64; 0] = [];
            read_u64_into(&src, &mut dst);
            assert_eq!(dst.len(), 0);
        }

        // Failure condition pinning the *exact* precondition rather than the
        // weaker `src.len() % SIZE == 0`: src.len() == 16 is a multiple of
        // SIZE, but dst.len() * SIZE == 8, so the call must still panic. The
        // existing 15-/17-byte tests do not distinguish these two checks.
        #[test]
        #[should_panic]
        fn len_multiple_of_size_but_mismatched_panics() {
            let bytes = [0u8; 16];
            let mut numbers = [0u64];
            read_u64_into(&bytes, &mut numbers);
        }
    }

}
