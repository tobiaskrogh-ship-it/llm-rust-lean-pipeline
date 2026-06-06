//! Extracted from `byteorder` 1.5.0: `BigEndian::write_u64_into`.
//!
//! The original method is defined inside `impl ByteOrder for BigEndian` in
//! `src/lib.rs` and is implemented via the private `write_slice!` macro.
//! The macro body is inlined verbatim below.
//
// Hax-compatibility rewrite notes (driven by `cargo hax into lean` /
// `lake build` against the pinned Hax Lean prelude). This is the
// write-direction mirror of the verified `big_endian_read_u64_into`
// reference; the original body
//
//     const SIZE: usize = core::mem::size_of::<u64>();
//     assert_eq!(src.len() * SIZE, dst.len());
//     for (src, dst) in src.iter().zip(dst.chunks_exact_mut(SIZE)) {
//         dst.copy_from_slice(&src.to_be_bytes());
//     }
//
// bundles four constructs outside the Hax-modeled fragment:
//
//   1. `core::mem::size_of::<u64>()` is a generic intrinsic with no Hax
//      model; replaced by the literal `8` (the fixed `u64` byte width).
//      The "Check types:" `let src: &[u64] = src; let dst: &mut [u8] =
//      dst;` rebindings were pure type assertions with no runtime effect
//      and are dropped (the surrounding body is fully rewritten anyway).
//
//   2. `assert_eq!(a, b)` desugars to `core::panicking::assert_failed`,
//      which is NOT defined in the Hax Lean prelude (only
//      `core_models.panicking.{panic,panic_explicit,panic_fmt}` and
//      `rust_primitives.hax_lib.assert` are). Replaced by
//      `hax_lib::assert!(a == b)`, which proxies to `core::assert!` in
//      normal builds (so the `#[should_panic]` / `catch_unwind`
//      length-mismatch tests still panic) and extracts to the modeled
//      `rust_primitives.hax_lib.assert` under Hax. The panic condition
//      is bit-for-bit identical to the original: panic iff
//      `src.len() * 8 != dst.len()`.
//
//   3. `src.iter().zip(dst.chunks_exact_mut(SIZE))` is an iterator
//      combinator chain over slices (`core_models.iter.*` /
//      `IntoIterator` / `Iterator::fold` / `chunks_exact_mut`), none
//      modeled by the Hax Lean prelude. Converted to index-based tail
//      recursion (`build_output`), preferred over a `while` loop per the
//      recursion-preference rule. Decreasing measure `src.len() - i`;
//      extracted as `partial_fixpoint`.
//
//   4. `u64::to_be_bytes` extracts to `core_models.num.Impl_*.to_be_bytes`,
//      undefined in the Hax Lean prelude (`lake build`: Unknown
//      identifier). Replaced by direct big-endian disassembly with `>>`
//      + narrowing `as u8` casts (all modeled) — the write-side mirror
//      of `read_be_u64` in `big_endian_read_u64_into` and of
//      `rewrite_patterns/from_be_bytes_slice_try_into.rs`.
//
//   5. Even with the bytes in hand, the per-chunk in-place store into a
//      `&mut [u8]` slice (`dst.copy_from_slice` into a `chunks_exact_mut`
//      sub-slice) cannot stay per-element: a slice-element store extracts
//      to `rust_primitives.hax.monomorphized_update_at.update_at_usize`,
//      which the prelude types ONLY for `RustArray`, never `RustSlice`.
//      Fixed (per `rewrite_patterns/slice_element_store_to_copy_from_slice.rs`
//      and the verified `big_endian_read_u64_into` / `from_slice_u64`
//      references) by building the full target image in a fresh
//      `Vec<u8>` (index-based tail recursion + `Vec::extend_from_slice`
//      with a *typed* `[u8; 8]` chunk, both modeled) and writing it back
//      with the modeled `<[u8]>::copy_from_slice`. `copy_from_slice`
//      requires equal lengths, which holds by construction
//      (`build_output` emits exactly 8 bytes per input word, and after
//      the assert there are exactly `src.len()` words so `out.len() ==
//      src.len() * 8 == dst.len()`), so the empty-slice no-op boundary
//      (`0 == 8 * 0`) still passes.

/// Build the output image of `dst`: bytes `8*i .. 8*i + 8` are the
/// big-endian encoding of `src[i]`, for `i` in `0 .. src.len()`,
/// appended to `acc`.
//
// Index-based tail recursion (preferred over `while` per the
// recursion-preference rule); decreasing measure `src.len() - i`.
// `Vec::push` (`alloc.vec.Impl_1.push`) is undefined in the Hax prelude,
// so the 8 big-endian bytes are appended via `Vec::extend_from_slice`
// (`alloc.vec.Impl_2.extend_from_slice`, modeled) using a *typed*
// `let chunk: [u8; 8]` binding so the array size appears in the type
// ascription and Hax can resolve `unsize`'s `RustArray` size parameter
// (cf. `rewrite_patterns/vec_push_to_extend_from_slice_typed_chunk.rs`).
// The disassembly puts byte 0 as the most significant (big-endian),
// mirroring `read_be_u64` in the verified `big_endian_read_u64_into`.
fn build_output(src: &[u64], i: usize, acc: Vec<u8>) -> Vec<u8> {
    if i >= src.len() {
        acc
    } else {
        let n = src[i];
        let mut acc = acc;
        let chunk: [u8; 8] = [
            (n >> 56) as u8,
            (n >> 48) as u8,
            (n >> 40) as u8,
            (n >> 32) as u8,
            (n >> 24) as u8,
            (n >> 16) as u8,
            (n >> 8) as u8,
            n as u8,
        ];
        acc.extend_from_slice(&chunk);
        build_output(src, i + 1, acc)
    }
}

/// Writes unsigned 64 bit integers from `src` into `dst` in big-endian order.
///
/// # Panics
///
/// Panics when `dst.len() != 8 * src.len()`.
pub fn write_u64_into(src: &[u64], dst: &mut [u8]) {
    // Precondition `dst.len() == src.len() * 8`, preserved from the
    // original `assert_eq!`. `hax_lib::assert!` panics in normal builds
    // (proxied to `core::assert!`, so the `#[should_panic]` /
    // `catch_unwind` length-mismatch tests still pass) and extracts to
    // the modeled `rust_primitives.hax_lib.assert` under Hax.
    hax_lib::assert!(src.len() * 8 == dst.len());
    let out = build_output(src, 0, Vec::new());
    dst.copy_from_slice(&out);
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
