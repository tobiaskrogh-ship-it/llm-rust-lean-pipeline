//! Extracted from `byteorder` 1.5.0 — `LittleEndian::write_u64_into`.
//!
//! This function writes a slice of `u64` values into a destination byte
//! slice using little-endian encoding. Its body is the inlined expansion
//! of the `write_slice!` macro from the source crate, specialized to
//! `u64` / `to_le_bytes`.
//!
//! `LittleEndian` is a zero-sized marker type in the source crate, so the
//! receiver has been dropped and the function is exposed as a free `pub fn`.
//
// Hax-compatibility rewrite notes (driven by `cargo hax into lean` /
// `lake build` against the pinned Hax Lean prelude). The original body
//
//     const SIZE: usize = core::mem::size_of::<u64>();
//     let src: &[u64] = src;
//     let dst: &mut [u8] = dst;
//     assert_eq!(src.len() * SIZE, dst.len());
//     for (src, dst) in src.iter().zip(dst.chunks_exact_mut(SIZE)) {
//         dst.copy_from_slice(&src.to_le_bytes());
//     }
//
// bundles five constructs outside the Hax-modeled fragment:
//
//   1. `core::mem::size_of::<u64>()` is a generic compiler intrinsic with
//      no Hax model. `u64` is a fixed primitive, so the constant is
//      replaced by its literal byte width `8` and the inert "Check types"
//      rebindings are dropped (cf.
//      `rewrite_patterns/mem_size_of_to_literal.rs`).
//
//   2. `assert_eq!(a, b)` desugars to `core::panicking::assert_failed`,
//      undefined in the Hax Lean prelude. Replaced by
//      `hax_lib::assert!(a == b)`, which proxies to `core::assert!` in
//      normal builds (so the `#[should_panic]` / `catch_unwind`
//      length-mismatch tests still panic identically) and extracts to
//      the modeled `rust_primitives.hax_lib.assert` (cf.
//      `rewrite_patterns/assert_eq_macro_to_hax_assert.rs`).
//
//   3. `src.iter().zip(dst.chunks_exact_mut(SIZE))` is an iterator
//      combinator chain extracting to unmodeled `core_models.iter.*`
//      symbols. Replaced by index-based tail recursion (preferred over a
//      `while` loop per the recursion-preference rule; cf.
//      `rewrite_patterns/iter_chain_to_recursion.rs` /
//      `for_loop_over_slice_to_recursion.rs`).
//
//   4. `u64::to_le_bytes` extracts to `core_models.num.Impl_*.to_le_bytes`,
//      undefined in the Hax Lean prelude. Replaced by direct
//      little-endian disassembly with `>>` + narrowing `as u8` casts
//      (all modeled) — the write-side mirror of
//      `rewrite_patterns/from_be_bytes_slice_try_into.rs`.
//
//   5. In-place mutation of the `&mut [u8]` destination through
//      `chunks_exact_mut` / per-element store extracts to
//      `rust_primitives.hax.monomorphized_update_at.update_at_usize`,
//      which the prelude types ONLY for `RustArray`, never `RustSlice`.
//      Fixed (per `rewrite_patterns/slice_element_store_to_copy_from_slice.rs`
//      and the verified `big_endian_write_u64` / `big_endian_from_slice_u64`
//      references) by building the full target image in a fresh `Vec<u8>`
//      (index-based tail recursion + `Vec::extend_from_slice` with a
//      *typed* `[u8; 8]` chunk, both modeled; `Vec::push` is undefined in
//      the prelude) and writing it back with the modeled
//      `<[u8]>::copy_from_slice`. `out.len() == src.len() * 8 == dst.len()`
//      holds after the assert, so `copy_from_slice`'s equal-length
//      requirement is satisfied by construction and the empty-slice edge
//      case is preserved.

/// Build the little-endian byte image of `src[i..]`, appended to `acc`.
//
// Index-based tail recursion over the immutable `&[u64]` source
// (decreasing measure `src.len() - i`). The 8 little-endian bytes of
// each element are appended through a *typed* `let chunk: [u8; 8]`
// binding so the array size appears in the type ascription and Hax can
// resolve `unsize`'s `RustArray` size parameter (cf.
// `rewrite_patterns/vec_push_to_extend_from_slice_typed_chunk.rs` /
// `to_be_bytes_to_shift_disassembly.rs`). Extracted as
// `partial_fixpoint`; the proof stage handles it via `Nat.strongRecOn`.
fn build_output(src: &[u64], i: usize, acc: Vec<u8>) -> Vec<u8> {
    if i >= src.len() {
        acc
    } else {
        let mut acc = acc;
        let n = src[i];
        // Little-endian disassembly: byte 0 is the least significant.
        let chunk: [u8; 8] = [
            n as u8,
            (n >> 8) as u8,
            (n >> 16) as u8,
            (n >> 24) as u8,
            (n >> 32) as u8,
            (n >> 40) as u8,
            (n >> 48) as u8,
            (n >> 56) as u8,
        ];
        acc.extend_from_slice(&chunk);
        build_output(src, i + 1, acc)
    }
}

/// Writes unsigned 64 bit integers from `src` into `dst` in little-endian
/// order.
///
/// # Panics
///
/// Panics when `dst.len() != 8 * src.len()`.
pub fn write_u64_into(src: &[u64], dst: &mut [u8]) {
    // `core::mem::size_of::<u64>() == 8` (fixed `u64` byte width); the
    // inert "Check types" rebindings had no runtime effect and are
    // dropped. Preserves the original `assert_eq!` length-mismatch panic.
    hax_lib::assert!(src.len() * 8 == dst.len());
    let out = build_output(src, 0, Vec::new());
    dst.copy_from_slice(&out);
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
