//! Extracted from `byteorder` 1.5.0: `BigEndian::write_u64`.
//!
//! Source: src/lib.rs:1987-1990, inside `impl ByteOrder for BigEndian`.
//! `BigEndian` is a zero-sized marker type and `write_u64` takes no `&self`
//! receiver, so the function is rewritten as a free `pub fn` with identical
//! signature and body.
//
// Hax-compatibility rewrite notes (driven by `cargo hax into lean` /
// `lake build` against the pinned Hax Lean prelude). The original body
//
//     buf[..8].copy_from_slice(&n.to_be_bytes());
//
// bundles three constructs outside the Hax-modeled fragment:
//
//   1. `u64::to_be_bytes` extracts to `core_models.num.Impl_*.to_be_bytes`,
//      undefined in the Hax Lean prelude (`lake build`: Unknown
//      identifier). Replaced by direct big-endian disassembly with `>>`
//      + narrowing `as u8` casts (all modeled) — the write-side mirror
//      of `rewrite_patterns/from_be_bytes_slice_try_into.rs`.
//
//   2. Range slicing `buf[..8]` is outside the modeled fragment (only
//      the single-element partial index `_[_]?` is modeled), cf.
//      `rewrite_patterns/from_be_bytes_slice_try_into.rs`.
//
//   3. Even with the bytes in hand, an in-place per-element store into a
//      `&mut [u8]` slice (`buf[i] = ...`) extracts to
//      `rust_primitives.hax.monomorphized_update_at.update_at_usize`,
//      which the prelude types ONLY for `RustArray`, never `RustSlice`.
//      Fixed (per `rewrite_patterns/slice_element_store_to_copy_from_slice.rs`
//      and the verified `big_endian_from_slice_u64` / `read_u64_into`
//      references) by building the full target image in a fresh
//      `Vec<u8>` (index-based tail recursion + `Vec::extend_from_slice`
//      with a *typed* `[u8; 1]` chunk, both modeled) and writing it back
//      with the modeled `<[u8]>::copy_from_slice`. The first 8 bytes are
//      the big-endian encoding of `n`; bytes at index >= 8 are copied
//      unchanged, so `copy_from_slice`'s equal-length requirement holds
//      by construction and the tail-unchanged contract is preserved.
//
// The original `buf[..8]` slice panics when `buf.len() < 8`. That panic
// is preserved by an explicit `hax_lib::assert!(buf.len() >= 8)`, which
// panics in normal builds (proxied to `core::assert!`, so the
// `#[should_panic]` / `catch_unwind` too-small-buffer tests still pass)
// and extracts to the modeled `rust_primitives.hax_lib.assert`.

/// Build the target image of `buf`: bytes `0..8` are `be`, bytes `8..`
/// are copied unchanged from `buf`, appended to `acc`.
//
// Index-based tail recursion (preferred over a `while` loop per the
// recursion-preference rule); decreasing measure `buf.len() - i`.
// `Vec::push` (`alloc.vec.Impl_1.push`) is undefined in the Hax prelude,
// so the element is appended via `Vec::extend_from_slice`
// (`alloc.vec.Impl_2.extend_from_slice`, modeled) using a *typed*
// `let chunk: [u8; 1]` binding so the array size appears in the type
// ascription and Hax can resolve `unsize`'s `RustArray` size parameter
// (cf. `rewrite_patterns/vec_push_to_extend_from_slice_typed_chunk.rs`).
fn build_output(buf: &[u8], be: &[u8; 8], i: usize, acc: Vec<u8>) -> Vec<u8> {
    if i >= buf.len() {
        acc
    } else {
        let mut acc = acc;
        let byte = if i < 8 { be[i] } else { buf[i] };
        let chunk: [u8; 1] = [byte];
        acc.extend_from_slice(&chunk);
        build_output(buf, be, i + 1, acc)
    }
}

#[inline]
pub fn write_u64(buf: &mut [u8], n: u64) {
    // Preserves the original `buf[..8]` out-of-bounds panic when the
    // buffer is shorter than 8 bytes.
    hax_lib::assert!(buf.len() >= 8);
    // Big-endian disassembly: byte 0 is the most significant. Mirror of
    // the widening assembly in `from_be_bytes_slice_try_into.rs`.
    let be: [u8; 8] = [
        (n >> 56) as u8,
        (n >> 48) as u8,
        (n >> 40) as u8,
        (n >> 32) as u8,
        (n >> 24) as u8,
        (n >> 16) as u8,
        (n >> 8) as u8,
        n as u8,
    ];
    let out = build_output(buf, &be, 0, Vec::new());
    buf.copy_from_slice(&out);
}

#[cfg(test)]
mod tests {
    use super::write_u64;
    use std::panic::{self, AssertUnwindSafe};

    // Transferred from src/lib.rs: `too_small!(small_u64, 7, 0, read_u64, write_u64);`
    // expansion of the `write_big_endian` arm. The `too_small!` macro generates
    // a `#[should_panic]` test that calls `BigEndian::write_u64(&mut [0; 7], 0)`
    // to ensure the function panics when the buffer is too small.
    #[test]
    #[should_panic]
    fn write_big_endian() {
        let mut buf = [0; 7];
        write_u64(&mut buf, 0);
    }

    // Deterministic sample of `n` values: edge cases plus an xorshift sequence
    // so every byte lane takes many distinct values.
    fn sample_values() -> Vec<u64> {
        let mut vs = vec![
            0,
            1,
            u64::MAX,
            0x0102_0304_0506_0708, // all 8 bytes distinct: distinguishes byte order
            0xFEDC_BA98_7654_3210,
            0x00FF_00FF_00FF_00FF,
            0xFF00_0000_0000_0000, // only the most-significant byte set
            0x0000_0000_0000_00FF, // only the least-significant byte set
        ];
        let mut x: u64 = 0x9E37_79B9_7F4A_7C15;
        for _ in 0..64 {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            vs.push(x);
        }
        vs
    }

    // POSTCONDITION (value + endianness): for any `n` and any buffer of length
    // >= 8, the first 8 bytes are the big-endian encoding of `n`, i.e. byte `i`
    // is the `(7 - i)`-th byte counting from the least-significant end. Computed
    // with explicit shifts so the test does not just restate `n.to_be_bytes()`;
    // a little-endian (or otherwise byte-permuted) implementation fails here.
    #[test]
    fn prop_big_endian_byte_order() {
        for &n in &sample_values() {
            for len in 8..=16usize {
                let mut buf = vec![0xAAu8; len];
                write_u64(&mut buf, n);
                for i in 0..8 {
                    let expected = (n >> (8 * (7 - i as u32))) as u8;
                    assert_eq!(
                        buf[i], expected,
                        "n={n:#018x}, len={len}, byte {i}"
                    );
                }
            }
        }
    }

    // POSTCONDITION (writes exactly 8 bytes): bytes at index >= 8 are left
    // untouched. The buffer is pre-filled with a sentinel that never appears in
    // the big-endian encoding region under test, so a write that spills past
    // index 8 (or clears the whole buffer) is caught.
    #[test]
    fn prop_tail_unchanged() {
        const SENTINEL: u8 = 0x5A;
        for &n in &sample_values() {
            for len in 9..=24usize {
                let mut buf = vec![SENTINEL; len];
                write_u64(&mut buf, n);
                for i in 8..len {
                    assert_eq!(
                        buf[i], SENTINEL,
                        "n={n:#018x}, len={len}, tail byte {i} modified"
                    );
                }
            }
        }
    }

    // FAILURE CONDITION (precondition violation): every buffer shorter than 8
    // bytes causes a panic, regardless of `n`. Generalizes the single len==7
    // case in `write_big_endian` to all sub-minimal lengths.
    #[test]
    fn prop_panics_when_buffer_too_small() {
        for len in 0..8usize {
            for &n in &[0u64, 1, u64::MAX, 0x0102_0304_0506_0708] {
                let mut buf = vec![0u8; len];
                let result =
                    panic::catch_unwind(AssertUnwindSafe(|| write_u64(&mut buf, n)));
                assert!(
                    result.is_err(),
                    "expected panic for buffer len {len} with n={n:#018x}"
                );
            }
        }
    }
}
