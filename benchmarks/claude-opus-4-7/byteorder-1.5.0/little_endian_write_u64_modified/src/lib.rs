//! Extracted from `byteorder` 1.5.0:
//! `impl ByteOrder for LittleEndian { fn write_u64(buf: &mut [u8], n: u64) }`
//! at src/lib.rs:2174.
//!
//! The original is an associated function (no `&self` receiver) on the
//! zero-sized marker type `LittleEndian`, so it is rewritten here as a free
//! function with the same signature and body.
//
// Hax-compatibility rewrite notes (driven by `cargo hax into lean` /
// `lake build` against the pinned Hax Lean prelude). This is the
// little-endian mirror of the verified `big_endian_write_u64`
// reference. The original body
//
//     buf[..8].copy_from_slice(&n.to_le_bytes());
//
// bundles three constructs outside the Hax-modeled fragment:
//
//   1. `u64::to_le_bytes` extracts to `core_models.num.Impl_*.to_le_bytes`,
//      undefined in the Hax Lean prelude (`lake build`: Unknown
//      identifier). Replaced by direct little-endian disassembly with
//      `>>` + narrowing `as u8` casts (all modeled) — the write-side
//      little-endian mirror of
//      `rewrite_patterns/to_be_bytes_to_shift_disassembly.rs`.
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
//      and the verified `big_endian_write_u64` reference) by building the
//      full target image in a fresh `Vec<u8>` (index-based tail recursion
//      + `Vec::extend_from_slice` with a *typed* `[u8; 1]` chunk, both
//      modeled) and writing it back with the modeled
//      `<[u8]>::copy_from_slice`. The first 8 bytes are the little-endian
//      encoding of `n`; bytes at index >= 8 are copied unchanged, so
//      `copy_from_slice`'s equal-length requirement holds by construction
//      and the tail-unchanged contract is preserved.
//
// The original `buf[..8]` slice panics when `buf.len() < 8`. That panic
// is preserved by an explicit `hax_lib::assert!(buf.len() >= 8)`, which
// panics in normal builds (proxied to `core::assert!`, so the
// `#[should_panic]` / `catch_unwind` too-small-buffer tests still pass)
// and extracts to the modeled `rust_primitives.hax_lib.assert`.

/// Build the target image of `buf`: bytes `0..8` are `le`, bytes `8..`
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
fn build_output(buf: &[u8], le: &[u8; 8], i: usize, acc: Vec<u8>) -> Vec<u8> {
    if i >= buf.len() {
        acc
    } else {
        let mut acc = acc;
        let byte = if i < 8 { le[i] } else { buf[i] };
        let chunk: [u8; 1] = [byte];
        acc.extend_from_slice(&chunk);
        build_output(buf, le, i + 1, acc)
    }
}

/// Writes an unsigned 64-bit integer `n` to `buf` in little-endian order.
///
/// # Panics
///
/// Panics when `buf.len() < 8`.
#[inline]
pub fn write_u64(buf: &mut [u8], n: u64) {
    // Preserves the original `buf[..8]` out-of-bounds panic when the
    // buffer is shorter than 8 bytes.
    hax_lib::assert!(buf.len() >= 8);
    // Little-endian disassembly: byte 0 is the least significant.
    let le: [u8; 8] = [
        n as u8,
        (n >> 8) as u8,
        (n >> 16) as u8,
        (n >> 24) as u8,
        (n >> 32) as u8,
        (n >> 40) as u8,
        (n >> 48) as u8,
        (n >> 56) as u8,
    ];
    let out = build_output(buf, &le, 0, Vec::new());
    buf.copy_from_slice(&out);
}

#[cfg(test)]
mod tests {
    use super::write_u64;

    // Transferred from the doc-comment on
    // `trait ByteOrder { fn write_u64(...) }` in src/lib.rs:464.
    // The original round-trips through `LittleEndian::read_u64`; since we
    // only extracted the writer, we verify the bytes against
    // `u64::from_le_bytes` (the documented serialization).
    #[test]
    fn doc_example_round_trip() {
        let mut buf = [0; 8];
        write_u64(&mut buf, 1_000_000);
        assert_eq!(1_000_000, u64::from_le_bytes(buf));
    }

    // Transferred from the `too_small!(small_u64, 7, 0, read_u64, write_u64)`
    // expansion at src/lib.rs:3022 — specifically the `write_little_endian`
    // arm (src/lib.rs:2974-2978): writing into a 7-byte buffer must panic.
    #[test]
    #[should_panic]
    fn write_little_endian_too_small() {
        let mut buf = [0; 7];
        write_u64(&mut buf, 0);
    }

    /// A deterministic sweep of `u64` inputs: explicit boundary/structured
    /// values plus a xorshift64 pseudo-random tail. Used to make the
    /// `#[test]` functions below universally-quantified property checks
    /// without pulling in a proptest dependency.
    fn sample_inputs() -> Vec<u64> {
        let mut v = vec![
            0,
            1,
            2,
            255,
            256,
            1_000_000,
            0x00FF_00FF_00FF_00FF,
            0xFF00_FF00_FF00_FF00,
            0x0123_4567_89AB_CDEF,
            u64::MAX - 1,
            u64::MAX,
            1 << 7,
            1 << 8,
            1 << 31,
            1 << 32,
            1 << 63,
        ];
        let mut x: u64 = 0x9E37_79B9_7F4A_7C15;
        for _ in 0..256 {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            v.push(x);
        }
        v
    }

    // Postcondition: after `write_u64`, the first eight bytes of `buf` are
    // exactly the little-endian base-256 digits of `n`, i.e.
    // `buf[i] == (n >> (8*i)) & 0xff`. This single property fully pins down
    // the serialization *and* the byte ordering; the round-trip via
    // `u64::from_le_bytes` (see `doc_example_round_trip`) is a derived
    // consequence and is not retested as a separate property.
    #[test]
    fn prop_little_endian_byte_order() {
        for n in sample_inputs() {
            let mut buf = [0u8; 8];
            write_u64(&mut buf, n);
            for i in 0..8 {
                let expected = ((n >> (8 * i)) & 0xff) as u8;
                assert_eq!(
                    buf[i], expected,
                    "byte {i} mismatch for n = {n:#018x}"
                );
            }
        }
    }

    // Independent frame condition: `write_u64` writes *exactly* the first
    // eight bytes and leaves any trailing capacity untouched. A buggy
    // implementation that wrote the whole slice (or wrote at the wrong
    // offset) would still satisfy the byte-order postcondition above but
    // would be caught here, so this claim earns its own test.
    #[test]
    fn prop_only_first_eight_bytes_written() {
        const SENTINEL: u8 = 0xAA;
        for &len in &[8usize, 9, 16, 33, 64] {
            for n in sample_inputs() {
                let mut buf = vec![SENTINEL; len];
                write_u64(&mut buf, n);
                for i in 0..8 {
                    let expected = ((n >> (8 * i)) & 0xff) as u8;
                    assert_eq!(buf[i], expected, "n = {n:#018x}, len = {len}");
                }
                for (j, &b) in buf.iter().enumerate().skip(8) {
                    assert_eq!(
                        b, SENTINEL,
                        "trailing byte {j} modified (n = {n:#018x}, len = {len})"
                    );
                }
            }
        }
    }

    // Failure condition: `write_u64` panics whenever `buf.len() < 8`,
    // for every too-small length and independent of `n`. This generalises
    // the single `write_little_endian_too_small` case (len == 7) over the
    // full range of failing lengths.
    #[test]
    fn prop_panics_when_buffer_too_small() {
        let prev = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let mut failures = Vec::new();
        for len in 0usize..8 {
            for n in [0u64, 1, u64::MAX] {
                let result = std::panic::catch_unwind(move || {
                    let mut buf = vec![0u8; len];
                    write_u64(&mut buf, n);
                });
                if result.is_ok() {
                    failures.push((len, n));
                }
            }
        }
        std::panic::set_hook(prev);
        assert!(
            failures.is_empty(),
            "write_u64 failed to panic for (len, n) = {failures:?}"
        );
    }
}
