//! Extracted from `byteorder` 1.5.0:
//! `impl ByteOrder for BigEndian { fn from_slice_u64(numbers: &mut [u64]) { .. } }`
//!
//! The receiver `BigEndian` is a zero-sized marker type, and the original
//! signature does not take `&self` (the trait method has no receiver). So the
//! free-function form drops nothing structural — we just lift the method body.

/// Byte-swap a `u64` (big-endian conversion on a little-endian host).
///
/// Inlined replacement for `u64::to_be`: the method extracts to
/// `core_models.num.Impl_*.to_be`, which the Hax Lean prelude does not
/// define (`lake build` would fail with an `Unknown identifier`). The
/// shift/mask form uses only `&`, `<<`, `>>`, `|` over `u64`, all of
/// which Hax models. Equivalent to `u64::swap_bytes`, which is what
/// `to_be()` reduces to inside the `target_endian = "little"` branch.
#[inline]
fn swap_bytes_u64(x: u64) -> u64 {
    ((x & 0x0000_0000_0000_00FF) << 56)
        | ((x & 0x0000_0000_0000_FF00) << 40)
        | ((x & 0x0000_0000_00FF_0000) << 24)
        | ((x & 0x0000_0000_FF00_0000) << 8)
        | ((x & 0x0000_00FF_0000_0000) >> 8)
        | ((x & 0x0000_FF00_0000_0000) >> 24)
        | ((x & 0x00FF_0000_0000_0000) >> 40)
        | ((x & 0xFF00_0000_0000_0000) >> 56)
}

/// Build the byte-swapped image of `numbers[i..]`, appended to `acc`.
//
// Index-based tail recursion over an immutable `&[u64]`, accumulating
// into a `Vec<u64>` passed by value. This is the proven Hax-compatible
// shape for "transform each element of a slice into a new buffer"
// (cf. `rewrite_patterns/for_loop_over_slice_to_recursion.rs` and the
// verified `rolling_max` reference). `Vec::push`
// (`alloc.vec.Impl_1.push`) is undefined in the Hax prelude, so the
// element is appended via `Vec::extend_from_slice`
// (`alloc.vec.Impl_2.extend_from_slice`, modeled) using a *typed*
// `let chunk: [u64; 1]` binding so the array size appears in the type
// ascription and Hax can resolve `unsize`'s `RustArray` size parameter
// (cf. `rewrite_patterns/vec_push_to_extend_from_slice_typed_chunk.rs`).
// Decreasing measure: `numbers.len() - i`. Extracted as
// `partial_fixpoint`; the proof stage handles it via `Nat.strongRecOn`.
fn build_swapped(numbers: &[u64], i: usize, acc: Vec<u64>) -> Vec<u64> {
    if i >= numbers.len() {
        acc
    } else {
        let mut acc = acc;
        let chunk: [u64; 1] = [swap_bytes_u64(numbers[i])];
        acc.extend_from_slice(&chunk);
        build_swapped(numbers, i + 1, acc)
    }
}

/// Converts the given slice of unsigned 64 bit integers to big endian.
///
/// If the host platform is already big endian, this is a no-op.
//
// The original body was `for n in numbers { *n = n.to_be(); }`. Two
// Hax issues had to be removed:
//   1. `for n in numbers` over `&mut [u64]` desugars to
//      `IntoIterator::into_iter` + `Iterator::next`, extracted as
//      unmodeled `core_models.iter.*` symbols.
//   2. In-place element assignment `numbers[i] = v` on a `&mut [u64]`
//      slice extracts to `rust_primitives.hax.monomorphized_update_at.
//      update_at_usize`, which the Hax prelude types ONLY for
//      `RustArray`, not `RustSlice` (`lake build` error: "argument
//      `numbers` has type `RustSlice u64` but is expected to have type
//      `RustArray ?m ?m`"). The prelude models NO slice-element-set
//      operation at all.
// Fix: build the fully byte-swapped buffer in a fresh `Vec<u64>`
// (recursion + `extend_from_slice`, both modeled) and write it back
// with `<[u64]>::copy_from_slice`, which IS modeled
// (`core_models.slice.Impl.copy_from_slice`). The signature stays
// `&mut [u64]` (pinned by tests, which pass `&mut Vec<u64>`); the in
// place mutation now goes through a modeled whole-slice copy instead of
// an unmodeled per-element slice store. `copy_from_slice` requires
// equal lengths, which holds by construction (`build_swapped` emits
// exactly one element per input index), so the empty-slice and
// length-preservation tests still pass.
#[inline]
pub fn from_slice_u64(numbers: &mut [u64]) {
    if cfg!(target_endian = "little") {
        let swapped = build_swapped(numbers, 0, Vec::new());
        numbers.copy_from_slice(&swapped);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from the doc-test on `ByteOrder::from_slice_u64` in
    // byteorder-1.5.0/src/lib.rs lines 1653-1659.
    #[test]
    fn doc_example_big_endian() {
        let mut numbers = [5, 65000];
        from_slice_u64(&mut numbers);
        assert_eq!(numbers, [5u64.to_be(), 65000u64.to_be()]);
    }

    /// Deterministic input generator: a hand-picked set of edge values
    /// followed by a linear-congruential sweep. No external proptest crate
    /// is available, so this stands in for randomized inputs.
    fn sample_values() -> Vec<u64> {
        let mut v = vec![
            0,
            1,
            u64::MAX,
            0xFF,
            0xFF00,
            0x00FF_00FF_00FF_00FF,
            0x0123_4567_89AB_CDEF,
            0x8000_0000_0000_0000,
            0xDEAD_BEEF_CAFE_BABE,
            0x1122_3344_5566_7788,
        ];
        // LCG (Numerical Recipes constants) for a reproducible sweep.
        let mut s: u64 = 0x9E37_79B9_7F4A_7C15;
        for _ in 0..256 {
            s = s
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            v.push(s);
        }
        v
    }

    // POSTCONDITION (core contract). The documented behaviour is "convert
    // each integer to big endian". Rust's `u64::to_be` is exactly that
    // conversion, and the spec is platform-independent: on a big-endian
    // host `to_be` is the identity, which matches the function's no-op
    // branch there. So on every platform the result at each index must
    // equal the original element's `to_be()`.
    //
    // This single property also pins down two structural claims:
    //   * elements are transformed in place at their own index (no
    //     reordering) — `to_be` is a bijection, so any permutation of the
    //     non-palindromic sample values would break index-wise equality;
    //   * the length is unchanged — we compare element-wise across the
    //     whole original length.
    #[test]
    fn prop_each_element_becomes_big_endian() {
        let values = sample_values();

        // Exercise a range of slice lengths, including length 1, and a
        // window that slides through the sample data so every value is
        // covered in multiple positions.
        for len in [1usize, 2, 3, 5, 8, 13, 32] {
            for start in 0..(values.len() - len) {
                let original: Vec<u64> = values[start..start + len].to_vec();
                let mut numbers = original.clone();

                from_slice_u64(&mut numbers);

                assert_eq!(
                    numbers.len(),
                    original.len(),
                    "length must be preserved"
                );
                for i in 0..original.len() {
                    assert_eq!(
                        numbers[i],
                        original[i].to_be(),
                        "element {i} (orig {:#018x}) not converted to big endian",
                        original[i]
                    );
                }
            }
        }
    }

    // FAILURE CONDITION / EDGE CASE. The function has no preconditions and
    // no failure modes (return type is `()`). The only structural edge
    // case is the empty slice: the loop body never runs, so the call must
    // complete without panicking and leave the (empty) slice untouched.
    #[test]
    fn prop_empty_slice_is_total_and_noop() {
        let mut numbers: [u64; 0] = [];
        from_slice_u64(&mut numbers);
        assert_eq!(numbers, [] as [u64; 0]);

        let mut v: Vec<u64> = Vec::new();
        from_slice_u64(&mut v);
        assert!(v.is_empty());
    }
}
