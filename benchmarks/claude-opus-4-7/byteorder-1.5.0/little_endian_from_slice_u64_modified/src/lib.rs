//! Extracted from `byteorder` 1.5.0:
//! `impl ByteOrder for LittleEndian { fn from_slice_u64(numbers: &mut [u64]) { .. } }`
//! at src/lib.rs:2262.
//!
//! `LittleEndian` is a zero-sized marker type in the source, so the `&self`
//! receiver is dropped here and the method is exposed as a free function.

/// Byte-swap a `u64` (little-endian conversion on a big-endian host).
///
/// Inlined replacement for `u64::to_le`: the method extracts to
/// `core_models.num.Impl_*.to_le`, which the Hax Lean prelude does not
/// define (`lake build` would fail with an `Unknown identifier`). The
/// shift/mask form uses only `&`, `<<`, `>>`, `|` over `u64`, all of
/// which Hax models. Inside the `cfg!(target_endian = "big")` branch the
/// host is big-endian, where `u64::to_le()` is exactly
/// `u64::swap_bytes()`, so this substitution is semantics-preserving.
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
// (cf. `rewrite_patterns/for_loop_over_slice_to_recursion.rs`). `Vec::push`
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

/// Converts the given slice of unsigned 64 bit integers to little endian.
///
/// If the host platform is already little endian, this is a no-op.
//
// The original body was `for n in numbers { *n = n.to_le(); }`. Two
// Hax issues had to be removed:
//   1. `for n in numbers` over `&mut [u64]` desugars to
//      `IntoIterator::into_iter` + `Iterator::next`, extracted as
//      unmodeled `core_models.iter.*` symbols.
//   2. In-place element assignment `*n = v` (i.e. `numbers[i] = v`) on a
//      `&mut [u64]` slice extracts to `rust_primitives.hax.
//      monomorphized_update_at.update_at_usize`, which the Hax prelude
//      types ONLY for `RustArray`, not `RustSlice`. The prelude models
//      NO slice-element-set operation at all.
// Fix: build the fully byte-swapped buffer in a fresh `Vec<u64>`
// (recursion + `extend_from_slice`, both modeled) and write it back
// with `<[u64]>::copy_from_slice`, which IS modeled
// (`core_models.slice.Impl.copy_from_slice`). The signature stays
// `&mut [u64]` (pinned by tests, which pass `&mut [u64]` / `&mut Vec`);
// the in-place mutation now goes through a modeled whole-slice copy
// instead of an unmodeled per-element slice store. `copy_from_slice`
// requires equal lengths, which holds by construction (`build_swapped`
// emits exactly one element per input index), so the empty-slice and
// length-preservation tests still pass.
#[inline]
pub fn from_slice_u64(numbers: &mut [u64]) {
    if cfg!(target_endian = "big") {
        let swapped = build_swapped(numbers, 0, Vec::new());
        numbers.copy_from_slice(&swapped);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from the doc-test on the `ByteOrder::from_slice_u64`
    // trait method (src/lib.rs:1653-1659), monomorphized to the
    // `LittleEndian` impl: `BigEndian::from_slice_u64` -> local
    // `from_slice_u64`, and `to_be` -> `to_le`.
    #[test]
    fn doctest_little_endian() {
        let mut numbers = [5, 65000];
        from_slice_u64(&mut numbers);
        assert_eq!(numbers, [5u64.to_le(), 65000u64.to_le()]);
    }

    // Simple deterministic xorshift PRNG so the property is exercised over
    // many inputs without pulling in a proptest dependency.
    fn next_u64(state: &mut u64) -> u64 {
        let mut x = *state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        *state = x;
        x
    }

    // POSTCONDITION (core contract clause): after the call, every element
    // equals the original value of that element mapped through `to_le()`.
    // This fully characterises the function: it maps each element through
    // `to_le` and changes nothing else (length, order, untouched elements).
    //
    // A buggy implementation that byte-swaps unconditionally, reverses or
    // permutes the slice, zeroes/overwrites elements, or processes the
    // wrong number of elements would be caught.
    #[test]
    fn prop_postcondition_each_element_mapped_through_to_le() {
        let mut state: u64 = 0x9E3779B97F4A7C15;
        // Lengths include the empty-slice edge case (must not panic / no-op).
        for &len in &[0usize, 1, 2, 3, 7, 16, 64] {
            for _ in 0..256 {
                let mut numbers: Vec<u64> = (0..len).map(|_| next_u64(&mut state)).collect();
                // Seed in some boundary values among the random data.
                if len >= 2 {
                    numbers[0] = 0;
                    numbers[len - 1] = u64::MAX;
                }
                let original = numbers.clone();

                from_slice_u64(&mut numbers);

                assert_eq!(numbers.len(), original.len());
                for i in 0..original.len() {
                    assert_eq!(numbers[i], original[i].to_le());
                }
            }
        }
    }

    // POSTCONDITION at value boundaries: explicit check that the per-element
    // mapping holds for extreme and structured bit patterns, not just the
    // PRNG-generated values.
    #[test]
    fn prop_postcondition_boundary_values() {
        let mut numbers = [
            0u64,
            u64::MAX,
            1,
            u64::MAX - 1,
            0x00FF_00FF_00FF_00FF,
            0xFF00_FF00_FF00_FF00,
            0x0123_4567_89AB_CDEF,
        ];
        let original = numbers;

        from_slice_u64(&mut numbers);

        for i in 0..original.len() {
            assert_eq!(numbers[i], original[i].to_le());
        }
    }
}
