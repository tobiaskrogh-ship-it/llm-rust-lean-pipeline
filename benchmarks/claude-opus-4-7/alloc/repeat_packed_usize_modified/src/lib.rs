//! Extracted from `core::alloc::Layout::repeat_packed` (src/alloc/layout.rs:448).
//!
//! `Layout` is modeled as `{ size: usize, align: usize }`. The private helpers
//! `from_size_alignment` and `max_size_for_align` are inlined; `unchecked_sub`
//! becomes `-`.

/// Layout of a block of memory: a size and a power-of-two alignment.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Layout {
    size: usize,
    align: usize,
}

impl Layout {
    pub fn size(&self) -> usize {
        self.size
    }
    pub fn align(&self) -> usize {
        self.align
    }
}

/// Returned on arithmetic overflow.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LayoutError;

/// Creates a layout describing the record for `n` instances of `layout`, with
/// no padding between each instance.
pub fn repeat_packed(layout: Layout, n: usize) -> Result<Layout, LayoutError> {
    // `usize::checked_mul` extracts to the unmodeled
    // `core_models.<int>.Impl.checked_mul` identifier in the Hax Lean prelude
    // (see rewrite_patterns/checked_wrapping_to_bare_arith.rs). Replace with
    // an explicit overflow check: `size * n` fits in `usize` iff `n == 0` or
    // `size <= usize::MAX / n`. `usize::MAX` is itself unmodeled (an
    // associated constant — see rewrite_patterns/primitive_int_assoc_const.rs);
    // inline the 64-bit literal `2^64 - 1 = 18_446_744_073_709_551_615`.
    //
    // Use `if`/`else` rather than `n != 0 && size > usize::MAX / n` so the
    // guard on `/ n` survives Hax's eager `do`-block extraction
    // (see rewrite_patterns/short_circuit_and_with_partial_op.rs).
    if n == 0 {
        from_size_alignment(0, layout.align)
    } else if layout.size > 18_446_744_073_709_551_615usize / n {
        Err(LayoutError)
    } else {
        from_size_alignment(layout.size * n, layout.align)
    }
}

// Inlined from `Layout::from_size_alignment` (src/alloc/layout.rs:101).
fn from_size_alignment(size: usize, align: usize) -> Result<Layout, LayoutError> {
    if size > max_size_for_align(align) {
        return Err(LayoutError);
    }
    Ok(Layout { size, align })
}

// Inlined from `Layout::max_size_for_align` (src/alloc/layout.rs:78).
// `isize::MAX as usize` would reference the unmodeled
// `core_models.num.Impl_<N>.MAX` associated constant in the Hax Lean prelude
// (see rewrite_patterns/primitive_int_assoc_const.rs). Inline the literal:
// `isize::MAX = 2^63 - 1`, so `isize::MAX as usize + 1 = 2^63 = 9_223_372_036_854_775_808`.
fn max_size_for_align(align: usize) -> usize {
    9_223_372_036_854_775_808usize - align
}

#[cfg(test)]
mod tests {
    use super::*;

    // Representative input grids. The pipeline turns each assertion into a
    // proof obligation, so the suite is kept deliberately small: one test per
    // independent contract clause, each driven over edge + bulk values.

    const SIZES: &[usize] = &[0, 1, 2, 6, 17, 1024, 65536];
    const ALIGNS: &[usize] = &[1, 2, 4, 8, 4096];
    const NS: &[usize] = &[0, 1, 2, 3, 100, 50_000];

    // Postcondition (success case): when `repeat_packed` returns `Ok`, the
    // result is *packed* (size is exactly `size * n`, no inter-instance
    // padding) and the original alignment is carried through unchanged.
    // These are two independent claims: a buggy impl could pad the size while
    // keeping align, or keep size while resetting align.
    #[test]
    fn ok_is_packed_and_preserves_align() {
        for &size in SIZES {
            for &align in ALIGNS {
                for &n in NS {
                    let layout = Layout { size, align };
                    // These grids never overflow `usize` and stay far below
                    // the isize size limit, so the call must succeed.
                    let out = repeat_packed(layout, n)
                        .expect("in-bounds inputs must succeed");
                    assert_eq!(out.size(), size * n, "packed size");
                    assert_eq!(out.align(), align, "alignment preserved");
                }
            }
        }
    }

    // Precondition / failure boundary: `from_size_alignment` accepts a record
    // exactly up to `max_size_for_align(align) == (isize::MAX + 1) - align`
    // and rejects anything larger. This pins down both directions of the
    // threshold (no spurious error at/under the limit; `Err` just past it),
    // generalising the original `layout_errors` case over many aligns/sizes.
    #[test]
    fn isize_size_limit_boundary() {
        for &align in ALIGNS {
            let max = (isize::MAX as usize + 1) - align;
            for &size in &[1usize, 2, 3, 7] {
                let layout = Layout { size, align };
                let n_ok = max / size; // n_ok * size <= max
                let n_bad = n_ok + 1; // n_ok*size + size  > max, no usize overflow
                assert!(
                    repeat_packed(layout, n_ok).is_ok(),
                    "product <= limit must be Ok (size={size}, align={align})"
                );
                assert!(
                    repeat_packed(layout, n_bad).is_err(),
                    "product > limit must be Err (size={size}, align={align})"
                );
            }
        }
    }

    // Failure condition: when `size * n` overflows `usize`, the checked
    // multiplication is `None` and `repeat_packed` returns `Err` (it must not
    // wrap around and report a bogus small layout).
    #[test]
    fn mul_overflow_is_err() {
        for &size in &[usize::MAX, usize::MAX / 2 + 1, usize::MAX - 1] {
            for &n in &[2usize, 3, 1000, usize::MAX] {
                // size > usize::MAX/2 and n >= 2  =>  size * n overflows.
                let layout = Layout { size, align: 1 };
                assert!(
                    repeat_packed(layout, n).is_err(),
                    "overflowing size*n must be Err (size={size}, n={n})"
                );
            }
        }
        // An explicit overflowing pair: 2^40 * 2^40 = 2^80 > usize::MAX.
        let layout = Layout { size: 1usize << 40, align: 8 };
        assert!(repeat_packed(layout, 1usize << 40).is_err());
    }
}
