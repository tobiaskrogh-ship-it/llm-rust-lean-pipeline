//! Extracted from `core::alloc::Layout::repeat` (src/alloc/layout.rs:360).
//!
//! `Layout` is modeled as `{ size: usize, align: usize }`. The private helpers
//! `pad_to_align`, `repeat_packed`, `from_size_alignment`,
//! `size_rounded_up_to_custom_align`, and `max_size_for_align` are inlined.
//! `from_size_align_unchecked` becomes a plain struct construction;
//! `unchecked_add`/`unchecked_sub` intrinsics become `+`/`-`.

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
/// suitable padding between each. On success returns `(k, offs)` where `k` is
/// the array layout and `offs` is the stride between elements.
pub fn repeat(layout: Layout, n: usize) -> Result<(Layout, usize), LayoutError> {
    let padded = pad_to_align(layout);
    if let Ok(repeated) = repeat_packed(padded, n) {
        Ok((repeated, padded.size()))
    } else {
        Err(LayoutError)
    }
}

// Inlined from `Layout::pad_to_align` (src/alloc/layout.rs:320).
fn pad_to_align(layout: Layout) -> Layout {
    let new_size = size_rounded_up_to_custom_align(layout.size, layout.align);
    Layout { size: new_size, align: layout.align }
}

// Inlined from `Layout::repeat_packed` (src/alloc/layout.rs:448).
fn repeat_packed(layout: Layout, n: usize) -> Result<Layout, LayoutError> {
    if let Some(size) = layout.size.checked_mul(n) {
        from_size_alignment(size, layout.align)
    } else {
        Err(LayoutError)
    }
}

// Inlined from `Layout::from_size_alignment` (src/alloc/layout.rs:101).
fn from_size_alignment(size: usize, align: usize) -> Result<Layout, LayoutError> {
    if size > max_size_for_align(align) {
        return Err(LayoutError);
    }
    Ok(Layout { size, align })
}

// Inlined from `Layout::size_rounded_up_to_custom_align` (src/alloc/layout.rs:285).
fn size_rounded_up_to_custom_align(size: usize, align: usize) -> usize {
    let align_m1 = align - 1;
    (size + align_m1) & !align_m1
}

// Inlined from `Layout::max_size_for_align` (src/alloc/layout.rs:78).
fn max_size_for_align(align: usize) -> usize {
    (isize::MAX as usize + 1) - align
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from the doc-test of `Layout::repeat`. The source builds
    // layouts with `Layout::from_size_align(_, _)`; the equivalent valid
    // `Layout` values are constructed directly here.
    #[test]
    fn doc_example() {
        // All rust types have a size that's a multiple of their alignment.
        let normal = Layout { size: 12, align: 4 };
        let repeated = repeat(normal, 3).unwrap();
        assert_eq!(repeated, (Layout { size: 36, align: 4 }, 12));

        // But you can manually make layouts which don't meet that rule.
        let padding_needed = Layout { size: 6, align: 4 };
        let repeated = repeat(padding_needed, 3).unwrap();
        assert_eq!(repeated, (Layout { size: 24, align: 4 }, 8));
    }

    // Transferred from the `repeat` assertions of
    // `tests/alloc.rs::layout_errors` (`Layout::new::<[u8; 2]>()` => size 2,
    // align 1).
    #[test]
    fn layout_errors() {
        let layout = Layout { size: 2, align: 1 };
        let size = layout.size();
        let size_max = isize::MAX as usize;
        let align_max = size_max / size;

        assert!(repeat(layout, align_max).is_ok());
        assert!(repeat(layout, align_max + 1).is_err());
    }

    // ---- Property-based tests -------------------------------------------
    //
    // Preconditions respected by every generated input: `align` is a
    // power of two with `align >= 1` (a `Layout` invariant), and the
    // inlined `size + (align - 1)` in `size_rounded_up_to_custom_align`
    // must not overflow `usize`. Sizes are kept `<= isize::MAX as usize`
    // and alignments `<= 1 << 30`, so `size + align - 1 < usize::MAX`.

    const ALIGNS: [usize; 7] = [1, 2, 4, 8, 16, 4096, 1 << 30];

    fn sizes() -> [usize; 12] {
        let imax = isize::MAX as usize;
        [0, 1, 2, 3, 5, 6, 7, 8, 13, 4097, imax / 2, imax]
    }

    fn ns() -> [usize; 9] {
        let imax = isize::MAX as usize;
        [0, 1, 2, 3, 7, 1 << 20, imax, imax + 1, usize::MAX]
    }

    // Smallest multiple of `align` that is `>= size`, computed via
    // remainder/division rather than the implementation's bitmask trick,
    // so it is an *independent* oracle for the padded element stride.
    fn round_up(size: usize, align: usize) -> usize {
        let r = size % align;
        if r == 0 { size } else { size + (align - r) }
    }

    // Postcondition on the returned stride (second tuple component): it is
    // the element size padded up to `align` — a multiple of `align`, at
    // least `size`, with a gap strictly smaller than `align`. This is the
    // "suitable padding between each" clause of the contract. A buggy
    // implementation that under-pads, over-pads, or misaligns the stride
    // would be caught here.
    #[test]
    fn prop_stride_is_correct_padding() {
        for &align in &ALIGNS {
            for size in sizes() {
                for n in ns() {
                    let layout = Layout { size, align };
                    if let Ok((_, offs)) = repeat(layout, n) {
                        assert_eq!(offs % align, 0, "stride not a multiple of align");
                        assert!(offs >= size, "stride smaller than element size");
                        assert!(offs - size < align, "stride over-padded");
                    }
                }
            }
        }
    }

    // Postcondition relating the array layout to the stride: the array
    // size is exactly `n` strides, and the input alignment is preserved.
    // Independent of `prop_stride_is_correct_padding` (which pins the
    // stride value itself): an implementation could return a correct
    // stride yet a wrong total size, or drop the alignment.
    #[test]
    fn prop_array_size_is_stride_times_n() {
        for &align in &ALIGNS {
            for size in sizes() {
                for n in ns() {
                    let layout = Layout { size, align };
                    if let Ok((arr, offs)) = repeat(layout, n) {
                        assert_eq!(arr.align(), align, "alignment not preserved");
                        let expected = offs
                            .checked_mul(n)
                            .expect("success implies stride * n does not overflow");
                        assert_eq!(arr.size(), expected, "array size != stride * n");
                    }
                }
            }
        }
    }

    // Failure condition: `repeat` succeeds exactly when the padded stride
    // times `n` neither overflows `usize` nor exceeds
    // `max_size_for_align(align) = (isize::MAX as usize + 1) - align`.
    // `round_up` is an independent reimplementation of the padding, so
    // this pins the precise Ok/Err boundary on its own.
    #[test]
    fn prop_success_iff_fits() {
        let mut saw_ok = false;
        let mut saw_err = false;
        for &align in &ALIGNS {
            for size in sizes() {
                for n in ns() {
                    let layout = Layout { size, align };
                    let stride = round_up(size, align);
                    let max = (isize::MAX as usize + 1) - align;
                    let should_fit = match stride.checked_mul(n) {
                        Some(total) => total <= max,
                        None => false,
                    };
                    let got = repeat(layout, n);
                    assert_eq!(
                        got.is_ok(),
                        should_fit,
                        "Ok/Err boundary mismatch for size={size}, align={align}, n={n}"
                    );
                    if should_fit {
                        saw_ok = true;
                    } else {
                        saw_err = true;
                    }
                }
            }
        }
        // Guard against the input grid degenerating to a single branch.
        assert!(saw_ok && saw_err, "inputs must exercise both Ok and Err");
    }
}
