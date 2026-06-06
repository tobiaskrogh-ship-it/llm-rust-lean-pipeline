//! Extracted from `core::alloc::Layout::extend` (src/alloc/layout.rs:417).
//!
//! `Layout` is modeled as `{ size: usize, align: usize }`. `Alignment::max`
//! becomes `usize::max`. The private helpers `size_rounded_up_to_custom_align`,
//! `from_size_alignment`, and `max_size_for_align` are inlined. The
//! `unchecked_add`/`unchecked_sub` intrinsics cannot overflow given the
//! documented `Layout` invariants, so they become `+`/`-`.

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

/// Creates a layout describing the record for `layout` followed by `next`,
/// including necessary alignment padding but no trailing padding. Returns
/// `Ok((k, offset))` where `offset` is the start of `next` within the record.
pub fn extend(layout: Layout, next: Layout) -> Result<(Layout, usize), LayoutError> {
    // `usize::max` (`Ord::max`) has no Hax model
    // (`core_models.cmp.Ord.max` is undefined). Inline the comparison.
    // Rust's `a.max(b)` returns the second argument on a tie, so use
    // `>` (not `>=`) to match exact semantics.
    let new_align = if layout.align > next.align {
        layout.align
    } else {
        next.align
    };
    let offset = size_rounded_up_to_custom_align(layout.size, next.align);

    // `offset` is at most `isize::MAX + 1` and `next.size` is at most
    // `isize::MAX`, so the largest possible `new_size` is `usize::MAX` and
    // cannot overflow.
    let new_size = offset + next.size;

    if let Ok(layout) = from_size_alignment(new_size, new_align) {
        Ok((layout, offset))
    } else {
        Err(LayoutError)
    }
}

// Inlined from `Layout::size_rounded_up_to_custom_align` (src/alloc/layout.rs:285).
fn size_rounded_up_to_custom_align(size: usize, align: usize) -> usize {
    let align_m1 = align - 1;
    (size + align_m1) & !align_m1
}

// Inlined from `Layout::from_size_alignment` (src/alloc/layout.rs:101).
fn from_size_alignment(size: usize, align: usize) -> Result<Layout, LayoutError> {
    if size > max_size_for_align(align) {
        return Err(LayoutError);
    }
    Ok(Layout { size, align })
}

// Inlined from `Layout::max_size_for_align` (src/alloc/layout.rs:78).
fn max_size_for_align(align: usize) -> usize {
    // `isize::MAX` (a primitive-int associated const) has no Hax model
    // (`core_models.num.Impl_5.MAX` is undefined). On a 64-bit target
    // `isize::MAX as usize + 1 == 2^63 == 9223372036854775808`; inline
    // that literal directly.
    9_223_372_036_854_775_808usize - align
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from the `extend` assertion of
    // `tests/alloc.rs::layout_errors` (`Layout::new::<[u8; 2]>()` => size 2,
    // align 1; `next` is size `isize::MAX`, align 1).
    #[test]
    fn layout_errors() {
        let layout = Layout { size: 2, align: 1 };
        let size_max = isize::MAX as usize;
        let next = Layout { size: size_max, align: 1 };
        assert!(extend(layout, next).is_err());
    }

    // Mirrors the `repr_c`-style usage shown in the `extend` doc comment
    // (the doc-test itself uses `Vec`/`Layout::new::<T>()` and so cannot be
    // transferred without `alloc`/intrinsics; this checks the same arithmetic).
    #[test]
    fn extends_with_alignment_padding() {
        let a = Layout { size: 8, align: 8 };
        let b = Layout { size: 4, align: 4 };
        let (combined, offset) = extend(a, b).unwrap();
        assert_eq!(offset, 8);
        assert_eq!(combined, Layout { size: 12, align: 8 });

        // Padding is inserted before `next` so it is properly aligned.
        let a = Layout { size: 3, align: 1 };
        let b = Layout { size: 2, align: 4 };
        let (combined, offset) = extend(a, b).unwrap();
        assert_eq!(offset, 4);
        assert_eq!(combined, Layout { size: 6, align: 4 });
    }

    // ---- Property-based tests over the `extend` contract ----------------
    //
    // Preconditions for a valid call: `align` is a power of two with
    // `1 <= align <= isize::MAX + 1`, and `size <= isize::MAX`. The crate
    // header documents that these are exactly the `Layout` invariants the
    // inlined `+`/`-` operations rely on, so every (size, align) pair drawn
    // from the arrays below is a legal input `Layout`.
    const ALIGNS: [usize; 8] = [1, 2, 4, 8, 16, 4096, 1usize << 62, 1usize << 63];
    const SIZES: [usize; 8] = [
        0,
        1,
        3,
        8,
        15,
        4096,
        (isize::MAX as usize) - 4096,
        isize::MAX as usize,
    ];

    // Postcondition: whenever `extend` succeeds, the returned `offset` and
    // combined `Layout` satisfy every clause the contract promises. Each
    // assertion pins down an independent claim:
    //   * `offset` is aligned to `next.align`              (next is aligned)
    //   * `offset >= layout.size`                          (first fits before)
    //   * `offset < layout.size + next.align`              (offset is minimal)
    //   * `combined.align == max(layout.align, next.align)` (alignment rule)
    //   * `combined.size == offset + next.size`             (no trailing pad)
    //   * `combined` is itself a well-formed `Layout`       (valid output)
    #[test]
    fn ok_postconditions() {
        for &la in &ALIGNS {
            for &ls in &SIZES {
                for &na in &ALIGNS {
                    for &ns in &SIZES {
                        let layout = Layout { size: ls, align: la };
                        let next = Layout { size: ns, align: na };
                        if let Ok((combined, offset)) = extend(layout, next) {
                            assert_eq!(
                                offset % na, 0,
                                "offset not aligned: {la} {ls} {na} {ns}"
                            );
                            assert!(
                                offset >= ls,
                                "offset below size: {la} {ls} {na} {ns}"
                            );
                            assert!(
                                offset < ls + na,
                                "offset not minimal: {la} {ls} {na} {ns}"
                            );
                            assert_eq!(
                                combined.align(), la.max(na),
                                "wrong align: {la} {ls} {na} {ns}"
                            );
                            assert_eq!(
                                combined.size(), offset + ns,
                                "wrong size: {la} {ls} {na} {ns}"
                            );
                            assert!(
                                combined.size()
                                    <= (isize::MAX as usize + 1) - combined.align(),
                                "result not a valid layout: {la} {ls} {na} {ns}"
                            );
                        }
                    }
                }
            }
        }
    }

    // Failure condition: `extend` returns `Err` *exactly* when the record
    // does not fit -- i.e. when the padded size of the first layout plus
    // `next.size` exceeds the maximum size allowed for the combined
    // alignment. `offset_ref` is computed with ceiling division instead of
    // the implementation's bit-masking, so it is an independent oracle for
    // the round-up; this test therefore checks the `Ok`/`Err` decision
    // (the `iff`), not just one direction.
    #[test]
    fn err_iff_record_does_not_fit() {
        for &la in &ALIGNS {
            for &ls in &SIZES {
                for &na in &ALIGNS {
                    for &ns in &SIZES {
                        let layout = Layout { size: ls, align: la };
                        let next = Layout { size: ns, align: na };
                        let offset_ref = ls.div_ceil(na) * na;
                        let new_align = la.max(na);
                        let max_size = (isize::MAX as usize + 1) - new_align;
                        let fits = offset_ref + ns <= max_size;
                        assert_eq!(
                            extend(layout, next).is_ok(),
                            fits,
                            "Ok/Err disagreement: {la} {ls} {na} {ns}"
                        );
                    }
                }
            }
        }
    }
}
