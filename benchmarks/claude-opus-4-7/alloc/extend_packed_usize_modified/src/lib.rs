//! Extracted from `core::alloc::Layout::extend_packed` (src/alloc/layout.rs:465).
//!
//! `Layout` is modeled as `{ size: usize, align: usize }`. The private helpers
//! `from_size_alignment` and `max_size_for_align` are inlined. Each `size` is
//! at most `isize::MAX`, so `unchecked_add` cannot overflow and becomes `+`;
//! `unchecked_sub` becomes `-`.

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

/// Creates a layout describing the record for `layout` followed by `next` with
/// no additional padding between the two. The alignment of `next` is ignored.
pub fn extend_packed(layout: Layout, next: Layout) -> Result<Layout, LayoutError> {
    // each `size` is at most `isize::MAX == usize::MAX/2`, so the sum is at
    // most `usize::MAX - 1` and cannot overflow.
    let new_size = layout.size + next.size;
    // The safe constructor enforces that the new size isn't too big for the alignment.
    from_size_alignment(new_size, layout.align)
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
    // `isize::MAX = 2^63 - 1 = 9_223_372_036_854_775_807` (Hax models
    // `isize` as 64-bit). Inlining the literal avoids the missing
    // `core_models.num.Impl_5.MAX` identifier in the Hax Lean prelude;
    // the computation `(isize::MAX as usize + 1) - align` is unchanged.
    (9_223_372_036_854_775_807usize + 1) - align
}

#[cfg(test)]
mod tests {
    use super::*;

    const ISIZE_MAX: usize = isize::MAX as usize;

    // `max_size_for_align`, restated independently of the code under test so
    // the boundary test pins the contract rather than echoing the impl.
    fn spec_max_size_for_align(align: usize) -> usize {
        (ISIZE_MAX + 1) - align
    }

    // Alignments: powers of two 2^0 .. 2^63. 2^63 == isize::MAX + 1 is the
    // largest alignment for which `max_size_for_align` does not underflow.
    fn align_values() -> Vec<usize> {
        (0..=63).map(|k| 1usize << k).collect()
    }

    // A spread of in-precondition sizes (each <= isize::MAX).
    fn size_values() -> Vec<usize> {
        vec![0, 1, 2, 3, 7, 64, 4096, ISIZE_MAX / 2, ISIZE_MAX - 1, ISIZE_MAX]
    }

    // Split a target sum `t` (<= isize::MAX + 1) into two operands that each
    // satisfy the precondition (<= isize::MAX).
    fn split(t: usize) -> (usize, usize) {
        let a = if t > ISIZE_MAX { ISIZE_MAX } else { t };
        (a, t - a)
    }

    // ----- concrete witnesses (kept from the original suite) -----
    #[test]
    fn adds_sizes_without_padding() {
        let a = Layout { size: 2, align: 4 };
        let b = Layout { size: 3, align: 2 };
        assert_eq!(
            extend_packed(a, b).unwrap(),
            Layout { size: 5, align: 4 }
        );
    }

    #[test]
    fn overflowing_size_errors() {
        let a = Layout { size: ISIZE_MAX, align: 1 };
        let b = Layout { size: 2, align: 1 };
        assert!(extend_packed(a, b).is_err());
    }

    // Postcondition (success): the result size is *exactly* the sum of the two
    // input sizes -- no padding is inserted between the records. A buggy impl
    // that aligned/padded `new_size` would be caught here.
    #[test]
    fn ok_size_is_exact_sum() {
        for &align in &align_values() {
            for &s1 in &size_values() {
                for &s2 in &size_values() {
                    let layout = Layout { size: s1, align };
                    let next = Layout { size: s2, align: 1 };
                    if let Ok(l) = extend_packed(layout, next) {
                        assert_eq!(l.size(), s1 + s2);
                    }
                }
            }
        }
    }

    // Postcondition (success): the result alignment is `layout.align`, and the
    // alignment of `next` is ignored -- varying only `next.align` never changes
    // the result (value or Ok/Err).
    #[test]
    fn next_align_is_ignored_and_layout_align_preserved() {
        for &la in &align_values() {
            for &s1 in &size_values() {
                for &s2 in &size_values() {
                    let layout = Layout { size: s1, align: la };
                    let mut prev: Option<Result<Layout, LayoutError>> = None;
                    for &na in &align_values() {
                        let next = Layout { size: s2, align: na };
                        let r = extend_packed(layout, next);
                        if let Ok(l) = &r {
                            assert_eq!(l.align(), la);
                        }
                        if let Some(p) = &prev {
                            assert_eq!(p, &r);
                        }
                        prev = Some(r);
                    }
                }
            }
        }
    }

    // Precise success/failure boundary: `extend_packed` returns
    // `Ok(Layout { size: s1 + s2, align: layout.align })` iff
    // `s1 + s2 <= max_size_for_align(layout.align)`, and `Err(LayoutError)`
    // otherwise. Targets straddle the boundary for every alignment.
    #[test]
    fn ok_iff_sum_within_max_size_for_align() {
        for &align in &align_values() {
            let bound = spec_max_size_for_align(align);
            let mut targets = vec![0usize, 1];
            for &t in &[bound.wrapping_sub(1), bound, bound + 1] {
                if t <= ISIZE_MAX + 1 {
                    targets.push(t);
                }
            }
            for &t in &targets {
                let (s1, s2) = split(t);
                let layout = Layout { size: s1, align };
                let next = Layout { size: s2, align: 1 };
                let r = extend_packed(layout, next);
                if t <= bound {
                    assert_eq!(r, Ok(Layout { size: t, align }));
                } else {
                    assert_eq!(r, Err(LayoutError));
                }
            }
        }
    }
}
