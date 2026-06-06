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
    let new_align = layout.align.max(next.align);
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
    (isize::MAX as usize + 1) - align
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
}
