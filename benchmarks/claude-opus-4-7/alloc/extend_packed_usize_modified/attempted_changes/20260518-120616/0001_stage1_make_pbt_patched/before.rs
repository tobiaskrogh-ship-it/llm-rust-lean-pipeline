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
    (isize::MAX as usize + 1) - align
}

#[cfg(test)]
mod tests {
    use super::*;

    // No dedicated source test exists for `extend_packed`; these cases follow
    // from its documented behavior (sizes add with no padding; the alignment
    // of `next` is irrelevant; the result must still fit `isize`).
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
        let size_max = isize::MAX as usize;
        let a = Layout { size: size_max, align: 1 };
        let b = Layout { size: 2, align: 1 };
        assert!(extend_packed(a, b).is_err());
    }
}
