//! Extracted from `core::alloc::Layout::align_to` (src/alloc/layout.rs:244).
//!
//! `Layout` is modeled as `{ size: usize, align: usize }`. `Alignment::new`
//! becomes `usize::is_power_of_two`; `Alignment::max` becomes `usize::max`. The
//! private helper `from_size_alignment` (and the `max_size_for_align` it calls)
//! is inlined; `unchecked_sub` → `-`.

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

/// Returned when the requested alignment is invalid or the resulting layout
/// would overflow `isize`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LayoutError;

/// Creates a layout describing a record that has the same layout as `layout`
/// but is aligned to at least `align` bytes.
pub fn align_to(layout: Layout, align: usize) -> Result<Layout, LayoutError> {
    if align.is_power_of_two() {
        from_size_alignment(layout.size, layout.align.max(align))
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

// Inlined from `Layout::max_size_for_align` (src/alloc/layout.rs:78).
fn max_size_for_align(align: usize) -> usize {
    (isize::MAX as usize + 1) - align
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from the `align_to` assertions of
    // `tests/alloc.rs::layout_errors`. `Layout::new::<[u8; 2]>()` has size 2,
    // align 1.
    #[test]
    fn layout_errors() {
        let layout = Layout { size: 2, align: 1 };

        // Should error if the alignment is not a power of two.
        assert!(align_to(layout, 3).is_err());

        // Errors on arithmetic overflow as the alignment cannot overflow `isize`.
        let size_max = isize::MAX as usize;
        assert!(align_to(layout, size_max + 1).is_err());
    }

    #[test]
    fn raises_alignment() {
        let layout = Layout { size: 2, align: 1 };
        assert_eq!(
            align_to(layout, 4).unwrap(),
            Layout { size: 2, align: 4 }
        );
        // Already sufficiently aligned: alignment is unchanged.
        let layout = Layout { size: 16, align: 8 };
        assert_eq!(align_to(layout, 4).unwrap(), Layout { size: 16, align: 8 });
    }
}
