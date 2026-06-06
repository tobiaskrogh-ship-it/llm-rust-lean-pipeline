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
    if let Some(size) = layout.size.checked_mul(n) {
        // The safe constructor is called here to enforce the isize size limit.
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

// Inlined from `Layout::max_size_for_align` (src/alloc/layout.rs:78).
fn max_size_for_align(align: usize) -> usize {
    (isize::MAX as usize + 1) - align
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from the `repeat_packed` assertions of
    // `tests/alloc.rs::layout_errors` (`Layout::new::<[u8; 2]>()` => size 2,
    // align 1).
    #[test]
    fn layout_errors() {
        let layout = Layout { size: 2, align: 1 };
        let size = layout.size();
        let size_max = isize::MAX as usize;
        let align_max = size_max / size;

        assert!(repeat_packed(layout, align_max).is_ok());
        assert!(repeat_packed(layout, align_max + 1).is_err());
    }

    #[test]
    fn packs_without_padding() {
        let layout = Layout { size: 6, align: 4 };
        assert_eq!(
            repeat_packed(layout, 3).unwrap(),
            Layout { size: 18, align: 4 }
        );
    }
}
