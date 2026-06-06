//! Extracted from `core::alloc::Layout::pad_to_align` (src/alloc/layout.rs:320).
//!
//! `Layout` is modeled as `{ size: usize, align: usize }`. The private helper
//! `size_rounded_up_to_custom_align` is inlined; the call to
//! `from_size_align_unchecked` (which only constructs a `Layout` after the
//! invariant is established) becomes a plain struct construction. The
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

/// Creates a layout by rounding the size of `layout` up to a multiple of its
/// alignment.
pub fn pad_to_align(layout: Layout) -> Layout {
    let new_size = size_rounded_up_to_custom_align(layout.size, layout.align);
    // padded size is guaranteed to not exceed `isize::MAX`.
    Layout { size: new_size, align: layout.align }
}

// Inlined from `Layout::size_rounded_up_to_custom_align` (src/alloc/layout.rs:285).
fn size_rounded_up_to_custom_align(size: usize, align: usize) -> usize {
    let align_m1 = align - 1;
    (size + align_m1) & !align_m1
}

#[cfg(test)]
mod tests {
    use super::*;

    // No dedicated source test exists; these cases follow from the documented
    // behavior of `repeat` (a 6/align-4 layout pads to size 8; an already
    // aligned 12/align-4 layout is unchanged).
    #[test]
    fn pads_up() {
        assert_eq!(
            pad_to_align(Layout { size: 6, align: 4 }),
            Layout { size: 8, align: 4 }
        );
        assert_eq!(
            pad_to_align(Layout { size: 9, align: 4 }),
            Layout { size: 12, align: 4 }
        );
    }

    #[test]
    fn already_aligned_is_unchanged() {
        assert_eq!(
            pad_to_align(Layout { size: 12, align: 4 }),
            Layout { size: 12, align: 4 }
        );
        assert_eq!(
            pad_to_align(Layout { size: 0, align: 8 }),
            Layout { size: 0, align: 8 }
        );
    }
}
