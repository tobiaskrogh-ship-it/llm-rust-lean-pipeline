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
}
