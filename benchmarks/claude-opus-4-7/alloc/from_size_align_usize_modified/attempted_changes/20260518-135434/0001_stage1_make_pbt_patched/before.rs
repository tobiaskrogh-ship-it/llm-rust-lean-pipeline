//! Extracted from `core::alloc::Layout::from_size_align` (src/alloc/layout.rs:59).
//!
//! `Layout` is modeled as `{ size: usize, align: usize }` (the original wraps a
//! validated power-of-two `Alignment`). The private helpers `is_size_align_valid`
//! and `max_size_for_align` are inlined; `mem::transmute(align)` becomes a plain
//! struct construction; `Alignment::new` becomes `usize::is_power_of_two`.

/// Layout of a block of memory: a size and a power-of-two alignment.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Layout {
    size: usize,
    align: usize,
}

impl Layout {
    /// The minimum size in bytes for a memory block of this layout.
    pub fn size(&self) -> usize {
        self.size
    }

    /// The minimum byte alignment for a memory block of this layout.
    pub fn align(&self) -> usize {
        self.align
    }
}

/// Returned when the parameters given to `from_size_align` do not satisfy its
/// documented constraints.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LayoutError;

/// Constructs a `Layout` from a given `size` and `align`, or returns
/// `LayoutError` if `align` is not a power of two, or `size` rounded up to a
/// multiple of `align` would overflow `isize`.
pub fn from_size_align(size: usize, align: usize) -> Result<Layout, LayoutError> {
    if is_size_align_valid(size, align) {
        Ok(Layout { size, align })
    } else {
        Err(LayoutError)
    }
}

// Inlined from `Layout::is_size_align_valid` (src/alloc/layout.rs:69).
fn is_size_align_valid(size: usize, align: usize) -> bool {
    if !align.is_power_of_two() {
        return false;
    }
    if size > max_size_for_align(align) {
        return false;
    }
    true
}

// Inlined from `Layout::max_size_for_align` (src/alloc/layout.rs:78).
fn max_size_for_align(align: usize) -> usize {
    (isize::MAX as usize + 1) - align
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from `tests/alloc.rs::layout_round_up_to_align_edge_cases`.
    #[test]
    fn layout_round_up_to_align_edge_cases() {
        const MAX_SIZE: usize = isize::MAX as usize;

        for shift in 0..usize::BITS {
            let align = 1_usize << shift;
            let edge = (MAX_SIZE + 1) - align;
            let low = edge.saturating_sub(10);
            let high = edge.saturating_add(10);
            assert!(from_size_align(low, align).is_ok());
            assert!(from_size_align(high, align).is_err());
            for size in low..=high {
                assert_eq!(
                    from_size_align(size, align).is_ok(),
                    size.next_multiple_of(align) <= MAX_SIZE,
                );
            }
        }
    }

    // Transferred from `tests/alloc.rs::layout_accepts_all_valid_alignments`.
    #[test]
    fn layout_accepts_all_valid_alignments() {
        for align in 0..usize::BITS {
            let layout = from_size_align(0, 1_usize << align).unwrap();
            assert_eq!(layout.align(), 1_usize << align);
        }
    }

    // The `align_to(3)` assertion of `tests/alloc.rs::layout_errors` exercises
    // rejection of non-power-of-two alignments at construction time.
    #[test]
    fn rejects_invalid() {
        assert!(from_size_align(8, 3).is_err());
        assert!(from_size_align(0, 0).is_err());
        let l = from_size_align(24576, 8192).unwrap();
        assert_eq!(l.size(), 24576);
        assert_eq!(l.align(), 8192);
    }
}
