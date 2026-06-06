//! Extracted from `core::alloc::Layout::is_size_align_valid` (src/alloc/layout.rs:69).
//!
//! Monomorphized to `usize`. `Alignment::new(align)` returns `Some` exactly
//! when `align` is a power of two (and therefore non-zero), so it is rewritten
//! as `usize::is_power_of_two`. The private helper `max_size_for_align` is
//! inlined (its `unchecked_sub` intrinsic rewritten as `-`).

/// Checks the preconditions of `Layout::from_size_align`: `align` must be a
/// power of two, and `size` rounded up to a multiple of `align` must not
/// exceed `isize::MAX`.
pub fn is_size_align_valid(size: usize, align: usize) -> bool {
    // `Alignment::new(align)` is `None` unless `align` is a power of two.
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

    // Adapted from `tests/alloc.rs::layout_round_up_to_align_edge_cases`.
    // `Layout::from_size_align(size, align).is_ok()` is exactly
    // `is_size_align_valid(size, align)`.
    #[test]
    fn layout_round_up_to_align_edge_cases() {
        const MAX_SIZE: usize = isize::MAX as usize;

        for shift in 0..usize::BITS {
            let align = 1_usize << shift;
            let edge = (MAX_SIZE + 1) - align;
            let low = edge.saturating_sub(10);
            let high = edge.saturating_add(10);
            assert!(is_size_align_valid(low, align));
            assert!(!is_size_align_valid(high, align));
            for size in low..=high {
                assert_eq!(
                    is_size_align_valid(size, align),
                    size.next_multiple_of(align) <= MAX_SIZE,
                );
            }
        }
    }

    // Adapted from `tests/alloc.rs::layout_accepts_all_valid_alignments`.
    #[test]
    fn layout_accepts_all_valid_alignments() {
        for align in 0..usize::BITS {
            assert!(is_size_align_valid(0, 1_usize << align));
        }
    }

    // Non-power-of-two alignments must be rejected (cf. `layout_errors`).
    #[test]
    fn rejects_non_power_of_two() {
        assert!(!is_size_align_valid(8, 3));
        assert!(!is_size_align_valid(0, 0));
        assert!(!is_size_align_valid(0, 6));
    }
}
