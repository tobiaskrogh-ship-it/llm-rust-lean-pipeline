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

    // ---- Property-based contract tests ------------------------------------

    /// Overflow-safe oracle for the documented postcondition: `size` rounded
    /// up to the next multiple of `align` must not exceed `isize::MAX`.
    /// Computed in `u128` so it never panics or overflows for any `usize`
    /// input. Requires `align >= 1` (always true for a power of two).
    fn fits_when_rounded_up(size: usize, align: usize) -> bool {
        let a = align as u128;
        let rounded = ((size as u128) + (a - 1)) / a * a;
        rounded <= isize::MAX as u128
    }

    // Contract precondition / failure condition: when `align` is not a power
    // of two, `Alignment::new(align)` is `None`, so the input is rejected
    // regardless of `size`. This pins the alignment clause independently of
    // the size bound.
    #[test]
    fn non_power_of_two_align_always_rejected() {
        const NON_POW2_ALIGNS: &[usize] = &[
            0, 3, 5, 6, 7, 9, 10, 12, 15, 24, 100, 1000,
            (1usize << 10) + 1,
            (1usize << 32) + (1usize << 5),
            isize::MAX as usize,             // 2^63 - 1
            usize::MAX,                      // 2^64 - 1
            (1usize << 63) + 1,
            (1usize << 63) + (1usize << 10),
        ];
        const SIZES: &[usize] = &[
            0,
            1,
            8,
            4096,
            isize::MAX as usize,
            (isize::MAX as usize) + 1,
            usize::MAX,
        ];
        for &align in NON_POW2_ALIGNS {
            assert!(
                !align.is_power_of_two(),
                "test data error: {align} is a power of two",
            );
            for &size in SIZES {
                assert!(
                    !is_size_align_valid(size, align),
                    "non-power-of-two align {align} must be rejected (size {size})",
                );
            }
        }
    }

    // Contract postcondition: for every power-of-two `align`, the result is
    // exactly "`size` rounded up to a multiple of `align` fits within
    // `isize::MAX`" -- the property the doc comment states, expressed via
    // rounding semantics rather than the implementation's subtraction.
    // Sweeping the full neighbourhood of each per-align boundary also pins
    // the exact off-by-one threshold (a `<` vs `<=` or wrong-constant bug
    // would be caught here).
    #[test]
    fn power_of_two_align_matches_round_up_contract() {
        for shift in 0..usize::BITS {
            let align = 1_usize << shift;
            let edge = (isize::MAX as usize + 1) - align; // largest accepted size
            let low = edge.saturating_sub(4);
            let high = edge.saturating_add(4);
            for size in low..=high {
                assert_eq!(
                    is_size_align_valid(size, align),
                    fits_when_rounded_up(size, align),
                    "align {align}, size {size}",
                );
            }
            // Extremes: smallest and largest representable sizes.
            for &size in &[0usize, 1, usize::MAX] {
                assert_eq!(
                    is_size_align_valid(size, align),
                    fits_when_rounded_up(size, align),
                    "align {align}, size {size}",
                );
            }
        }
    }
}
