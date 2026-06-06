//! Extracted from `core::alloc::Layout::max_size_for_align` (src/alloc/layout.rs:78).
//!
//! Monomorphized to `usize`. The original uses the `unchecked_sub` intrinsic;
//! since the maximum possible alignment is `isize::MAX + 1`, the subtraction
//! cannot overflow, so it is rewritten as plain `-`.

/// Returns the largest size allowed for a memory block with the given
/// power-of-two alignment.
pub fn max_size_for_align(align: usize) -> usize {
    // Rounded up size is:
    //   size_rounded_up = (size + align - 1) & !(align - 1);
    //
    // Checking for summation overflow is both necessary and sufficient.
    //
    // The maximum possible alignment is `isize::MAX + 1`, so the subtraction
    // cannot overflow.
    (isize::MAX as usize + 1) - align
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn matches_formula() {
        assert_eq!(max_size_for_align(1), isize::MAX as usize);
        assert_eq!(max_size_for_align(2), isize::MAX as usize - 1);
        // For the maximum alignment (`isize::MAX + 1`), no positive size fits.
        let max_align = isize::MAX as usize + 1;
        assert_eq!(max_size_for_align(max_align), 0);
    }

    #[test]
    fn powers_of_two() {
        for shift in 0..usize::BITS {
            let align = 1_usize << shift;
            assert_eq!(max_size_for_align(align), (isize::MAX as usize + 1) - align);
        }
    }
}
