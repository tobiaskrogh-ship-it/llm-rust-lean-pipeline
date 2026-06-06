//! Extracted from `core::alloc::Layout::size_rounded_up_to_custom_align`
//! (src/alloc/layout.rs:285).
//!
//! Monomorphized to `usize`. The original takes `self` (a `Layout`) and an
//! `Alignment`; here `size` is passed directly and `align` is a plain
//! power-of-two `usize`. The `unchecked_sub`/`unchecked_add` intrinsics cannot
//! overflow given the documented `Layout` invariants, so they become `-`/`+`.

/// Returns the smallest multiple of `align` greater than or equal to `size`.
///
/// `align` must be a power of two.
pub fn size_rounded_up_to_custom_align(size: usize, align: usize) -> usize {
    // Rounded up value is:
    //   size_rounded_up = (size + align - 1) & !(align - 1);
    let align_m1 = align - 1;
    (size + align_m1) & !align_m1
}

#[cfg(test)]
mod tests {
    use super::*;

    // No dedicated source test exists for this private helper; these cases are
    // derived from the documented behavior of `padding_needed_for`/`repeat`
    // (e.g. size 9, align 4 rounds up to 12; size 6, align 4 rounds up to 8).
    #[test]
    fn rounds_up() {
        assert_eq!(size_rounded_up_to_custom_align(9, 4), 12);
        assert_eq!(size_rounded_up_to_custom_align(6, 4), 8);
        assert_eq!(size_rounded_up_to_custom_align(12, 4), 12);
        assert_eq!(size_rounded_up_to_custom_align(1, 8), 8);
        assert_eq!(size_rounded_up_to_custom_align(0, 1_usize << 20), 0);
        assert_eq!(size_rounded_up_to_custom_align(13, 1), 13);
    }

    #[test]
    fn already_aligned_is_unchanged() {
        for shift in 0..16 {
            let align = 1_usize << shift;
            assert_eq!(size_rounded_up_to_custom_align(align * 3, align), align * 3);
        }
    }
}
