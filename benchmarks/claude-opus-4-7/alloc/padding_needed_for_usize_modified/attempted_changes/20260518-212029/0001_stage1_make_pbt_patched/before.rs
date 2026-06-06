//! Extracted from `core::alloc::Layout::padding_needed_for`
//! (src/alloc/layout.rs:272).
//!
//! Monomorphized to `usize`. `self.size()` is passed as `size`. `Alignment::new`
//! becomes `usize::is_power_of_two` (returning `usize::MAX` when not a power of
//! two, as the original returns when `Alignment::new` is `None`). The private
//! helper `size_rounded_up_to_custom_align` is inlined; `unchecked_sub` → `-`.

/// Returns the amount of padding that must be inserted after a block of size
/// `size` so that the following address satisfies `align`.
///
/// The return value has no meaning if `align` is not a power of two
/// (`usize::MAX` is returned in that case).
pub fn padding_needed_for(size: usize, align: usize) -> usize {
    // `Alignment::new(align)` is `None` unless `align` is a power of two.
    if !align.is_power_of_two() {
        return usize::MAX;
    }
    let len_rounded_up = size_rounded_up_to_custom_align(size, align);
    // Cannot overflow because the rounded-up value is never less than `size`.
    len_rounded_up - size
}

// Inlined from `Layout::size_rounded_up_to_custom_align` (src/alloc/layout.rs:285).
fn size_rounded_up_to_custom_align(size: usize, align: usize) -> usize {
    let align_m1 = align - 1;
    (size + align_m1) & !align_m1
}

#[cfg(test)]
mod tests {
    use super::*;

    // From the doc comment of `padding_needed_for`: if size is 9 then
    // `padding_needed_for(4)` returns 3.
    #[test]
    fn doc_example() {
        assert_eq!(padding_needed_for(9, 4), 3);
    }

    #[test]
    fn basic_cases() {
        assert_eq!(padding_needed_for(8, 4), 0);
        assert_eq!(padding_needed_for(0, 16), 0);
        assert_eq!(padding_needed_for(6, 4), 2);
        assert_eq!(padding_needed_for(13, 1), 0);
    }

    #[test]
    fn non_power_of_two_returns_max() {
        assert_eq!(padding_needed_for(9, 3), usize::MAX);
        assert_eq!(padding_needed_for(9, 0), usize::MAX);
    }
}
