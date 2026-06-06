//! Extracted from `core::alloc::Layout::array` (src/alloc/layout.rs:480).
//!
//! Monomorphized to element type `u64`: `T::LAYOUT` becomes a fixed element
//! size of 8 and alignment of 8 (`size_of::<u64>()` / `align_of::<u64>()`).
//! The `inner` closure and the private helper `max_size_for_align` are inlined;
//! `from_size_align_unchecked` becomes a plain struct construction; the
//! `unchecked_mul`/`unchecked_sub` intrinsics become `*`/`-` (the preceding
//! bound guarantees they cannot overflow).

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

/// Returned on arithmetic overflow or when the total size would exceed
/// `isize::MAX`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LayoutError;

/// Creates a layout describing the record for a `[u64; n]`.
pub fn array_u64(n: usize) -> Result<Layout, LayoutError> {
    // `u64::LAYOUT`: size_of::<u64>() == 8, align_of::<u64>() == 8.
    let element_size: usize = 8;
    let align: usize = 8;

    // We need to check that the total size won't overflow a `usize` and that it
    // still fits in an `isize`. Division checks both with a single threshold.
    if element_size != 0 && n > max_size_for_align(align) / element_size {
        return Err(LayoutError);
    }

    // We just checked that we won't overflow `usize` when we multiply.
    let array_size = element_size * n;

    // `array_size` will not exceed `isize::MAX` even when rounded up to the
    // alignment, and `align` is a power of two.
    Ok(Layout { size: array_size, align })
}

// Inlined from `Layout::max_size_for_align` (src/alloc/layout.rs:78).
fn max_size_for_align(align: usize) -> usize {
    (isize::MAX as usize + 1) - align
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from `tests/alloc.rs::layout_array_edge_cases`,
    // monomorphized to the `for_type::<T>()` case with `size_of::<T>() == 8`
    // (e.g. `i64`/`u64`). The `()` ZST case and the `[i32; _]`/`[u8; _]`
    // cases are dropped: they require different element-type monomorphizations
    // than `u64`.
    #[test]
    fn layout_array_edge_cases() {
        const MAX_SIZE: usize = isize::MAX as usize;
        const ELEM: usize = 8; // size_of::<u64>()

        let edge = (MAX_SIZE + 1) / ELEM;
        let low = edge.saturating_sub(10);
        let high = edge.saturating_add(10);
        assert!(array_u64(low).is_ok());
        assert!(array_u64(high).is_err());
        for n in low..=high {
            assert_eq!(array_u64(n).is_ok(), n * ELEM <= MAX_SIZE);
        }
    }

    #[test]
    fn basic_cases() {
        assert_eq!(array_u64(0).unwrap(), Layout { size: 0, align: 8 });
        assert_eq!(array_u64(3).unwrap(), Layout { size: 24, align: 8 });
    }
}
