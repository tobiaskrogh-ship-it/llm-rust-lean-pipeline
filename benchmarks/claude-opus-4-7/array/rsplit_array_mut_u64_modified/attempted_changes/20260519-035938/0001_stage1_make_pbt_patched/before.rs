//! Extracted from `core::array::<[T; N]>::rsplit_array_mut` (src/array/mod.rs:848),
//! monomorphized to `u64`. The inherent method `(&mut self) -> (&mut [T], &mut [T; M])`
//! is rewritten as a free function over a `&mut [u64; N]`.
//!
//! The original calls `self.split_last_chunk_mut::<M>().unwrap()`. The private
//! slice helper `split_last_chunk_mut` (src/slice/mod.rs:478) is inlined here.
//! Its body uses an unstable raw-pointer cast (`last.as_mut_ptr().cast_array()`);
//! since `last.len() == M` on the `Some` path, that is equivalent to the
//! stable `TryFrom<&mut [T]> for &mut [T; M]` conversion, which is used instead.

/// Returns the remaining slice and a mutable array reference to the last `M`
/// items. Returns `None` if the slice is shorter than `M`.
fn split_last_chunk_mut<const M: usize>(s: &mut [u64]) -> Option<(&mut [u64], &mut [u64; M])> {
    let Some(index) = s.len().checked_sub(M) else { return None };
    let (init, last) = s.split_at_mut(index);
    // SAFETY-equivalent: `last.len() == M`, so the conversion succeeds.
    Some((init, last.try_into().unwrap()))
}

/// Divides one mutable array reference into two at an index from the end.
///
/// The first will contain all indices from `[0, N - M)` and the second will
/// contain all indices from `[N - M, N)`.
///
/// # Panics
///
/// Panics if `M > N`.
#[inline]
pub fn rsplit_array_mut<const M: usize, const N: usize>(
    a: &mut [u64; N],
) -> (&mut [u64], &mut [u64; M]) {
    split_last_chunk_mut::<M>(a).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from the doc-test on `rsplit_array_mut` (src/array/mod.rs),
    // monomorphized to `u64`, call site rewritten to the free function.
    #[test]
    fn doctest_rsplit_array_mut() {
        let mut v: [u64; 6] = [1, 0, 3, 0, 5, 6];
        let (left, right) = rsplit_array_mut::<4, 6>(&mut v);
        assert_eq!(left, &mut [1, 0]);
        assert_eq!(right, &mut [3, 0, 5, 6][..]);
        left[1] = 2;
        right[1] = 4;
        assert_eq!(v, [1, 2, 3, 4, 5, 6]);
    }

    // Transferred from core's `tests/array.rs::array_rsplit_array_mut`,
    // monomorphized to `u64`.
    #[test]
    fn array_rsplit_array_mut() {
        let mut v: [u64; 6] = [1, 2, 3, 4, 5, 6];

        {
            let (left, right) = rsplit_array_mut::<0, 6>(&mut v);
            assert_eq!(left, &mut [1, 2, 3, 4, 5, 6]);
            assert_eq!(right, &mut []);
        }

        {
            let (left, right) = rsplit_array_mut::<6, 6>(&mut v);
            assert_eq!(left, &mut []);
            assert_eq!(right, &mut [1, 2, 3, 4, 5, 6]);
        }
    }

    // Transferred from core's `tests/array.rs::array_rsplit_array_mut_out_of_bounds`.
    #[test]
    #[should_panic]
    fn array_rsplit_array_mut_out_of_bounds() {
        let mut v: [u64; 6] = [1, 2, 3, 4, 5, 6];

        rsplit_array_mut::<7, 6>(&mut v);
    }
}
