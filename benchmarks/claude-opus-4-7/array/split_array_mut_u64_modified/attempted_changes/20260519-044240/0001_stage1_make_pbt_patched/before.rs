//! Extracted from `core::array::<[T; N]>::split_array_mut` (src/array/mod.rs:770),
//! monomorphized to `u64`. The inherent method `(&mut self) -> (&mut [T; M], &mut [T])`
//! is rewritten as a free function over a `&mut [u64; N]`.
//!
//! The original calls `self.split_first_chunk_mut::<M>().unwrap()`. The private
//! slice helper `split_first_chunk_mut` (src/slice/mod.rs:417) is inlined here.
//! Its body uses an unstable raw-pointer cast (`first.as_mut_ptr().cast_array()`);
//! since `first.len() == M` on the `Some` path, that is equivalent to the
//! stable `TryFrom<&mut [T]> for &mut [T; M]` conversion, which is used instead.

/// Returns a mutable array reference to the first `M` items in the slice and
/// the remaining slice. Returns `None` if the slice is shorter than `M`.
fn split_first_chunk_mut<const M: usize>(s: &mut [u64]) -> Option<(&mut [u64; M], &mut [u64])> {
    let Some((first, tail)) = s.split_at_mut_checked(M) else { return None };
    // SAFETY-equivalent: `first.len() == M`, so the conversion succeeds.
    Some((first.try_into().unwrap(), tail))
}

/// Divides one mutable array reference into two at an index.
///
/// The first will contain all indices from `[0, M)` and the second will
/// contain all indices from `[M, N)`.
///
/// # Panics
///
/// Panics if `M > N`.
#[inline]
pub fn split_array_mut<const M: usize, const N: usize>(
    a: &mut [u64; N],
) -> (&mut [u64; M], &mut [u64]) {
    split_first_chunk_mut::<M>(a).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from the doc-test on `split_array_mut` (src/array/mod.rs),
    // monomorphized to `u64`, call site rewritten to the free function.
    #[test]
    fn doctest_split_array_mut() {
        let mut v: [u64; 6] = [1, 0, 3, 0, 5, 6];
        let (left, right) = split_array_mut::<2, 6>(&mut v);
        assert_eq!(left, &mut [1, 0][..]);
        assert_eq!(right, &mut [3, 0, 5, 6]);
        left[1] = 2;
        right[1] = 4;
        assert_eq!(v, [1, 2, 3, 4, 5, 6]);
    }

    // Transferred from core's `tests/array.rs::array_split_array_mut`,
    // monomorphized to `u64`.
    #[test]
    fn array_split_array_mut() {
        let mut v: [u64; 6] = [1, 2, 3, 4, 5, 6];

        {
            let (left, right) = split_array_mut::<0, 6>(&mut v);
            assert_eq!(left, &mut []);
            assert_eq!(right, &mut [1, 2, 3, 4, 5, 6]);
        }

        {
            let (left, right) = split_array_mut::<6, 6>(&mut v);
            assert_eq!(left, &mut [1, 2, 3, 4, 5, 6]);
            assert_eq!(right, &mut []);
        }
    }

    // Transferred from core's `tests/array.rs::array_split_array_mut_out_of_bounds`.
    #[test]
    #[should_panic]
    fn array_split_array_mut_out_of_bounds() {
        let mut v: [u64; 6] = [1, 2, 3, 4, 5, 6];

        split_array_mut::<7, 6>(&mut v);
    }
}
