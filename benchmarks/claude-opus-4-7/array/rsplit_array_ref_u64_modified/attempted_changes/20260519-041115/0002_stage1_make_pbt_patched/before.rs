//! Extracted from `core::array::<[T; N]>::rsplit_array_ref` (src/array/mod.rs:815),
//! monomorphized to `u64`. The inherent method `(&self) -> (&[T], &[T; M])` is
//! rewritten as a free function over a `&[u64; N]`.
//!
//! The original calls `self.split_last_chunk::<M>().unwrap()`. The private
//! slice helper `split_last_chunk` (src/slice/mod.rs:447) is inlined here.
//! Its body uses an unstable raw-pointer cast (`last.as_ptr().cast_array()`);
//! since `last.len() == M` on the `Some` path, that is equivalent to the
//! stable `TryFrom<&[T]> for &[T; M]` conversion, which is used instead.

/// Returns the remaining slice and an array reference to the last `M` items.
/// Returns `None` if the slice is shorter than `M`.
fn split_last_chunk<const M: usize>(s: &[u64]) -> Option<(&[u64], &[u64; M])> {
    let Some(index) = s.len().checked_sub(M) else { return None };
    let (init, last) = s.split_at(index);
    // SAFETY-equivalent: `last.len() == M`, so the conversion succeeds.
    Some((init, last.try_into().unwrap()))
}

/// Divides one array reference into two at an index from the end.
///
/// The first will contain all indices from `[0, N - M)` and the second will
/// contain all indices from `[N - M, N)`.
///
/// # Panics
///
/// Panics if `M > N`.
#[inline]
pub fn rsplit_array_ref<const M: usize, const N: usize>(a: &[u64; N]) -> (&[u64], &[u64; M]) {
    split_last_chunk::<M>(a).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from the doc-test on `rsplit_array_ref` (src/array/mod.rs),
    // monomorphized to `u64`, call site rewritten to the free function.
    #[test]
    fn doctest_rsplit_array_ref() {
        let v: [u64; 6] = [1, 2, 3, 4, 5, 6];

        {
            let (left, right) = rsplit_array_ref::<0, 6>(&v);
            assert_eq!(left, &[1, 2, 3, 4, 5, 6]);
            assert_eq!(right, &[]);
        }

        {
            let (left, right) = rsplit_array_ref::<2, 6>(&v);
            assert_eq!(left, &[1, 2, 3, 4]);
            assert_eq!(right, &[5, 6]);
        }

        {
            let (left, right) = rsplit_array_ref::<6, 6>(&v);
            assert_eq!(left, &[]);
            assert_eq!(right, &[1, 2, 3, 4, 5, 6]);
        }
    }

    // Transferred from core's `tests/array.rs::array_rsplit_array_ref_out_of_bounds`.
    #[test]
    #[should_panic]
    fn array_rsplit_array_ref_out_of_bounds() {
        let v: [u64; 6] = [1, 2, 3, 4, 5, 6];

        rsplit_array_ref::<7, 6>(&v);
    }
}
