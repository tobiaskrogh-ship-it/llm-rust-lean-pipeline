//! Extracted from `core::array::<[T; N]>::split_array_ref` (src/array/mod.rs:737),
//! monomorphized to `u64`. The inherent method `(&self) -> (&[T; M], &[T])` is
//! rewritten as a free function over a `&[u64; N]`.
//!
//! The original calls `self.split_first_chunk::<M>().unwrap()`. The private
//! slice helper `split_first_chunk` (src/slice/mod.rs:387) is inlined here.
//! Its body uses an unstable raw-pointer cast (`first.as_ptr().cast_array()`);
//! since `first.len() == M` on the `Some` path, that is equivalent to the
//! stable `TryFrom<&[T]> for &[T; M]` conversion, which is used instead so the
//! crate is self-contained on stable.

/// Returns an array reference to the first `M` items in the slice and the
/// remaining slice. Returns `None` if the slice is shorter than `M`.
fn split_first_chunk<const M: usize>(s: &[u64]) -> Option<(&[u64; M], &[u64])> {
    let Some((first, tail)) = s.split_at_checked(M) else { return None };
    // SAFETY-equivalent: `first.len() == M`, so the conversion succeeds.
    Some((first.try_into().unwrap(), tail))
}

/// Divides one array reference into two at an index.
///
/// The first will contain all indices from `[0, M)` and the second will
/// contain all indices from `[M, N)`.
///
/// # Panics
///
/// Panics if `M > N`.
#[inline]
pub fn split_array_ref<const M: usize, const N: usize>(a: &[u64; N]) -> (&[u64; M], &[u64]) {
    split_first_chunk::<M>(a).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from the doc-test on `split_array_ref` (src/array/mod.rs),
    // monomorphized to `u64`, call site rewritten to the free function.
    #[test]
    fn doctest_split_array_ref() {
        let v: [u64; 6] = [1, 2, 3, 4, 5, 6];

        {
            let (left, right) = split_array_ref::<0, 6>(&v);
            assert_eq!(left, &[]);
            assert_eq!(right, &[1, 2, 3, 4, 5, 6]);
        }

        {
            let (left, right) = split_array_ref::<2, 6>(&v);
            assert_eq!(left, &[1, 2]);
            assert_eq!(right, &[3, 4, 5, 6]);
        }

        {
            let (left, right) = split_array_ref::<6, 6>(&v);
            assert_eq!(left, &[1, 2, 3, 4, 5, 6]);
            assert_eq!(right, &[]);
        }
    }

    // Transferred from core's `tests/array.rs::array_split_array_ref_out_of_bounds`.
    #[test]
    #[should_panic]
    fn array_split_array_ref_out_of_bounds() {
        let v: [u64; 6] = [1, 2, 3, 4, 5, 6];

        split_array_ref::<7, 6>(&v);
    }
}
