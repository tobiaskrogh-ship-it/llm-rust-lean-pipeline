//! Extracted from `core::array::<[T; N]>::as_mut_slice` (src/array/mod.rs:620),
//! monomorphized to `u64`. The inherent method `(&mut self) -> &mut [T]` is
//! rewritten as a free function over a `&mut [u64; N]`.

/// Returns a mutable slice containing the entire array. Equivalent to `&mut s[..]`.
pub const fn as_mut_slice<const N: usize>(a: &mut [u64; N]) -> &mut [u64] {
    a
}

#[cfg(test)]
mod tests {
    use super::*;

    // No test for `as_mut_slice` exists in the source crate; minimal test.
    #[test]
    fn it_works() {
        let mut arr: [u64; 3] = [1, 2, 3];
        {
            let s: &mut [u64] = as_mut_slice(&mut arr);
            assert_eq!(s, &mut [1, 2, 3]);
            s[1] = 20;
        }
        assert_eq!(arr, [1, 20, 3]);

        let mut empty: [u64; 0] = [];
        assert_eq!(as_mut_slice(&mut empty), &mut [] as &mut [u64]);
    }
}
