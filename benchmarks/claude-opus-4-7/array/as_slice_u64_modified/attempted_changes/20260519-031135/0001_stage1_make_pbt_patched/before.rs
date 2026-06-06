//! Extracted from `core::array::<[T; N]>::as_slice` (src/array/mod.rs:612),
//! monomorphized to `u64`. The inherent method `(&self) -> &[T]` is rewritten
//! as a free function over a `&[u64; N]`.

/// Returns a slice containing the entire array. Equivalent to `&s[..]`.
pub const fn as_slice<const N: usize>(a: &[u64; N]) -> &[u64] {
    a
}

#[cfg(test)]
mod tests {
    use super::*;

    // No test for `as_slice` exists in the source crate; minimal test.
    #[test]
    fn it_works() {
        let arr: [u64; 3] = [1, 2, 3];
        let s: &[u64] = as_slice(&arr);
        assert_eq!(s, &[1, 2, 3]);
        assert_eq!(s.len(), 3);

        let empty: [u64; 0] = [];
        assert_eq!(as_slice(&empty), &[] as &[u64]);
    }
}
