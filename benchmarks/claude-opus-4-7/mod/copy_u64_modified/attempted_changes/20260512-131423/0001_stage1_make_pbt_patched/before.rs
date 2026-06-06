//! Extracted from `core::mem::copy`, monomorphized to `u64`.
//!
//! Source: `to_be_extracted/core-1.94.0/src/mem/mod.rs:994` (function `copy`).
//!
//! The source defines `copy` as:
//!
//! ```ignore
//! pub const fn copy<T: Copy>(x: &T) -> T { *x }
//! ```

/// Bitwise-copies a value.
#[inline]
pub const fn copy(x: &u64) -> u64 {
    *x
}

#[cfg(test)]
mod tests {
    use super::*;

    // Doc-test from source uses `Result<(), &i32>` and `map_err`; the closest
    // monomorphic-to-u64 analog is to verify the function reproduces the
    // pointed-to value and is usable as a function pointer.
    #[test]
    fn doctest_basic_copy() {
        let x: u64 = 1;
        let y = copy(&x);
        assert_eq!(y, 1);
        assert_eq!(x, 1); // original still readable; we only had a reference.
    }

    #[test]
    fn copy_various_u64_values() {
        assert_eq!(copy(&0u64), 0);
        assert_eq!(copy(&u64::MAX), u64::MAX);
        assert_eq!(copy(&12345u64), 12345);
        let big = 0xDEAD_BEEF_CAFE_BABEu64;
        assert_eq!(copy(&big), big);
    }

    #[test]
    fn copy_usable_as_fn_pointer() {
        // The function is useful as a `fn(&T) -> T` combinator argument.
        let f: fn(&u64) -> u64 = copy;
        let v = 99u64;
        assert_eq!(f(&v), 99);
    }
}
