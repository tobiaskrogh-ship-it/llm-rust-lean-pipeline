//! Extracted from `core::array::from_ref` (src/array/mod.rs:166), monomorphized to `u64`.

/// Converts a reference to `T` into a reference to an array of length 1 (without copying).
pub const fn from_ref(s: &u64) -> &[u64; 1] {
    // SAFETY: Converting `&T` to `&[T; 1]` is sound.
    unsafe { &*(s as *const u64).cast::<[u64; 1]>() }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Transferred from core's `tests/array.rs::array_from_ref`,
    // monomorphized to `u64` (the original used `String`/`&str`).
    #[test]
    fn array_from_ref() {
        let value: u64 = 42;
        let arr: &[u64; 1] = from_ref(&value);
        assert_eq!(&[value], arr);

        const VALUE: &u64 = &123;
        const ARR: &[u64; 1] = from_ref(VALUE);
        assert_eq!(&[*VALUE], ARR);
        assert!(core::ptr::eq(VALUE, &ARR[0]));
    }

    /// Representative `u64` inputs, including boundary values. `from_ref` has
    /// no precondition (every `&u64` is a valid argument), so this set just
    /// needs to exercise the postconditions across the value range.
    const SAMPLES: [u64; 9] = [
        0,
        1,
        2,
        42,
        1 << 32,
        u64::MAX - 1,
        u64::MAX,
        0x0123_4567_89ab_cdef,
        0xffff_0000_ffff_0000,
    ];

    // Postcondition (value): `from_ref(&x)` yields a length-1 array whose sole
    // element equals the referenced value, for every input `x`. A buggy
    // implementation returning a different element (e.g. a default, or a
    // shifted/masked value) would be caught here.
    #[test]
    fn prop_element_equals_input() {
        for x in SAMPLES {
            let arr: &[u64; 1] = from_ref(&x);
            assert_eq!(arr[0], x, "from_ref(&{x})[0] should equal {x}");
        }
    }

    // Postcondition (no copy): the returned array reference aliases the input
    // storage rather than pointing at a fresh copy. This is independent of the
    // value postcondition — a copying implementation would still satisfy
    // `prop_element_equals_input` but fail this pointer-identity check, which
    // the doc comment ("without copying") makes part of the contract.
    #[test]
    fn prop_no_copy_aliases_input() {
        for x in SAMPLES {
            let r: &u64 = &x;
            let arr: &[u64; 1] = from_ref(r);
            assert!(
                core::ptr::eq(r, &arr[0]),
                "from_ref must not copy: &arr[0] should alias the input reference",
            );
        }
    }
}
