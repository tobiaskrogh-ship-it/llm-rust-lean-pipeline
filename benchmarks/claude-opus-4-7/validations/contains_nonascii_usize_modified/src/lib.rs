//! Extracted from `core::str::validations::contains_nonascii`.
//!
//! Returns `true` if any byte in the word `x` is nonascii (>= 128).
//!
//! Self-contained reimplementation: the source uses `usize::repeat_u8(0x80)`
//! (an unstable private `core` helper). The original inlined
//! `usize::from_ne_bytes([0x80; size_of::<usize>()])`, but `from_ne_bytes`
//! and `core::mem::size_of` have no Hax Lean model. The value of
//! `repeat_u8(0x80)` is a `usize` whose every byte is `0x80`; Hax models
//! `usize` as 64-bit (matching the 64-bit test host), so it equals the
//! constant `0x8080_8080_8080_8080`, inlined directly below.

const NONASCII_MASK: usize = 0x8080_8080_8080_8080;

#[inline]
pub const fn contains_nonascii(x: usize) -> bool {
    (x & NONASCII_MASK) != 0
}

#[cfg(test)]
mod tests {
    use super::contains_nonascii;

    /// Specification oracle, deliberately independent of the bit-mask trick
    /// used by the implementation: a word "contains nonascii" iff at least
    /// one of its native-endian bytes has its high bit set, i.e. byte value
    /// `>= 0x80` (== 128).
    fn spec_contains_nonascii(x: usize) -> bool {
        x.to_ne_bytes().iter().any(|&b| b >= 0x80)
    }

    /// Full contract. `contains_nonascii` is total (no precondition, never
    /// panics, returns a plain `bool`), so its entire contract is the single
    /// postcondition: the result equals the per-byte high-bit disjunction.
    ///
    /// The structured input space makes this property catch the realistic
    /// ways the contract could be violated:
    ///
    /// * sweeping a non-ascii byte (`0x80` and `0xFF`) through *every* byte
    ///   position rules out an implementation that inspects only some bytes
    ///   of the word (e.g. only the low byte, or treats `x` as an integer
    ///   magnitude);
    /// * the `0x7F` cases (all-`0x7F` word and a lone `0x7F` per position)
    ///   pin the threshold at exactly `>= 128`, ruling out an off-by-one
    ///   such as `> 0x80` or `>= 0x7F`;
    /// * `0`, `usize::MAX`, all-`0x01` and assorted small values guard
    ///   against a constant return value.
    #[test]
    fn result_equals_per_byte_high_bit_oracle() {
        const N: usize = size_of::<usize>();

        let mut words = vec![
            0usize,
            usize::MAX,
            0x41,
            0x80,
            0xFF,
            usize::from_ne_bytes([0x7F; N]),
            usize::from_ne_bytes([0x01; N]),
        ];
        for i in 0..N {
            for probe in [0x80u8, 0xFF, 0x7F] {
                let mut b = [0u8; N];
                b[i] = probe;
                words.push(usize::from_ne_bytes(b));
                // same probe but on an otherwise all-ascii word
                let mut b = [0x7Fu8; N];
                b[i] = probe;
                words.push(usize::from_ne_bytes(b));
            }
        }

        for w in words {
            assert_eq!(
                contains_nonascii(w),
                spec_contains_nonascii(w),
                "contract violated for word {w:#018x}"
            );
        }
    }
}
