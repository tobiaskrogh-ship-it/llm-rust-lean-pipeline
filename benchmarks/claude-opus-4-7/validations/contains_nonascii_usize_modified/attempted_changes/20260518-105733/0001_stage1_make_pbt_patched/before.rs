//! Extracted from `core::str::validations::contains_nonascii`.
//!
//! Returns `true` if any byte in the word `x` is nonascii (>= 128).
//!
//! Self-contained reimplementation: the source uses `usize::repeat_u8(0x80)`
//! (an unstable private `core` helper). We inline the equivalent computation
//! `usize::from_ne_bytes([0x80; size_of::<usize>()])` as a portable const.

/// Returns a `usize` where every byte equals `x` (inlined from
/// `core::num::repeat_u8`).
const fn repeat_u8(x: u8) -> usize {
    usize::from_ne_bytes([x; size_of::<usize>()])
}

const NONASCII_MASK: usize = repeat_u8(0x80);

#[inline]
pub const fn contains_nonascii(x: usize) -> bool {
    (x & NONASCII_MASK) != 0
}

#[cfg(test)]
mod tests {
    use super::contains_nonascii;

    #[test]
    fn all_ascii_returns_false() {
        assert!(!contains_nonascii(0));
        // word with each byte set to 0x7F
        let ascii: usize = usize::from_ne_bytes([0x7F; size_of::<usize>()]);
        assert!(!contains_nonascii(ascii));
        // single ASCII byte at low position
        assert!(!contains_nonascii(0x41));
    }

    #[test]
    fn any_high_bit_set_returns_true() {
        // each byte 0x80
        let m: usize = usize::from_ne_bytes([0x80; size_of::<usize>()]);
        assert!(contains_nonascii(m));
        // single non-ASCII byte
        assert!(contains_nonascii(0x80));
        assert!(contains_nonascii(0xFF));
    }

    #[test]
    fn mixed_word_with_one_nonascii_byte() {
        // [0x7F, 0x7F, ..., 0x7F, 0x80] (last byte non-ascii)
        let mut bytes = [0x7Fu8; size_of::<usize>()];
        let n = bytes.len();
        bytes[n - 1] = 0x80;
        let w = usize::from_ne_bytes(bytes);
        assert!(contains_nonascii(w));
    }
}
