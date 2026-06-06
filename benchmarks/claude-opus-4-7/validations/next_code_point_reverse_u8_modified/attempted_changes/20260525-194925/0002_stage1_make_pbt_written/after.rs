//! Extracted from `core::str::validations::next_code_point_reverse`.
//!
//! Reads the last code point out of a byte iterator (assuming a UTF-8-like
//! encoding).
//!
//! The source is generic over `I: DoubleEndedIterator<Item = &'a u8>`.
//! This crate monomorphizes the iterator to `core::slice::Iter<'a, u8>`
//! (the most common caller in `core::str`).
//!
//! Private helpers `utf8_first_byte`, `utf8_acc_cont_byte`, and
//! `utf8_is_cont_byte` are inlined verbatim.

use core::slice::Iter;

/// Mask of the value bits of a continuation byte.
const CONT_MASK: u8 = 0b0011_1111;

#[inline]
const fn utf8_first_byte(byte: u8, width: u32) -> u32 {
    (byte & (0x7F >> width)) as u32
}

#[inline]
const fn utf8_acc_cont_byte(ch: u32, byte: u8) -> u32 {
    (ch << 6) | (byte & CONT_MASK) as u32
}

#[inline]
const fn utf8_is_cont_byte(byte: u8) -> bool {
    (byte as i8) < -64
}

/// # Safety
///
/// `bytes` must produce a valid UTF-8-like (UTF-8 or WTF-8) string.
#[inline]
pub unsafe fn next_code_point_reverse<'a>(bytes: &mut Iter<'a, u8>) -> Option<u32> {
    // Decode UTF-8
    let w = match *bytes.next_back()? {
        next_byte if next_byte < 128 => return Some(next_byte as u32),
        back_byte => back_byte,
    };

    // Multibyte case follows
    // Decode from a byte combination out of: [x [y [z w]]]
    let mut ch;
    // SAFETY: `bytes` produces an UTF-8-like string,
    // so the iterator must produce a value here.
    let z = unsafe { *bytes.next_back().unwrap_unchecked() };
    ch = utf8_first_byte(z, 2);
    if utf8_is_cont_byte(z) {
        // SAFETY: `bytes` produces an UTF-8-like string,
        // so the iterator must produce a value here.
        let y = unsafe { *bytes.next_back().unwrap_unchecked() };
        ch = utf8_first_byte(y, 3);
        if utf8_is_cont_byte(y) {
            // SAFETY: `bytes` produces an UTF-8-like string,
            // so the iterator must produce a value here.
            let x = unsafe { *bytes.next_back().unwrap_unchecked() };
            ch = utf8_first_byte(x, 4);
            ch = utf8_acc_cont_byte(ch, y);
        }
        ch = utf8_acc_cont_byte(ch, z);
    }
    ch = utf8_acc_cont_byte(ch, w);

    Some(ch)
}

#[cfg(test)]
mod tests {
    use super::next_code_point_reverse;

    #[test]
    fn ascii_byte_returns_single_codepoint() {
        let s = b"A";
        let mut it = s.iter();
        let cp = unsafe { next_code_point_reverse(&mut it) };
        assert_eq!(cp, Some(0x41));
        let cp2 = unsafe { next_code_point_reverse(&mut it) };
        assert_eq!(cp2, None);
    }

    #[test]
    fn two_byte_codepoint_copyright() {
        // U+00A9 © -> 0xC2 0xA9
        let s = b"\xC2\xA9";
        let mut it = s.iter();
        let cp = unsafe { next_code_point_reverse(&mut it) };
        assert_eq!(cp, Some(0xA9));
    }

    #[test]
    fn three_byte_codepoint_bmp() {
        // U+20AC € -> 0xE2 0x82 0xAC
        let s = b"\xE2\x82\xAC";
        let mut it = s.iter();
        let cp = unsafe { next_code_point_reverse(&mut it) };
        assert_eq!(cp, Some(0x20AC));
    }

    #[test]
    fn four_byte_codepoint_supplementary() {
        // U+1F600 😀 -> 0xF0 0x9F 0x98 0x80
        let s = b"\xF0\x9F\x98\x80";
        let mut it = s.iter();
        let cp = unsafe { next_code_point_reverse(&mut it) };
        assert_eq!(cp, Some(0x1F600));
    }

    #[test]
    fn empty_iterator_returns_none() {
        let s: &[u8] = b"";
        let mut it = s.iter();
        let cp = unsafe { next_code_point_reverse(&mut it) };
        assert_eq!(cp, None);
    }

    #[test]
    fn sequence_of_codepoints_reverse() {
        let s = "Aé€😀".as_bytes();
        let mut it = s.iter();
        unsafe {
            assert_eq!(next_code_point_reverse(&mut it), Some(0x1F600));
            assert_eq!(next_code_point_reverse(&mut it), Some(0x20AC));
            assert_eq!(next_code_point_reverse(&mut it), Some(0xE9));
            assert_eq!(next_code_point_reverse(&mut it), Some(0x41));
            assert_eq!(next_code_point_reverse(&mut it), None);
        }
    }

    // ----- Property-based tests -----

    /// Postcondition (single code point): for *every* valid Unicode scalar
    /// value `cp`, encoding `cp` to UTF-8 and then calling
    /// `next_code_point_reverse` on the resulting bytes recovers `Some(cp)`
    /// and fully drains the iterator. This pins down the decoding contract
    /// across all four encoding widths (1, 2, 3, and 4 bytes) and at every
    /// boundary (0x00, 0x7F, 0x80, 0x7FF, 0x800, 0xFFFF, 0x10000, 0x10FFFF,
    /// surrogate-adjacent values, ...).
    #[test]
    fn prop_single_codepoint_roundtrip() {
        let mut buf = [0u8; 4];
        for cp in 0u32..=0x10FFFF {
            let Some(c) = char::from_u32(cp) else { continue };
            let s = c.encode_utf8(&mut buf);
            let bytes = s.as_bytes();
            let mut it = bytes.iter();
            let decoded = unsafe { next_code_point_reverse(&mut it) };
            assert_eq!(decoded, Some(cp), "round-trip failed for U+{:04X}", cp);
            // Consumption postcondition: the iterator is drained exactly.
            assert!(
                it.as_slice().is_empty(),
                "iterator not drained for U+{:04X}",
                cp
            );
        }
    }

    /// Postcondition (sequence + consumption): for any valid UTF-8 string,
    /// repeatedly calling `next_code_point_reverse` yields the same sequence
    /// of `u32` values as `s.chars().rev()`. This is the multi-codepoint
    /// extension of the single-codepoint round-trip and is what catches
    /// bugs in *how many* bytes the function consumes: an off-by-one in the
    /// consumption count would land the next call on a continuation byte
    /// and produce a wrong code point (or trigger the `unwrap_unchecked`
    /// branch). The set of strings exercises ASCII, mixed widths, and
    /// every encoding-width boundary in a single byte slice.
    #[test]
    fn prop_string_matches_chars_rev() {
        let strings: &[&str] = &[
            "",
            "A",
            "hello, world",
            "café",
            "Aé€😀",
            "🦀🦀🦀",
            "Hello, 世界!",
            "abc\u{0080}\u{07FF}\u{0800}\u{FFFF}\u{10000}\u{10FFFF}",
        ];
        for s in strings {
            let mut it = s.as_bytes().iter();
            let mut expected = s.chars().rev();
            loop {
                let got = unsafe { next_code_point_reverse(&mut it) };
                let want = expected.next().map(|c| c as u32);
                assert_eq!(got, want, "mismatch on string {:?}", s);
                if got.is_none() {
                    break;
                }
            }
            // After drainage, the iterator stays empty.
            assert!(it.as_slice().is_empty(), "leftover bytes on {:?}", s);
        }
    }

    /// Failure clause: the only way `next_code_point_reverse` returns
    /// `None` is when the iterator is empty, and once it is empty it
    /// stays `None` on every subsequent call (no panics, no spurious
    /// `Some`). A buggy implementation that, say, returned `Some(0)` on
    /// the second call would be caught here.
    #[test]
    fn prop_empty_iterator_stays_none() {
        let s: &[u8] = b"";
        let mut it = s.iter();
        for _ in 0..8 {
            assert_eq!(unsafe { next_code_point_reverse(&mut it) }, None);
            assert!(it.as_slice().is_empty());
        }
    }
}
