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
}
