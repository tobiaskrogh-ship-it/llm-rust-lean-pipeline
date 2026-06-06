//! Extracted from `core::str::validations::next_code_point`.
//!
//! Reads the next code point out of a byte iterator (assuming a
//! UTF-8-like encoding).
//!
//! The source is generic over `I: Iterator<Item = &'a u8>`. This crate
//! monomorphizes the generic iterator to `core::slice::Iter<'a, u8>` (the
//! most common caller in `core::str`).
//!
//! Private helpers `utf8_first_byte` and `utf8_acc_cont_byte` are inlined
//! verbatim below.

use core::slice::Iter;

/// Mask of the value bits of a continuation byte.
const CONT_MASK: u8 = 0b0011_1111;

/// Returns the initial codepoint accumulator for the first byte.
#[inline]
const fn utf8_first_byte(byte: u8, width: u32) -> u32 {
    (byte & (0x7F >> width)) as u32
}

/// Returns the value of `ch` updated with continuation byte `byte`.
#[inline]
const fn utf8_acc_cont_byte(ch: u32, byte: u8) -> u32 {
    (ch << 6) | (byte & CONT_MASK) as u32
}

/// # Safety
///
/// `bytes` must produce a valid UTF-8-like (UTF-8 or WTF-8) string.
#[inline]
pub unsafe fn next_code_point<'a>(bytes: &mut Iter<'a, u8>) -> Option<u32> {
    // Decode UTF-8
    let x = *bytes.next()?;
    if x < 128 {
        return Some(x as u32);
    }

    // Multibyte case follows
    // Decode from a byte combination out of: [[[x y] z] w]
    // NOTE: Performance is sensitive to the exact formulation here
    let init = utf8_first_byte(x, 2);
    // SAFETY: `bytes` produces an UTF-8-like string,
    // so the iterator must produce a value here.
    let y = unsafe { *bytes.next().unwrap_unchecked() };
    let mut ch = utf8_acc_cont_byte(init, y);
    if x >= 0xE0 {
        // [[x y z] w] case
        // 5th bit in 0xE0 .. 0xEF is always clear, so `init` is still valid
        // SAFETY: `bytes` produces an UTF-8-like string,
        // so the iterator must produce a value here.
        let z = unsafe { *bytes.next().unwrap_unchecked() };
        let y_z = utf8_acc_cont_byte((y & CONT_MASK) as u32, z);
        ch = init << 12 | y_z;
        if x >= 0xF0 {
            // [x y z w] case
            // use only the lower 3 bits of `init`
            // SAFETY: `bytes` produces an UTF-8-like string,
            // so the iterator must produce a value here.
            let w = unsafe { *bytes.next().unwrap_unchecked() };
            ch = (init & 7) << 18 | utf8_acc_cont_byte(y_z, w);
        }
    }

    Some(ch)
}

#[cfg(test)]
mod tests {
    use super::next_code_point;

    #[test]
    fn ascii_byte_returns_single_codepoint() {
        let s = b"A";
        let mut it = s.iter();
        // SAFETY: input is valid UTF-8.
        let cp = unsafe { next_code_point(&mut it) };
        assert_eq!(cp, Some(0x41));
        // No more bytes
        let cp2 = unsafe { next_code_point(&mut it) };
        assert_eq!(cp2, None);
    }

    #[test]
    fn two_byte_codepoint_copyright() {
        // U+00A9 © -> 0xC2 0xA9
        let s = b"\xC2\xA9";
        let mut it = s.iter();
        let cp = unsafe { next_code_point(&mut it) };
        assert_eq!(cp, Some(0xA9));
    }

    #[test]
    fn three_byte_codepoint_bmp() {
        // U+20AC € -> 0xE2 0x82 0xAC
        let s = b"\xE2\x82\xAC";
        let mut it = s.iter();
        let cp = unsafe { next_code_point(&mut it) };
        assert_eq!(cp, Some(0x20AC));
    }

    #[test]
    fn four_byte_codepoint_supplementary() {
        // U+1F600 😀 -> 0xF0 0x9F 0x98 0x80
        let s = b"\xF0\x9F\x98\x80";
        let mut it = s.iter();
        let cp = unsafe { next_code_point(&mut it) };
        assert_eq!(cp, Some(0x1F600));
    }

    #[test]
    fn empty_iterator_returns_none() {
        let s: &[u8] = b"";
        let mut it = s.iter();
        let cp = unsafe { next_code_point(&mut it) };
        assert_eq!(cp, None);
    }

    #[test]
    fn sequence_of_codepoints() {
        let s = "Aé€😀".as_bytes();
        let mut it = s.iter();
        unsafe {
            assert_eq!(next_code_point(&mut it), Some(0x41));
            assert_eq!(next_code_point(&mut it), Some(0xE9));
            assert_eq!(next_code_point(&mut it), Some(0x20AC));
            assert_eq!(next_code_point(&mut it), Some(0x1F600));
            assert_eq!(next_code_point(&mut it), None);
        }
    }

    // ----------------------------------------------------------------
    // Property-based contract tests
    //
    // These are expressed as deterministic, domain-exhaustive checks
    // (no external proptest dependency) so that they remain meaningful
    // as downstream proof obligations.
    // ----------------------------------------------------------------

    /// Decode exactly one code point from the UTF-8 encoding of `c`.
    /// Returns the decoded value and the number of bytes left unread.
    fn decode_one(c: char) -> (Option<u32>, usize) {
        let mut buf = [0u8; 4];
        let encoded = c.encode_utf8(&mut buf);
        let bytes = encoded.as_bytes();
        let mut it = bytes.iter();
        // SAFETY: `bytes` is the UTF-8 encoding of a `char`, hence valid UTF-8.
        let cp = unsafe { next_code_point(&mut it) };
        (cp, it.len())
    }

    /// Postcondition (core decode contract), checked over the *entire*
    /// domain of Unicode scalar values (all `u32` for which `char::from_u32`
    /// succeeds — every width and every range boundary, surrogates excluded):
    ///
    /// * the returned value equals the scalar value that was encoded, and
    /// * the call consumes *exactly* the bytes of that encoding
    ///   (iterator empty afterwards => not too few / not too many bytes read).
    ///
    /// This simultaneously pins the 1-, 2-, 3- and 4-byte branches and the
    /// `utf8_first_byte` / `utf8_acc_cont_byte` reconstruction across the
    /// full input space. A buggy implementation that returned any other
    /// valid scalar, or that mis-counted continuation bytes, would fail.
    #[test]
    fn prop_roundtrip_every_scalar_value() {
        for u in 0u32..=0x10_FFFF {
            if let Some(c) = char::from_u32(u) {
                let (cp, remaining) = decode_one(c);
                assert_eq!(cp, Some(u), "decoded value mismatch for U+{u:04X}");
                assert_eq!(
                    remaining, 0,
                    "did not consume the full encoding for U+{u:04X}"
                );
            }
        }
    }

    /// Independent claim: iterator-advancement / resumption.
    ///
    /// Over a long buffer containing many code points of mixed widths,
    /// successive calls yield exactly `s.chars()` (as `u32`), then `None`,
    /// and stay `None`. This is *not* implied by the single-code-point
    /// roundtrip above: it additionally pins that each call advances the
    /// shared iterator by precisely one code point's UTF-8 width (no
    /// over- or under-read into the following code point) and that the
    /// `None` termination occurs exactly at end-of-input and is stable.
    #[test]
    fn prop_sequence_matches_chars_iterator() {
        let sample = "\u{0}\u{1}A~\u{7F}\u{80}é\u{7FF}\u{800}€\u{D7FF}\
                      \u{E000}\u{FFFF}\u{10000}😀\u{10FFFF}本語";
        let big = sample.repeat(64);
        let bytes = big.as_bytes();
        let mut it = bytes.iter();
        for expected in big.chars() {
            // SAFETY: `bytes` comes from a `String`, hence valid UTF-8.
            let cp = unsafe { next_code_point(&mut it) };
            assert_eq!(cp, Some(expected as u32));
        }
        // Termination: exhausted exactly at the end...
        let end = unsafe { next_code_point(&mut it) };
        assert_eq!(end, None);
        // ...and remains `None` on further calls.
        let end_again = unsafe { next_code_point(&mut it) };
        assert_eq!(end_again, None);
    }
}
