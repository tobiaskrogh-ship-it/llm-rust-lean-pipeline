//! Extracted from `core::str::validations::utf8_char_width`.
//!
//! Given a first byte, determines how many bytes are in this UTF-8 character.

// https://tools.ietf.org/html/rfc3629
const UTF8_CHAR_WIDTH: &[u8; 256] = &[
    // 1  2  3  4  5  6  7  8  9  A  B  C  D  E  F
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 0
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 1
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 2
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 3
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 4
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 5
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 6
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 7
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // 8
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // 9
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // A
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // B
    0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, // C
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, // D
    3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, // E
    4, 4, 4, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // F
];

#[must_use]
#[inline]
pub const fn utf8_char_width(b: u8) -> usize {
    UTF8_CHAR_WIDTH[b as usize] as usize
}

#[cfg(test)]
mod tests {
    use super::utf8_char_width;

    #[test]
    fn ascii_bytes_have_width_1() {
        assert_eq!(utf8_char_width(0x00), 1);
        assert_eq!(utf8_char_width(0x41), 1); // 'A'
        assert_eq!(utf8_char_width(0x7F), 1);
    }

    #[test]
    fn continuation_bytes_have_width_0() {
        assert_eq!(utf8_char_width(0x80), 0);
        assert_eq!(utf8_char_width(0xBF), 0);
    }

    #[test]
    fn leading_bytes_widths() {
        // 0xC0/0xC1 invalid, width 0
        assert_eq!(utf8_char_width(0xC0), 0);
        assert_eq!(utf8_char_width(0xC1), 0);
        // 0xC2-0xDF 2-byte starts
        assert_eq!(utf8_char_width(0xC2), 2);
        assert_eq!(utf8_char_width(0xDF), 2);
        // 0xE0-0xEF 3-byte starts
        assert_eq!(utf8_char_width(0xE0), 3);
        assert_eq!(utf8_char_width(0xEF), 3);
        // 0xF0-0xF4 4-byte starts
        assert_eq!(utf8_char_width(0xF0), 4);
        assert_eq!(utf8_char_width(0xF4), 4);
        // 0xF5-0xFF invalid
        assert_eq!(utf8_char_width(0xF5), 0);
        assert_eq!(utf8_char_width(0xFF), 0);
    }
}
