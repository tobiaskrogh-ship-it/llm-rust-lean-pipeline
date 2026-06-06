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

    // The function is total on `u8` and never panics (implicitly checked by
    // every test below, since each exhaustively iterates over a sub-range of
    // the 256 possible inputs and would panic-fail otherwise).
    //
    // The six tests below partition `0x00..=0xFF` and together fully pin down
    // the function's behaviour.

    /// Postcondition: every ASCII byte has width 1.
    #[test]
    fn ascii_range_has_width_1() {
        for b in 0x00u8..=0x7F {
            assert_eq!(utf8_char_width(b), 1, "byte {:#04x}", b);
        }
    }

    /// Postcondition: continuation bytes (0x80..=0xBF) and the two overlong
    /// 2-byte leaders (0xC0, 0xC1) are not valid first bytes, so width 0.
    #[test]
    fn continuation_and_overlong_have_width_0() {
        for b in 0x80u8..=0xC1 {
            assert_eq!(utf8_char_width(b), 0, "byte {:#04x}", b);
        }
    }

    /// Postcondition: 0xC2..=0xDF are 2-byte sequence leaders.
    #[test]
    fn two_byte_leaders_have_width_2() {
        for b in 0xC2u8..=0xDF {
            assert_eq!(utf8_char_width(b), 2, "byte {:#04x}", b);
        }
    }

    /// Postcondition: 0xE0..=0xEF are 3-byte sequence leaders.
    #[test]
    fn three_byte_leaders_have_width_3() {
        for b in 0xE0u8..=0xEF {
            assert_eq!(utf8_char_width(b), 3, "byte {:#04x}", b);
        }
    }

    /// Postcondition: 0xF0..=0xF4 are 4-byte sequence leaders.
    /// (RFC 3629 caps UTF-8 at U+10FFFF, so 0xF5..=0xFF are invalid.)
    #[test]
    fn four_byte_leaders_have_width_4() {
        for b in 0xF0u8..=0xF4 {
            assert_eq!(utf8_char_width(b), 4, "byte {:#04x}", b);
        }
    }

    /// Postcondition: 0xF5..=0xFF are not valid UTF-8 first bytes, so width 0.
    #[test]
    fn high_invalid_have_width_0() {
        for b in 0xF5u8..=0xFF {
            assert_eq!(utf8_char_width(b), 0, "byte {:#04x}", b);
        }
    }
}
