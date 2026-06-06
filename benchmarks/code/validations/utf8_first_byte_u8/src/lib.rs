//! Extracted from `core::str::validations::utf8_first_byte`.
//!
//! Returns the initial codepoint accumulator for the first byte.
//! The first byte is special, only want bottom 5 bits for width 2, 4 bits
//! for width 3, and 3 bits for width 4.

#[inline]
pub const fn utf8_first_byte(byte: u8, width: u32) -> u32 {
    (byte & (0x7F >> width)) as u32
}

#[cfg(test)]
mod tests {
    use super::utf8_first_byte;

    #[test]
    fn ascii_width_passes_byte_low_bits() {
        // For width 2, mask is 0x1F. 0xC2 -> 0x02
        assert_eq!(utf8_first_byte(0xC2, 2), 0x02);
        // For width 3, mask is 0x0F. 0xE0 -> 0x00
        assert_eq!(utf8_first_byte(0xE0, 3), 0x00);
        assert_eq!(utf8_first_byte(0xEF, 3), 0x0F);
        // For width 4, mask is 0x07. 0xF0 -> 0x00, 0xF4 -> 0x04
        assert_eq!(utf8_first_byte(0xF0, 4), 0x00);
        assert_eq!(utf8_first_byte(0xF4, 4), 0x04);
    }

    #[test]
    fn width_zero_keeps_low_7_bits() {
        // mask 0x7F
        assert_eq!(utf8_first_byte(0x7F, 0), 0x7F);
        assert_eq!(utf8_first_byte(0xFF, 0), 0x7F);
    }
}
