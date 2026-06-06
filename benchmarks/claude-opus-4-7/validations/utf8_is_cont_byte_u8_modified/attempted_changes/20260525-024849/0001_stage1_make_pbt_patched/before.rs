//! Extracted from `core::str::validations::utf8_is_cont_byte`.
//!
//! Checks whether the byte is a UTF-8 continuation byte (i.e., starts with the
//! bits `10`).

#[inline]
pub const fn utf8_is_cont_byte(byte: u8) -> bool {
    (byte as i8) < -64
}

#[cfg(test)]
mod tests {
    use super::utf8_is_cont_byte;

    #[test]
    fn continuation_bytes_in_range_0x80_0xbf() {
        assert!(utf8_is_cont_byte(0x80));
        assert!(utf8_is_cont_byte(0xA9));
        assert!(utf8_is_cont_byte(0xBF));
    }

    #[test]
    fn non_continuation_bytes() {
        // ASCII
        assert!(!utf8_is_cont_byte(0x00));
        assert!(!utf8_is_cont_byte(0x7F));
        // 2-byte leading
        assert!(!utf8_is_cont_byte(0xC0));
        assert!(!utf8_is_cont_byte(0xDF));
        // 3-byte leading
        assert!(!utf8_is_cont_byte(0xE0));
        // 4-byte leading
        assert!(!utf8_is_cont_byte(0xF0));
        // Invalid
        assert!(!utf8_is_cont_byte(0xFF));
    }
}
