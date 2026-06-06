//! Extracted from `core::str::validations::utf8_acc_cont_byte`.
//!
//! Returns the value of `ch` updated with continuation byte `byte`.

/// Mask of the value bits of a continuation byte.
const CONT_MASK: u8 = 0b0011_1111;

#[inline]
pub const fn utf8_acc_cont_byte(ch: u32, byte: u8) -> u32 {
    (ch << 6) | (byte & CONT_MASK) as u32
}

#[cfg(test)]
mod tests {
    use super::utf8_acc_cont_byte;

    #[test]
    fn shifts_accumulator_and_ors_low_6_bits() {
        // ch = 0b00010, byte = 0b10_101010
        // result = (0b00010 << 6) | 0b101010 = 0b00010_101010 = 0x0AA
        assert_eq!(utf8_acc_cont_byte(0b00010, 0b1010_1010), 0b00010_101010);
    }

    #[test]
    fn ignores_top_two_bits_of_byte() {
        // top two bits of byte are dropped by CONT_MASK
        assert_eq!(utf8_acc_cont_byte(0, 0xFF), 0x3F);
        assert_eq!(utf8_acc_cont_byte(0, 0xBF), 0x3F);
        assert_eq!(utf8_acc_cont_byte(0, 0x80), 0x00);
    }

    #[test]
    fn typical_2byte_utf8() {
        // U+00A9 © encoded as 0xC2 0xA9
        // init = 0xC2 & 0x1F = 0x02
        // result = (0x02 << 6) | (0xA9 & 0x3F) = 0x80 | 0x29 = 0xA9
        let init: u32 = 0x02;
        assert_eq!(utf8_acc_cont_byte(init, 0xA9), 0xA9);
    }
}
