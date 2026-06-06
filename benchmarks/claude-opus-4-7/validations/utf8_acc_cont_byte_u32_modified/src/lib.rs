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

    /// A curated set of `u32` values exercising the relevant structure:
    /// zero, one, all-ones, alternating patterns, powers of two near the
    /// 6-bit shift boundary, and values with bits set in the top 6 places
    /// (which must be discarded by `<< 6`) as well as the bottom 26
    /// (which must survive).
    const CH_SAMPLES: &[u32] = &[
        0x0000_0000,
        0x0000_0001,
        0x0000_003F,
        0x0000_0040,
        0x0000_0041,
        0x0000_FFFF,
        0x00FF_FFFF,
        0x03FF_FFFF, // largest value preserved by `<< 6`
        0x0400_0000, // smallest value fully lost by `<< 6`
        0xAAAA_AAAA,
        0x5555_5555,
        0xFC00_0000, // only top-6 bits set: result must depend only on byte
        0xFFFF_FFFF,
    ];

    // --- Postcondition 1: low 6 bits of result are exactly low 6 bits of byte. ---
    //
    // This pins down the "byte contributes its low 6 bits, nothing more,
    // nothing less" half of the contract. A buggy mask (0x1F, 0x7F, …) or
    // a wrong shift amount would be detected here.
    #[test]
    fn low_six_bits_of_result_match_low_six_bits_of_byte() {
        for &ch in CH_SAMPLES {
            for byte in 0u8..=255 {
                let result = utf8_acc_cont_byte(ch, byte);
                assert_eq!(
                    result & 0x3F,
                    (byte & 0x3F) as u32,
                    "ch = {:#010x}, byte = {:#04x}",
                    ch,
                    byte,
                );
            }
        }
    }

    // --- Postcondition 2: bits above position 6 are `ch` shifted left by 6. ---
    //
    // Equivalently, `result >> 6 == ch & 0x03FF_FFFF`: the low 26 bits of
    // `ch` end up in positions 6..32, and the top 6 bits of `ch` are
    // discarded. A wrong shift width or a corrupted accumulator path
    // would fail this check.
    #[test]
    fn high_bits_of_result_match_ch_shifted() {
        for &ch in CH_SAMPLES {
            for byte in 0u8..=255 {
                let result = utf8_acc_cont_byte(ch, byte);
                assert_eq!(
                    result >> 6,
                    ch & 0x03FF_FFFF,
                    "ch = {:#010x}, byte = {:#04x}",
                    ch,
                    byte,
                );
            }
        }
    }

    // --- Failure conditions: there are none. ---
    //
    // The function is total: it takes any `u32` and any `u8`, performs a
    // shift by a fixed small constant (well-defined) and a bitwise OR
    // (never overflows), so it never panics. This test simply documents
    // that fact by exercising the extremes without expecting any failure.
    #[test]
    fn total_function_never_panics_on_extremes() {
        let _ = utf8_acc_cont_byte(0, 0);
        let _ = utf8_acc_cont_byte(u32::MAX, 0);
        let _ = utf8_acc_cont_byte(0, u8::MAX);
        let _ = utf8_acc_cont_byte(u32::MAX, u8::MAX);
    }

    // --- Retained concrete vectors as anchors. ---
    //
    // These pin the function's value on a couple of distinguished inputs
    // so a regression that shifts the contract uniformly (e.g. swapping
    // arguments) is caught even before the property checks run.
    #[test]
    fn concrete_vectors() {
        // From the original test: (0b00010 << 6) | 0b101010.
        assert_eq!(utf8_acc_cont_byte(0b00010, 0b1010_1010), 0b00010_101010);
        // U+00A9 © encoded as 0xC2 0xA9; init = 0xC2 & 0x1F = 0x02.
        assert_eq!(utf8_acc_cont_byte(0x02, 0xA9), 0xA9);
    }
}
