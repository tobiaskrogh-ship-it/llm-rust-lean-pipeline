//! Extracted from `core::str::validations::utf8_char_width`.
//!
//! Given a first byte, determines how many bytes are in this UTF-8 character.

// The original Rust source used a 256-byte lookup table indexed by `b as usize`.
// Hax extracts such a literal as a Lean `#v[...]` vector whose elaboration
// recurses once per element, and 256 elements blows past Lean's default
// `maxRecDepth` — `lake build` then fails with `maximum recursion depth has
// been reached`, plus cascading `Unknown identifier 'UTF8_CHAR_WIDTH'` and
// `declaration uses 'sorry'` errors. The lookup table is range-compressible:
// only 6 contiguous byte ranges carry distinct values, so we replace it with
// a branch chain over those ranges. Semantically identical on every input.
// See `rewrite_patterns/large_const_lookup_table_to_branches.rs`.

// https://tools.ietf.org/html/rfc3629
#[must_use]
#[inline]
pub const fn utf8_char_width(b: u8) -> usize {
    if b < 0x80 {
        // 0x00..=0x7F: ASCII, width 1.
        1
    } else if b < 0xC2 {
        // 0x80..=0xC1: continuation bytes + overlong 2-byte leaders — invalid.
        0
    } else if b < 0xE0 {
        // 0xC2..=0xDF: valid 2-byte leaders.
        2
    } else if b < 0xF0 {
        // 0xE0..=0xEF: valid 3-byte leaders.
        3
    } else if b < 0xF5 {
        // 0xF0..=0xF4: valid 4-byte leaders.
        4
    } else {
        // 0xF5..=0xFF: beyond U+10FFFF — invalid.
        0
    }
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
