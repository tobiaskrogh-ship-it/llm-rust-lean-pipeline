// unsupported: large `&'static [u8; N]` (or similar) lookup tables used as
// classifiers fail Hax extraction. `cargo hax into lean` accepts the
// definition, but the generated Lean refers to a missing symbol and
// `lake build` fails with:
//   Unknown identifier 'UTF8_CHAR_WIDTH'
// (with the constant's own name). The Hax Lean prelude has no representation
// for static byte arrays referenced by an indexing expression like
// `TABLE[b as usize]`, so any function that classifies a byte via such a
// table is unextractable.
//
// Workaround: inline the classification as an `if`/`else` chain over the
// equivalent ranges. Group consecutive identical entries into range tests
// using simple `<` / `>=` comparisons (or `match`-with-range arms if the
// ranges are short). The resulting code has no static-array reference, so
// extraction goes through cleanly. This only works when the table encodes
// piecewise-constant data over a small number of contiguous ranges (UTF-8
// byte widths, character classes, parser DFA columns with few distinct
// outputs, ...). Genuinely arbitrary 256-entry tables (e.g. cryptographic
// S-boxes) cannot be flattened this way and remain unfixable at this
// stage — flag them as such instead.

// before

// https://tools.ietf.org/html/rfc3629
const UTF8_CHAR_WIDTH: &[u8; 256] = &[
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 0
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 1
    // ... (rows 0x20..=0x7F all 1, 0x80..=0xBF all 0, 0xC0/0xC1 = 0,
    // 0xC2..=0xDF = 2, 0xE0..=0xEF = 3, 0xF0..=0xF4 = 4, 0xF5..=0xFF = 0)
    4, 4, 4, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // F
];

#[inline]
const fn utf8_char_width(b: u8) -> usize {
    UTF8_CHAR_WIDTH[b as usize] as usize
}

// after

/// Same classification as the `UTF8_CHAR_WIDTH` table, expressed as an
/// `if`/`else` chain over the underlying RFC 3629 byte ranges. No static
/// array survives extraction.
fn utf8_char_width(b: u8) -> usize {
    if b < 0x80 {
        1
    } else if b < 0xC2 {
        // 0x80..=0xBF are continuation bytes; 0xC0/0xC1 are overlong.
        0
    } else if b < 0xE0 {
        // 0xC2..=0xDF
        2
    } else if b < 0xF0 {
        // 0xE0..=0xEF
        3
    } else if b < 0xF5 {
        // 0xF0..=0xF4
        4
    } else {
        // 0xF5..=0xFF
        0
    }
}
