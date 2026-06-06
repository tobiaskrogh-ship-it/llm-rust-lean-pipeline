//! Extracted from `core::str::validations::run_utf8_validation`.
//!
//! Walks through `v` checking that it's a valid UTF-8 sequence, returning
//! `Ok(())` in that case, or, if it is invalid, `Err(err)`.
//!
//! Inlining notes:
//! - `Utf8Error` is reimplemented locally with the same `(valid_up_to, error_len)`
//!   shape.
//! - The source uses an unstable `const_eval_select!` macro to pick between a
//!   `usize::MAX` alignment in const context and `align_offset` at runtime. Since
//!   this crate is run-time only, the macro is replaced by the runtime branch
//!   directly. As a consequence the `const` qualifier is dropped.
//! - Private helpers `utf8_char_width`, `contains_nonascii`, `NONASCII_MASK`,
//!   and the local equivalent of `usize::repeat_u8` are all inlined here.

/// Reimplementation of `core::str::Utf8Error`'s data shape.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct Utf8Error {
    pub valid_up_to: usize,
    pub error_len: Option<u8>,
}

impl Utf8Error {
    #[must_use]
    #[inline]
    pub const fn valid_up_to(&self) -> usize {
        self.valid_up_to
    }

    #[must_use]
    #[inline]
    pub const fn error_len(&self) -> Option<usize> {
        match self.error_len {
            Some(len) => Some(len as usize),
            None => None,
        }
    }
}

// ---- Inlined helpers from validations.rs ------------------------------------

/// Equivalent of `usize::repeat_u8` (unstable, `pub(crate)` in `core::num`).
const fn repeat_u8(x: u8) -> usize {
    usize::from_ne_bytes([x; size_of::<usize>()])
}

const NONASCII_MASK: usize = repeat_u8(0x80);

#[inline]
const fn contains_nonascii(x: usize) -> bool {
    (x & NONASCII_MASK) != 0
}

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

#[inline]
const fn utf8_char_width(b: u8) -> usize {
    UTF8_CHAR_WIDTH[b as usize] as usize
}

// ---- The main function -----------------------------------------------------

#[inline(always)]
pub fn run_utf8_validation(v: &[u8]) -> Result<(), Utf8Error> {
    let mut index = 0;
    let len = v.len();

    const USIZE_BYTES: usize = size_of::<usize>();

    let ascii_block_size = 2 * USIZE_BYTES;
    let blocks_end = if len >= ascii_block_size { len - ascii_block_size + 1 } else { 0 };
    // Source uses `const_eval_select!` to pick between `usize::MAX` (const) and
    // `align_offset` (runtime). At runtime we just call `align_offset` directly.
    let align = v.as_ptr().align_offset(USIZE_BYTES);

    while index < len {
        let old_offset = index;
        macro_rules! err {
            ($error_len: expr) => {
                return Err(Utf8Error { valid_up_to: old_offset, error_len: $error_len })
            };
        }

        macro_rules! next {
            () => {{
                index += 1;
                // we needed data, but there was none: error!
                if index >= len {
                    err!(None)
                }
                v[index]
            }};
        }

        let first = v[index];
        if first >= 128 {
            let w = utf8_char_width(first);
            // 2-byte encoding is for codepoints  \u{0080} to  \u{07ff}
            //        first  C2 80        last DF BF
            // 3-byte encoding is for codepoints  \u{0800} to  \u{ffff}
            //        first  E0 A0 80     last EF BF BF
            //   excluding surrogates codepoints  \u{d800} to  \u{dfff}
            //               ED A0 80 to       ED BF BF
            // 4-byte encoding is for codepoints \u{10000} to \u{10ffff}
            //        first  F0 90 80 80  last F4 8F BF BF
            match w {
                2 => {
                    if next!() as i8 >= -64 {
                        err!(Some(1))
                    }
                }
                3 => {
                    match (first, next!()) {
                        (0xE0, 0xA0..=0xBF)
                        | (0xE1..=0xEC, 0x80..=0xBF)
                        | (0xED, 0x80..=0x9F)
                        | (0xEE..=0xEF, 0x80..=0xBF) => {}
                        _ => err!(Some(1)),
                    }
                    if next!() as i8 >= -64 {
                        err!(Some(2))
                    }
                }
                4 => {
                    match (first, next!()) {
                        (0xF0, 0x90..=0xBF) | (0xF1..=0xF3, 0x80..=0xBF) | (0xF4, 0x80..=0x8F) => {}
                        _ => err!(Some(1)),
                    }
                    if next!() as i8 >= -64 {
                        err!(Some(2))
                    }
                    if next!() as i8 >= -64 {
                        err!(Some(3))
                    }
                }
                _ => err!(Some(1)),
            }
            index += 1;
        } else {
            // Ascii case, try to skip forward quickly.
            // When the pointer is aligned, read 2 words of data per iteration
            // until we find a word containing a non-ascii byte.
            if align != usize::MAX && align.wrapping_sub(index).is_multiple_of(USIZE_BYTES) {
                let ptr = v.as_ptr();
                while index < blocks_end {
                    // SAFETY: since `align - index` and `ascii_block_size` are
                    // multiples of `USIZE_BYTES`, `block = ptr.add(index)` is
                    // always aligned with a `usize` so it's safe to dereference
                    // both `block` and `block.add(1)`.
                    unsafe {
                        let block = ptr.add(index) as *const usize;
                        // break if there is a nonascii byte
                        let zu = contains_nonascii(*block);
                        let zv = contains_nonascii(*block.add(1));
                        if zu || zv {
                            break;
                        }
                    }
                    index += ascii_block_size;
                }
                // step from the point where the wordwise loop stopped
                while index < len && v[index] < 128 {
                    index += 1;
                }
            } else {
                index += 1;
            }
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{run_utf8_validation, Utf8Error};

    #[test]
    fn empty_slice_is_valid() {
        assert_eq!(run_utf8_validation(b""), Ok(()));
    }

    #[test]
    fn all_ascii_is_valid() {
        let s = b"hello, world! the quick brown fox jumps over the lazy dog";
        assert_eq!(run_utf8_validation(s), Ok(()));
    }

    #[test]
    fn valid_multibyte_codepoints() {
        // copyright + euro + smiley
        let s = "© € 😀".as_bytes();
        assert_eq!(run_utf8_validation(s), Ok(()));
    }

    #[test]
    fn mixed_ascii_and_multibyte() {
        let s = "Hello, é world! 🌍 the end".as_bytes();
        assert_eq!(run_utf8_validation(s), Ok(()));
    }

    #[test]
    fn rejects_lone_continuation_byte() {
        let s: &[u8] = &[0x80];
        let err = run_utf8_validation(s).unwrap_err();
        assert_eq!(err, Utf8Error { valid_up_to: 0, error_len: Some(1) });
    }

    #[test]
    fn rejects_truncated_2byte_sequence() {
        // 0xC2 is start of 2-byte, but no continuation follows
        let s: &[u8] = &[0xC2];
        let err = run_utf8_validation(s).unwrap_err();
        assert_eq!(err.valid_up_to(), 0);
        assert_eq!(err.error_len(), None);
    }

    #[test]
    fn rejects_truncated_3byte_sequence() {
        // 0xE2 0x82 then EOF (€ is 0xE2 0x82 0xAC)
        let s: &[u8] = &[0xE2, 0x82];
        let err = run_utf8_validation(s).unwrap_err();
        assert_eq!(err.valid_up_to(), 0);
        assert_eq!(err.error_len(), None);
    }

    #[test]
    fn rejects_surrogate() {
        // Surrogate U+D800 would be encoded as 0xED 0xA0 0x80 — invalid UTF-8.
        let s: &[u8] = &[0xED, 0xA0, 0x80];
        let err = run_utf8_validation(s).unwrap_err();
        assert_eq!(err.valid_up_to(), 0);
        // After reading the second byte we recognize it's outside the
        // permitted 0x80..=0x9F range for `0xED`, so error_len = Some(1).
        assert_eq!(err.error_len(), Some(1));
    }

    #[test]
    fn rejects_overlong_2byte_encoding() {
        // 0xC0 / 0xC1 are invalid leading bytes (overlong encodings).
        // utf8_char_width returns 0 for them, so we error with Some(1).
        let s: &[u8] = &[0xC0, 0x80];
        let err = run_utf8_validation(s).unwrap_err();
        assert_eq!(err.valid_up_to(), 0);
        assert_eq!(err.error_len(), Some(1));
    }

    #[test]
    fn rejects_byte_beyond_max_codepoint() {
        // 0xF5..=0xFF are invalid.
        let s: &[u8] = &[0xF5, 0x80, 0x80, 0x80];
        let err = run_utf8_validation(s).unwrap_err();
        assert_eq!(err.valid_up_to(), 0);
        assert_eq!(err.error_len(), Some(1));
    }

    #[test]
    fn valid_up_to_points_to_first_bad_byte() {
        // "ab" + bad byte
        let s: &[u8] = &[b'a', b'b', 0xFF];
        let err = run_utf8_validation(s).unwrap_err();
        assert_eq!(err.valid_up_to(), 2);
        assert_eq!(err.error_len(), Some(1));
    }

    #[test]
    fn long_ascii_triggers_wordwise_fastpath() {
        // 256 ascii bytes should exercise the SIMD-ish wordwise loop.
        let s = vec![b'a'; 256];
        assert_eq!(run_utf8_validation(&s), Ok(()));
    }

    #[test]
    fn long_ascii_with_bad_byte_at_end() {
        let mut s = vec![b'a'; 256];
        s.push(0xC2); // truncated 2-byte
        let err = run_utf8_validation(&s).unwrap_err();
        assert_eq!(err.valid_up_to(), 256);
        assert_eq!(err.error_len(), None);
    }

    #[test]
    fn utf8_error_accessors() {
        let e = Utf8Error { valid_up_to: 7, error_len: Some(2) };
        assert_eq!(e.valid_up_to(), 7);
        assert_eq!(e.error_len(), Some(2));
        let e2 = Utf8Error { valid_up_to: 3, error_len: None };
        assert_eq!(e2.error_len(), None);
    }

    // ---- Property-based tests ------------------------------------------
    //
    // Each `prop_*` test below states one independent contract clause.
    // `std::str::from_utf8` serves as the reference oracle when needed.
    // The properties are checked over a hand-rolled corpus that covers
    //   - every single byte (0..=255),
    //   - every 2-byte sequence whose leading byte sits on a boundary of
    //     the UTF-8 grammar (overlong starts, ASCII/multi-byte boundary,
    //     surrogate boundary, max-codepoint boundary, invalid leaders),
    //   - hand-picked valid 3- and 4-byte codepoints from real strings,
    //   - truncated prefixes of multi-byte codepoints,
    //   - long ASCII buffers (to trigger the wordwise fast path), and
    //   - the canonical "invalid" cases (lone continuation, surrogate,
    //     overlong, byte beyond U+10FFFF).
    //
    // A buggy implementation that returned a wrong `valid_up_to`, a
    // wrong `error_len`, or that disagreed with `from_utf8` on any of
    // these inputs would be caught by these properties.

    fn property_corpus() -> Vec<Vec<u8>> {
        let mut corpus: Vec<Vec<u8>> = Vec::new();

        // Every single byte.
        for b in 0u16..256 {
            corpus.push(vec![b as u8]);
        }

        // Every 2-byte sequence for boundary-relevant leading bytes.
        let leaders: &[u8] = &[
            0x00, 0x7F,                         // ASCII boundary
            0x80, 0xBF,                         // lone continuation range
            0xC0, 0xC1,                         // overlong 2-byte
            0xC2, 0xDF,                         // valid 2-byte boundary
            0xE0, 0xE1, 0xEC, 0xED, 0xEE, 0xEF, // 3-byte (incl. surrogate gap)
            0xF0, 0xF1, 0xF3, 0xF4,             // 4-byte
            0xF5, 0xFF,                         // beyond U+10FFFF
        ];
        for &first in leaders {
            for second in 0u16..256 {
                corpus.push(vec![first, second as u8]);
            }
        }

        // Real UTF-8 strings exercising 3- and 4-byte codepoints.
        let strings = [
            "",
            "ascii only",
            "Hello, world! © € 🌍 こんにちは 🎉 Привет αβγ",
            "𝛼+𝛽=γ — and a smiley 😀",
        ];
        for s in strings {
            corpus.push(s.as_bytes().to_vec());
        }

        // Truncated prefixes of multi-byte codepoints at the very end.
        let with_smiley = "Hi! 😀".as_bytes(); // 0x48 0x69 0x21 0x20 F0 9F 98 80
        for cut in 1..with_smiley.len() {
            corpus.push(with_smiley[..cut].to_vec());
        }

        // Long ASCII buffers — exercise the wordwise fast path on its own
        // and with bad / truncated tails.
        corpus.push(vec![b'x'; 257]);
        let mut long_with_bad = vec![b'x'; 128];
        long_with_bad.push(0xFF);
        corpus.push(long_with_bad);
        let mut long_with_truncation = vec![b'x'; 128];
        long_with_truncation.extend_from_slice(&[0xE2, 0x82]); // €, missing AC
        corpus.push(long_with_truncation);

        // Canonical invalid sequences.
        corpus.push(vec![0xED, 0xA0, 0x80]); // surrogate U+D800
        corpus.push(vec![0xC0, 0x80]);       // overlong NUL
        corpus.push(vec![0xF5, 0x80, 0x80, 0x80]); // beyond U+10FFFF

        corpus
    }

    /// Postcondition (master correctness oracle):
    /// `run_utf8_validation(v)` returns `Ok(())` iff `v` is valid UTF-8.
    /// `std::str::from_utf8` is taken as the definition of "valid UTF-8".
    #[test]
    fn prop_ok_iff_std_says_valid() {
        for v in property_corpus() {
            let ours = run_utf8_validation(&v).is_ok();
            let theirs = std::str::from_utf8(&v).is_ok();
            assert_eq!(ours, theirs, "validity mismatch on {:?}", v);
        }
    }

    /// Postcondition on `Err`:
    /// `valid_up_to` is a byte index inside the slice, and the prefix
    /// `v[..valid_up_to]` is itself valid UTF-8.  In other words, the
    /// validator never gives up "too early" — anything it claims to
    /// have validated really is valid.
    #[test]
    fn prop_valid_up_to_marks_valid_prefix() {
        for v in property_corpus() {
            if let Err(e) = run_utf8_validation(&v) {
                assert!(
                    e.valid_up_to() <= v.len(),
                    "valid_up_to {} > len {} for {:?}",
                    e.valid_up_to(),
                    v.len(),
                    v
                );
                assert!(
                    std::str::from_utf8(&v[..e.valid_up_to()]).is_ok(),
                    "prefix v[..{}] is not valid UTF-8 for {:?}",
                    e.valid_up_to(),
                    v
                );
            }
        }
    }

    /// Failure-condition shape, `Some` arm:
    /// when `error_len = Some(n)`, `n` is in 1..=3 and the n "bad" bytes
    /// starting at `valid_up_to` lie inside the slice.  (n can never be
    /// 0 or 4: a 4-byte codepoint is only rejected after at most 3
    /// already-read bytes, so the maximum reported `error_len` is 3.)
    #[test]
    fn prop_error_len_some_is_bounded_and_in_range() {
        for v in property_corpus() {
            if let Err(e) = run_utf8_validation(&v) {
                if let Some(n) = e.error_len() {
                    assert!(
                        (1..=3).contains(&n),
                        "error_len = Some({}) out of 1..=3 for {:?}",
                        n,
                        v
                    );
                    assert!(
                        e.valid_up_to() + n <= v.len(),
                        "bad-byte range [{}, {}) exceeds len {} for {:?}",
                        e.valid_up_to(),
                        e.valid_up_to() + n,
                        v.len(),
                        v
                    );
                }
            }
        }
    }

    /// Failure-condition shape, `None` arm:
    /// `error_len = None` means the validator stopped mid-codepoint
    /// because it ran out of bytes.  The leading byte at `valid_up_to`
    /// must therefore be a valid multi-byte start (width 2, 3 or 4)
    /// and strictly fewer bytes than that width remain in the slice.
    /// This distinguishes "truncation" (None) from "definitely bad"
    /// (Some(_)).
    #[test]
    fn prop_error_len_none_means_truncation() {
        fn codepoint_width(b: u8) -> usize {
            match b {
                0x00..=0x7F => 1,
                0xC2..=0xDF => 2,
                0xE0..=0xEF => 3,
                0xF0..=0xF4 => 4,
                _ => 0, // 0x80..=0xC1 and 0xF5..=0xFF are not valid leaders
            }
        }
        for v in property_corpus() {
            if let Err(e) = run_utf8_validation(&v) {
                if e.error_len().is_none() {
                    assert!(
                        e.valid_up_to() < v.len(),
                        "error_len = None but valid_up_to == len for {:?}",
                        v
                    );
                    let leader = v[e.valid_up_to()];
                    let w = codepoint_width(leader);
                    assert!(
                        w >= 2,
                        "error_len = None on non-multi-byte leader {:#x} in {:?}",
                        leader,
                        v
                    );
                    let remaining = v.len() - e.valid_up_to();
                    assert!(
                        remaining < w,
                        "error_len = None but {} bytes remain for width-{} leader in {:?}",
                        remaining,
                        w,
                        v
                    );
                }
            }
        }
    }

    /// Postcondition (positive specialization):
    /// every Rust `&str` — already guaranteed to be valid UTF-8 by the
    /// type system — is accepted.  This is logically a corollary of
    /// `prop_ok_iff_std_says_valid`, but it pins down the property in
    /// a form that does not mention `from_utf8`: useful as its own
    /// proof obligation downstream, since it can be stated purely in
    /// terms of `str::as_bytes`.
    #[test]
    fn prop_every_str_is_accepted() {
        let samples: &[&str] = &[
            "",
            "ascii",
            "café",
            "日本語",
            "🌍🌎🌏",
            "mixed: a© b€ c😀 d日 e𝛼 f-ascii",
        ];
        for s in samples {
            assert_eq!(
                run_utf8_validation(s.as_bytes()),
                Ok(()),
                "rejected valid &str {:?}",
                s
            );
        }
        // Long valid string to also cover the wordwise fast path.
        let long: String = "x".repeat(257);
        assert_eq!(run_utf8_validation(long.as_bytes()), Ok(()));
    }
}
