//! Extracted from `core::str::validations::run_utf8_validation`.
//!
//! Walks through `v` checking that it's a valid UTF-8 sequence, returning
//! `Ok(())` in that case, or, if it is invalid, `Err(err)`.
//!
//! Hax-compatibility rewrite notes (from the original `core` implementation):
//!   * The wordwise ASCII fast path used `v.as_ptr().align_offset(...)` plus
//!     `unsafe { *(ptr.add(index) as *const usize) }` reads. Hax's
//!     `reject_RawOrMutPointer` phase rejects raw pointers outright, and
//!     `align_offset`, `from_ne_bytes`, `is_multiple_of`, `wrapping_sub`,
//!     `usize::MAX`, `size_of::<usize>()` are all unmodeled in the Hax Lean
//!     prelude. The fast path was a performance optimization; removing it
//!     preserves correctness (byte-by-byte iteration matches the stdlib
//!     semantics). See `rewrite_patterns/unsafe_transmute_to_bits.rs` and
//!     `rewrite_patterns/primitive_int_assoc_const.rs`.
//!   * The original `while index < len { ... }` loop used local `err!` /
//!     `next!` macros containing `return Err(...)`. Hax extracts `return`
//!     inside a `while` to `rust_primitives.hax.while_loop_return`, which
//!     is undefined in the prelude (see
//!     `rewrite_patterns/while_loop_early_return.rs`). Rather than thread a
//!     `found` flag, the whole loop is converted to a tail-recursive helper
//!     `validate_at` per the recursion-preference rule
//!     (`rewrite_patterns/while_loop_to_recursion.rs` and
//!     `rewrite_patterns/for_loop_over_slice_to_recursion.rs`). Decreasing
//!     measure is `v.len() - index`. Test corpus depth is < 1000 bytes,
//!     well within the ~10^5 safe rule of thumb.
//!   * The tuple-pattern match `match (first, next!()) { (0xE0, 0xA0..=0xBF)
//!     | (0xE1..=0xEC, 0x80..=0xBF) | ... }` extracted as `let _ := sorry;`,
//!     so it is replaced by a sequential `if`/`else if` chain on `first`
//!     with explicit comparison ranges on the second byte.
//!   * `(next!() as i8) >= -64` (the "is this NOT a UTF-8 continuation byte"
//!     check) is replaced by the byte-pattern-equivalent `(b & 0xC0) != 0x80`.
//!     Continuation bytes are precisely `0x80..=0xBF`, whose top two bits
//!     are `10`; the new form avoids the `u8 -> i8` reinterpretation cast
//!     and stays in unsigned arithmetic.
//!
//! `Utf8Error` is reimplemented locally with the same `(valid_up_to,
//! error_len)` shape, and the `valid_up_to()` / `error_len()` accessors are
//! preserved unchanged.

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
//
// `repeat_u8` / `NONASCII_MASK` / `contains_nonascii` from the stdlib source
// powered the unsafe wordwise ASCII fast path. With that path removed
// (raw-pointer rejection by Hax), they have no callers and have been
// dropped.

// https://tools.ietf.org/html/rfc3629
//
// The original stdlib implementation uses a 256-byte lookup table
// (`UTF8_CHAR_WIDTH`). Hax extracts that table as a 256-element
// `#v[...]` vector literal, which exceeds Lean's elaboration recursion
// depth (lake build: `maximum recursion depth has been reached`).
// The table has only 4 distinct width values across 6 contiguous byte
// ranges, so the same function is expressible as a branch chain with
// identical semantics on every u8 input.
#[inline]
const fn utf8_char_width(b: u8) -> usize {
    if b < 0x80 {
        // 0x00..=0x7F: ASCII, width 1.
        1
    } else if b < 0xC2 {
        // 0x80..=0xC1: continuation bytes (0x80..=0xBF) and overlong
        // 2-byte leaders (0xC0..=0xC1) — both invalid as leaders.
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

// ---- The main function -----------------------------------------------------
//
// Tail-recursive validator. Decreasing measure: `v.len() - index` (each
// recursive call advances `index` by at least 1). Early-error branches
// short-circuit without recursing. Per the recursion-preference rule, this
// shape is preferred over a `while` loop for proof tractability — the
// extracted Lean is a `partial_fixpoint` provable via `Nat.strongRecOn` on
// `(v.len() - index).toNat`.

fn validate_at(v: &[u8], index: usize) -> Result<(), Utf8Error> {
    let len = v.len();
    if index >= len {
        Ok(())
    } else {
        let old_offset = index;
        let first = v[index];
        if first < 128 {
            // ASCII byte — advance one.
            validate_at(v, index + 1)
        } else {
            let w = utf8_char_width(first);
            // 2-byte encoding is for codepoints  \u{0080} to  \u{07ff}
            //        first  C2 80        last DF BF
            // 3-byte encoding is for codepoints  \u{0800} to  \u{ffff}
            //        first  E0 A0 80     last EF BF BF
            //   excluding surrogates codepoints  \u{d800} to  \u{dfff}
            //               ED A0 80 to       ED BF BF
            // 4-byte encoding is for codepoints \u{10000} to \u{10ffff}
            //        first  F0 90 80 80  last F4 8F BF BF
            if w == 2 {
                let i1 = index + 1;
                if i1 >= len {
                    Err(Utf8Error { valid_up_to: old_offset, error_len: None })
                } else if (v[i1] & 0xC0) != 0x80 {
                    // Continuation bytes are 0x80..=0xBF; equivalently
                    // the top two bits are `10`. `(b & 0xC0) != 0x80`
                    // mirrors the original `(b as i8) >= -64` check
                    // without the signed-cast reinterpretation.
                    Err(Utf8Error { valid_up_to: old_offset, error_len: Some(1) })
                } else {
                    validate_at(v, i1 + 1)
                }
            } else if w == 3 {
                let i1 = index + 1;
                if i1 >= len {
                    Err(Utf8Error { valid_up_to: old_offset, error_len: None })
                } else {
                    let b2 = v[i1];
                    // Sequential leader-range chain replacing the
                    // tuple-pattern match `(0xE0, 0xA0..=0xBF) | ...`
                    // that extracted as `let _ := sorry;`.
                    let ok2 = if first == 0xE0 {
                        b2 >= 0xA0 && b2 <= 0xBF
                    } else if first >= 0xE1 && first <= 0xEC {
                        b2 >= 0x80 && b2 <= 0xBF
                    } else if first == 0xED {
                        b2 >= 0x80 && b2 <= 0x9F
                    } else if first >= 0xEE && first <= 0xEF {
                        b2 >= 0x80 && b2 <= 0xBF
                    } else {
                        false
                    };
                    if !ok2 {
                        Err(Utf8Error { valid_up_to: old_offset, error_len: Some(1) })
                    } else {
                        let i2 = i1 + 1;
                        if i2 >= len {
                            Err(Utf8Error { valid_up_to: old_offset, error_len: None })
                        } else if (v[i2] & 0xC0) != 0x80 {
                            Err(Utf8Error { valid_up_to: old_offset, error_len: Some(2) })
                        } else {
                            validate_at(v, i2 + 1)
                        }
                    }
                }
            } else if w == 4 {
                let i1 = index + 1;
                if i1 >= len {
                    Err(Utf8Error { valid_up_to: old_offset, error_len: None })
                } else {
                    let b2 = v[i1];
                    let ok2 = if first == 0xF0 {
                        b2 >= 0x90 && b2 <= 0xBF
                    } else if first >= 0xF1 && first <= 0xF3 {
                        b2 >= 0x80 && b2 <= 0xBF
                    } else if first == 0xF4 {
                        b2 >= 0x80 && b2 <= 0x8F
                    } else {
                        false
                    };
                    if !ok2 {
                        Err(Utf8Error { valid_up_to: old_offset, error_len: Some(1) })
                    } else {
                        let i2 = i1 + 1;
                        if i2 >= len {
                            Err(Utf8Error { valid_up_to: old_offset, error_len: None })
                        } else if (v[i2] & 0xC0) != 0x80 {
                            Err(Utf8Error { valid_up_to: old_offset, error_len: Some(2) })
                        } else {
                            let i3 = i2 + 1;
                            if i3 >= len {
                                Err(Utf8Error { valid_up_to: old_offset, error_len: None })
                            } else if (v[i3] & 0xC0) != 0x80 {
                                Err(Utf8Error { valid_up_to: old_offset, error_len: Some(3) })
                            } else {
                                validate_at(v, i3 + 1)
                            }
                        }
                    }
                }
            } else {
                // w == 0 — invalid leading byte (0x80..=0xC1, 0xF5..=0xFF).
                // (w == 1 cannot occur here because we're in the `first >= 128`
                // branch, and the table has w == 1 only for 0x00..=0x7F.)
                Err(Utf8Error { valid_up_to: old_offset, error_len: Some(1) })
            }
        }
    }
}

#[inline]
pub fn run_utf8_validation(v: &[u8]) -> Result<(), Utf8Error> {
    validate_at(v, 0)
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
