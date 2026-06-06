-- Companion obligations file for the `next_code_point_reverse_u8` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import next_code_point_reverse_u8

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Next_code_point_reverse_u8Obligations

open next_code_point_reverse_u8
open core_models.slice.iter (Iter)
open rust_primitives.hax (Tuple2)
open rust_primitives.sequence (Seq)

-- We keep the option-type fully qualified to avoid clashing with `_root_.Option`.
abbrev OptU32 := core_models.option.Option u32

/-! ## Conveniences

`Iter u8` wraps a `Seq u8 = {val : Array u8 // val.size < USize64.size}`.
We freely speak of an `Iter u8` "of byte array `bytes`" via the constructor
below. -/

/-- Build an `Iter u8` from a byte array whose length fits in `USize64`. -/
def iterOfBytes (bytes : Array u8) (h : bytes.size < USize64.size) : Iter u8 :=
  Iter.mk ⟨bytes, h⟩

/-- An `Iter u8` is "empty" when its underlying byte array is empty. This is
    the condition `bytes.next_back()` returns `None` on. -/
def IsEmpty (it : Iter u8) : Prop := it._0.val.size = 0

/-! ## Failure / totality contract

The function is documented as `unsafe` only because of the *iterator-shape*
assumption (`bytes` must produce a UTF-8-like byte sequence); within the
abstract `RustM` model the implementation never panics, overflows, or hits
the partial `unwrap_unchecked` branch — that branch is justified by the
safety precondition, not entered. This is the "no failure mode" half of the
contract. -/

/-- **Totality / no panic.** For every `Iter u8` whose underlying bytes
    encode valid UTF-8 (or the empty prefix thereof), the function returns
    a successful `RustM.ok` value — no `fail`, no `panic`, no spurious
    error. Stated existentially over the resulting iterator and option
    payload because the body of `next_code_point_reverse` is opaque to
    this stage. Matches the implicit "no failure modes" half of the
    contract that all six unit tests and the three property tests rely
    on. -/
theorem next_code_point_reverse_total (it : Iter u8) :
    ∃ (it' : Iter u8) (o : OptU32),
      next_code_point_reverse it = RustM.ok (Tuple2.mk it' o) := by
  sorry

/-! ## Empty-iterator contract -/

/-- **Empty iterator returns `None`.** When the iterator's backing byte
    array is empty, `next_code_point_reverse` returns the `None` option
    payload without modifying the iterator. Corresponds to the unit test
    `empty_iterator_returns_none` and the first call inside
    `prop_empty_iterator_stays_none`. -/
theorem next_code_point_reverse_empty (it : Iter u8) (h : IsEmpty it) :
    next_code_point_reverse it =
      RustM.ok (Tuple2.mk it core_models.option.Option.None) := by
  sorry

/-- **Empty iterator stays `None`.** Once the iterator is empty, every
    subsequent call also returns `None` with the iterator unchanged (so
    repeated polling is safe — no panic, no spurious `Some`). This is
    exactly what `prop_empty_iterator_stays_none` certifies across an
    arbitrary number of repeat calls. Stated equationally: the only `Iter`
    state that can be produced by a sequence of calls starting from
    `IsEmpty` is itself empty, and the corresponding option payload is
    `None`. -/
theorem next_code_point_reverse_empty_again
    (it : Iter u8) (h : IsEmpty it) :
    ∀ it', next_code_point_reverse it =
        RustM.ok (Tuple2.mk it' core_models.option.Option.None) →
      next_code_point_reverse it' =
        RustM.ok (Tuple2.mk it' core_models.option.Option.None) := by
  sorry

/-! ## Single-byte (ASCII) decoding contract -/

/-- **ASCII byte decodes to itself.** For any byte `b` with `b < 128` and
    any `Iter u8` whose underlying byte array is `#[b]` (a singleton
    containing exactly `b`), `next_code_point_reverse` returns the option
    payload `Some (b as u32)` and the resulting iterator is drained.
    Captures the unit test `ascii_byte_returns_single_codepoint` and the
    ASCII slice of `prop_single_codepoint_roundtrip`. Stated over an
    arbitrary `Iter u8` with the singleton-bytes side condition because
    constructing the `Iter` explicitly requires a `size < USize64.size`
    proof obligation that this stage doesn't need to dispatch. -/
theorem next_code_point_reverse_ascii_one
    (it : Iter u8) (b : u8) (hb : b.toNat < 128)
    (h_bytes : it._0.val = #[b]) :
    ∃ (it' : Iter u8),
      next_code_point_reverse it =
        RustM.ok (Tuple2.mk it'
          (core_models.option.Option.Some (UInt32.ofNat b.toNat))) ∧
      IsEmpty it' := by
  sorry

/-! ## Multi-byte (UTF-8) decoding contract

The function decodes the *last* code point of a UTF-8-like byte iterator.
We characterise this through Lean's standard UTF-8 encoder `String.toUTF8`.
For each `Char`, encoding it (via a single-character string) yields a byte
array of length 1, 2, 3, or 4 — well below `USize64.size = 2^64`. -/

/-- **Single-codepoint round-trip.** For every `Char` (i.e. every valid
    Unicode scalar value in `0x00..=0x10FFFF` excluding the surrogate
    block) and every `Iter u8` whose underlying byte array equals the
    UTF-8 encoding of `c`, `next_code_point_reverse` returns the option
    payload `Some c.val` and the resulting iterator is drained. Captures
    `prop_single_codepoint_roundtrip` and subsumes the unit tests
    `two_byte_codepoint_copyright`, `three_byte_codepoint_bmp`, and
    `four_byte_codepoint_supplementary`. Stated over an arbitrary `Iter`
    with a UTF-8 side condition because constructing the iterator
    explicitly requires a `size < USize64.size` discharge that's not the
    contract's job. -/
theorem next_code_point_reverse_single_char_roundtrip
    (c : Char) (it : Iter u8)
    (h_bytes : it._0.val = (String.singleton c).toUTF8.toList.toArray) :
    ∃ (it' : Iter u8),
      next_code_point_reverse it =
        RustM.ok (Tuple2.mk it'
          (core_models.option.Option.Some c.val)) ∧
      IsEmpty it' := by
  sorry

/-! ## Multi-codepoint (string) contract

Sequence-of-codepoints semantics: repeatedly applying
`next_code_point_reverse` to the bytes of any valid UTF-8 string yields
the same sequence of `u32` values as `s.toList.reverse.map Char.val`,
and the iterator is fully drained at the end. This is what
`prop_string_matches_chars_rev` certifies — in particular, it pins down
*how many* bytes the function consumes per call. -/

/-- Iterated application of `next_code_point_reverse` `n` times, gathering
    the produced option payloads (in call order) and returning the final
    iterator state. If any call fails, the failure short-circuits the
    iteration and the gathered list is empty. -/
private def iterateBack (n : Nat) (it : Iter u8) :
    Iter u8 × List OptU32 :=
  match n with
  | 0 => (it, [])
  | k + 1 =>
    match next_code_point_reverse it with
    | RustM.ok (Tuple2.mk it' o) =>
      let (it'', os) := iterateBack k it'
      (it'', o :: os)
    | _ => (it, [])

/-- **String iteration matches `chars().rev()`.** For any valid UTF-8
    string `s` and any `Iter u8` whose underlying byte array equals
    `s.toUTF8`, calling `next_code_point_reverse` `n + 1` times on that
    iterator (where `n` is the number of characters in `s`) yields the
    codepoints of `s` in reverse — each wrapped in `Some` — followed by
    a final `None`, and the iterator is fully drained. Captures
    `prop_string_matches_chars_rev`. The off-by-one (`n + 1`) accounts
    for the final terminating `None` poll. -/
theorem next_code_point_reverse_string_iteration
    (s : String) (it : Iter u8)
    (h_bytes : it._0.val = s.toUTF8.toList.toArray) :
    let (it', os) := iterateBack (s.toList.length + 1) it
    IsEmpty it' ∧
    os = (s.toList.reverse.map
            (fun c => core_models.option.Option.Some c.val))
          ++ [core_models.option.Option.None] := by
  sorry

end Next_code_point_reverse_u8Obligations
