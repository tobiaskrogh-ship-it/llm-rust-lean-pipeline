-- Companion obligations file for the `run_utf8_validation_u8` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import run_utf8_validation_u8

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Run_utf8_validation_u8Obligations

open run_utf8_validation_u8

/-! ## UTF-8 validity specification

We characterise valid UTF-8 by a `Bool`-valued recursive predicate that
walks the byte array one codepoint at a time. The grammar follows
RFC 3629 (and matches the Rust function under verification):

  * ASCII bytes `0x00..=0x7F` are width-1 codepoints;
  * `0xC2..=0xDF` lead width-2 codepoints, followed by one continuation;
  * `0xE0..=0xEF` lead width-3 codepoints, with the surrogate range
    `U+D800..U+DFFF` (encoded `0xED 0xA0..=0xBF ...`) excluded;
  * `0xF0..=0xF4` lead width-4 codepoints, capped at U+10FFFF;
  * `0x80..=0xC1` and `0xF5..=0xFF` are not valid leaders. -/

/-- Width of the UTF-8 codepoint led by `b`: 1 for ASCII, 2/3/4 for valid
    multi-byte leaders, 0 otherwise. Mirrors the Rust `utf8_char_width`. -/
def leadWidth (b : u8) : Nat :=
  if b.toNat < 0x80 then 1
  else if b.toNat < 0xC2 then 0
  else if b.toNat < 0xE0 then 2
  else if b.toNat < 0xF0 then 3
  else if b.toNat < 0xF5 then 4
  else 0

/-- UTF-8 continuation byte (`0x80..=0xBF`). -/
def IsContByte (b : u8) : Prop := 0x80 ≤ b.toNat ∧ b.toNat ≤ 0xBF

instance (b : u8) : Decidable (IsContByte b) := by
  unfold IsContByte; infer_instance

/-- The second byte of a multi-byte codepoint led by `first` lies in the
    range required by RFC 3629 (excluding the UTF-16 surrogate range and
    capping at U+10FFFF). Used in the width-3 and width-4 branches. -/
def SecondByteOk (first b2 : u8) : Prop :=
  let f := first.toNat
  let s := b2.toNat
  (f = 0xE0 ∧ 0xA0 ≤ s ∧ s ≤ 0xBF) ∨
  (0xE1 ≤ f ∧ f ≤ 0xEC ∧ 0x80 ≤ s ∧ s ≤ 0xBF) ∨
  (f = 0xED ∧ 0x80 ≤ s ∧ s ≤ 0x9F) ∨
  (0xEE ≤ f ∧ f ≤ 0xEF ∧ 0x80 ≤ s ∧ s ≤ 0xBF) ∨
  (f = 0xF0 ∧ 0x90 ≤ s ∧ s ≤ 0xBF) ∨
  (0xF1 ≤ f ∧ f ≤ 0xF3 ∧ 0x80 ≤ s ∧ s ≤ 0xBF) ∨
  (f = 0xF4 ∧ 0x80 ≤ s ∧ s ≤ 0x8F)

instance (b1 b2 : u8) : Decidable (SecondByteOk b1 b2) := by
  unfold SecondByteOk; infer_instance

/-- Recursive validator over the byte array. Returns `true` once the
    suffix is empty; otherwise consumes one codepoint of width 1/2/3/4
    and recurses, or returns `false` if the bytes don't form a complete
    valid codepoint. Termination measure: `bs.size - k`. -/
def isValidUtf8From (bs : Array u8) (k : Nat) : Bool :=
  if hk : bs.size ≤ k then true
  else
    have hk' : k < bs.size := Nat.lt_of_not_le hk
    let b1 := bs[k]'hk'
    let w := leadWidth b1
    if w = 1 then isValidUtf8From bs (k + 1)
    else if w = 2 then
      if hk1 : k + 1 < bs.size then
        decide (IsContByte (bs[k+1]'hk1)) && isValidUtf8From bs (k + 2)
      else false
    else if w = 3 then
      if hk1 : k + 1 < bs.size then
        if decide (SecondByteOk b1 (bs[k+1]'hk1)) then
          if hk2 : k + 2 < bs.size then
            decide (IsContByte (bs[k+2]'hk2)) && isValidUtf8From bs (k + 3)
          else false
        else false
      else false
    else if w = 4 then
      if hk1 : k + 1 < bs.size then
        if decide (SecondByteOk b1 (bs[k+1]'hk1)) then
          if hk2 : k + 2 < bs.size then
            if decide (IsContByte (bs[k+2]'hk2)) then
              if hk3 : k + 3 < bs.size then
                decide (IsContByte (bs[k+3]'hk3)) && isValidUtf8From bs (k + 4)
              else false
            else false
          else false
        else false
      else false
    else false
termination_by bs.size - k
decreasing_by all_goals (simp_wf; omega)

/-- The byte array `bs` is a valid UTF-8 sequence. -/
def IsValidUtf8 (bs : Array u8) : Prop := isValidUtf8From bs 0 = true

/-! ## Contract clauses

Each Rust property test maps to one theorem below. Proofs are deferred
to the proof stage and stubbed with `sorry`. -/

/-- **`prop_ok_iff_std_says_valid`** — master correctness oracle.
    `run_utf8_validation v` returns `Ok(())` iff the underlying bytes
    `v.val` form a valid UTF-8 sequence. -/
theorem run_utf8_validation_ok_iff_isValidUtf8 (v : RustSlice u8) :
    run_utf8_validation v =
        RustM.ok (core_models.result.Result.Ok rust_primitives.hax.Tuple0.mk) ↔
      IsValidUtf8 v.val := by
  sorry

/-- **`prop_valid_up_to_marks_valid_prefix`** — on `Err`, `valid_up_to`
    is in-bounds and the prefix `v[..valid_up_to]` is itself valid
    UTF-8. The validator never gives up "too early". -/
theorem run_utf8_validation_err_prefix_valid
    (v : RustSlice u8) (err : Utf8Error)
    (h : run_utf8_validation v =
        RustM.ok (core_models.result.Result.Err err)) :
    err.valid_up_to.toNat ≤ v.val.size ∧
      IsValidUtf8 (v.val.take err.valid_up_to.toNat) := by
  sorry

/-- **`prop_error_len_some_is_bounded_and_in_range`** — when an `Err`
    carries `error_len = Some n`, `n ∈ {1, 2, 3}` and the `n` bad bytes
    starting at `valid_up_to` lie inside the slice. (`n = 0` and
    `n ≥ 4` never occur: a 4-byte codepoint is rejected after at most
    3 already-read bytes.) -/
theorem run_utf8_validation_err_error_len_some_in_range
    (v : RustSlice u8) (err : Utf8Error) (n : u8)
    (h : run_utf8_validation v =
        RustM.ok (core_models.result.Result.Err err))
    (hn : err.error_len = core_models.option.Option.Some n) :
    1 ≤ n.toNat ∧ n.toNat ≤ 3 ∧
      err.valid_up_to.toNat + n.toNat ≤ v.val.size := by
  sorry

/-- **`prop_error_len_none_means_truncation`** — when an `Err` carries
    `error_len = None`, the validator stopped mid-codepoint because the
    slice ran out of bytes. The byte at `valid_up_to` is a multi-byte
    leader (width 2/3/4) and strictly fewer bytes than that width
    remain in the slice. This distinguishes "truncation" (`None`) from
    "definitely bad" (`Some _`). -/
theorem run_utf8_validation_err_error_len_none_truncation
    (v : RustSlice u8) (err : Utf8Error)
    (h : run_utf8_validation v =
        RustM.ok (core_models.result.Result.Err err))
    (hn : err.error_len = core_models.option.Option.None) :
    ∃ (hb : err.valid_up_to.toNat < v.val.size),
      2 ≤ leadWidth (v.val[err.valid_up_to.toNat]'hb) ∧
        v.val.size - err.valid_up_to.toNat <
          leadWidth (v.val[err.valid_up_to.toNat]'hb) := by
  sorry

end Run_utf8_validation_u8Obligations
