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

/-! ## Helpers (transferred from `contains_u64`/`below_zero` reference patterns) -/

/-- `RustM.ok x >>= f = f x`. The library's `pure_bind` simp lemma only
    matches literal `Pure.pure`; this rewrite handles the `RustM.ok` form
    produced after reducing definitions. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

private theorem u8_lt_iff (a b : u8) : (a < b) ↔ (a.toNat < b.toNat) := by
  exact UInt8.lt_iff_toNat_lt.symm |>.symm |>.symm |>.symm
private theorem u8_le_iff (a b : u8) : (a ≤ b) ↔ (a.toNat ≤ b.toNat) := by
  exact UInt8.le_iff_toNat_le.symm |>.symm |>.symm |>.symm

/-- Convenient decidable equality on `u8` lifted to `toNat`. -/
private theorem u8_eq_iff_toNat_eq (a b : u8) : a = b ↔ a.toNat = b.toNat :=
  UInt8.toNat_inj.symm

/-! ## `validate_at` step lemmas — one per branch of the body.

Each lemma assumes the branch's discriminating condition and rewrites the
`validate_at` call to the resulting expression (either a recursive call or
a concrete `Ok` / `Err` value). The lemmas share the same `unfold + simp only`
recipe as the `contains_u64` reference and act as the building blocks for the
strong-induction master lemma. -/

/-- Out-of-bounds step: `index.toNat ≥ v.val.size` ⇒ returns `Ok ()`. -/
private theorem validate_at_oob (v : RustSlice u8) (index : usize)
    (hi : v.val.size ≤ index.toNat) :
    validate_at v index =
      RustM.ok (core_models.result.Result.Ok rust_primitives.hax.Tuple0.mk) := by
  conv => lhs; unfold validate_at
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat v.val.size ≤ index) = true := by
    rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat]; exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, h_cond, ↓reduceIte]
  rfl

/-- Reduces `(index +? 1)` to `RustM.ok (index + 1)` under no-overflow. -/
private theorem usize_add_one_ok (i : usize) (h : i.toNat + 1 < 2^64) :
    (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
  show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = _
  show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure (i + 1)) = _
  have h_no_bv : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hi := (USize64.uaddOverflow_iff i 1).mp hbo
      rw [usize_one_toNat] at hi; omega
  rw [h_no_bv]; rfl

/-- The Rust indexer `v[i]_?` reduces to `RustM.ok (v.val[i.toNat])` under bounds. -/
private theorem getElem_ok (v : RustSlice u8) (i : usize)
    (hi : i.toNat < v.val.size) :
    (v[i]_? : RustM u8) = RustM.ok (v.val[i.toNat]'hi) := by
  show (if h : i.toNat < v.val.size then pure (v.val[i]) else .fail .arrayOutOfBounds)
      = RustM.ok (v.val[i.toNat]'hi)
  rw [dif_pos hi]; rfl

/-! ## Step lemmas for each branch of `validate_at`.

These give the unfolding equation for `validate_at v index` for one specific
branch — the master lemma below dispatches to the right one based on the
byte values it observes. -/

/-- ASCII step: `index.toNat < v.val.size`, `first.toNat < 128` ⇒ recurse with `index + 1`. -/
private theorem validate_at_ascii (v : RustSlice u8) (index : usize)
    (hi : index.toNat < v.val.size)
    (h_ascii : (v.val[index.toNat]'hi).toNat < 128) :
    validate_at v index = validate_at v (index + 1) := by
  conv => lhs; unfold validate_at
  have h_size_lt : v.val.size < 2^64 := v.size_lt_usizeSize
  have h_no_overflow : index.toNat + 1 < 2^64 := by omega
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat v.val.size ≤ index) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]; omega
  have h_idx := getElem_ok v index hi
  have h_first_lt : (v.val[index.toNat]'hi) < (128 : u8) := by
    rw [UInt8.lt_iff_toNat_lt]; exact h_ascii
  have h_lt : decide ((v.val[index.toNat]'hi) < (128 : u8)) = true :=
    decide_eq_true h_first_lt
  have h_add := usize_add_one_ok index h_no_overflow
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx, rust_primitives.cmp.lt, h_lt, h_add]

/-! ### Width-table helpers — `utf8_char_width first = RustM.ok (concrete width)`. -/

private theorem u8_lit_toNat (n : Nat) (h : n < 256) :
    ((OfNat.ofNat n : u8)).toNat = n := by
  show UInt8.toNat (OfNat.ofNat n) = n
  rw [UInt8.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Concrete `UInt8.toNat` values for the threshold constants. -/
private theorem u8_128_toNat : ((128 : u8)).toNat = 128 := u8_lit_toNat 128 (by decide)
private theorem u8_194_toNat : ((194 : u8)).toNat = 194 := u8_lit_toNat 194 (by decide)
private theorem u8_224_toNat : ((224 : u8)).toNat = 224 := u8_lit_toNat 224 (by decide)
private theorem u8_240_toNat : ((240 : u8)).toNat = 240 := u8_lit_toNat 240 (by decide)
private theorem u8_245_toNat : ((245 : u8)).toNat = 245 := u8_lit_toNat 245 (by decide)
private theorem u8_192_toNat : ((192 : u8)).toNat = 192 := u8_lit_toNat 192 (by decide)
private theorem u8_191_toNat : ((191 : u8)).toNat = 191 := u8_lit_toNat 191 (by decide)
private theorem u8_160_toNat : ((160 : u8)).toNat = 160 := u8_lit_toNat 160 (by decide)
private theorem u8_159_toNat : ((159 : u8)).toNat = 159 := u8_lit_toNat 159 (by decide)
private theorem u8_144_toNat : ((144 : u8)).toNat = 144 := u8_lit_toNat 144 (by decide)
private theorem u8_143_toNat : ((143 : u8)).toNat = 143 := u8_lit_toNat 143 (by decide)
private theorem u8_237_toNat : ((237 : u8)).toNat = 237 := u8_lit_toNat 237 (by decide)
private theorem u8_238_toNat : ((238 : u8)).toNat = 238 := u8_lit_toNat 238 (by decide)
private theorem u8_239_toNat : ((239 : u8)).toNat = 239 := u8_lit_toNat 239 (by decide)
private theorem u8_241_toNat : ((241 : u8)).toNat = 241 := u8_lit_toNat 241 (by decide)
private theorem u8_243_toNat : ((243 : u8)).toNat = 243 := u8_lit_toNat 243 (by decide)
private theorem u8_244_toNat : ((244 : u8)).toNat = 244 := u8_lit_toNat 244 (by decide)
private theorem u8_236_toNat : ((236 : u8)).toNat = 236 := u8_lit_toNat 236 (by decide)
private theorem u8_225_toNat : ((225 : u8)).toNat = 225 := u8_lit_toNat 225 (by decide)
private theorem u8_E0_toNat : ((0xE0 : u8)).toNat = 0xE0 := u8_lit_toNat 0xE0 (by decide)
private theorem u8_F0_toNat : ((0xF0 : u8)).toNat = 0xF0 := u8_lit_toNat 0xF0 (by decide)

private theorem utf8_char_width_w0_small (b : u8) (h1 : 128 ≤ b.toNat) (h2 : b.toNat < 194) :
    run_utf8_validation_u8.utf8_char_width b = RustM.ok (0 : usize) := by
  unfold run_utf8_validation_u8.utf8_char_width
  have h_lt1 : decide (b < (128 : u8)) = false := by
    rw [decide_eq_false_iff_not, UInt8.lt_iff_toNat_lt, u8_128_toNat]; omega
  have h_lt2 : decide (b < (194 : u8)) = true := by
    rw [decide_eq_true_iff, UInt8.lt_iff_toNat_lt, u8_194_toNat]; omega
  simp only [rust_primitives.cmp.lt, pure_bind, h_lt1, h_lt2, Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem utf8_char_width_w2 (b : u8) (h1 : 194 ≤ b.toNat) (h2 : b.toNat < 224) :
    run_utf8_validation_u8.utf8_char_width b = RustM.ok (2 : usize) := by
  unfold run_utf8_validation_u8.utf8_char_width
  have h_lt1 : decide (b < (128 : u8)) = false := by
    rw [decide_eq_false_iff_not, UInt8.lt_iff_toNat_lt, u8_128_toNat]; omega
  have h_lt2 : decide (b < (194 : u8)) = false := by
    rw [decide_eq_false_iff_not, UInt8.lt_iff_toNat_lt, u8_194_toNat]; omega
  have h_lt3 : decide (b < (224 : u8)) = true := by
    rw [decide_eq_true_iff, UInt8.lt_iff_toNat_lt, u8_224_toNat]; omega
  simp only [rust_primitives.cmp.lt, pure_bind, h_lt1, h_lt2, h_lt3,
             Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem utf8_char_width_w3 (b : u8) (h1 : 224 ≤ b.toNat) (h2 : b.toNat < 240) :
    run_utf8_validation_u8.utf8_char_width b = RustM.ok (3 : usize) := by
  unfold run_utf8_validation_u8.utf8_char_width
  have h_lt1 : decide (b < (128 : u8)) = false := by
    rw [decide_eq_false_iff_not, UInt8.lt_iff_toNat_lt, u8_128_toNat]; omega
  have h_lt2 : decide (b < (194 : u8)) = false := by
    rw [decide_eq_false_iff_not, UInt8.lt_iff_toNat_lt, u8_194_toNat]; omega
  have h_lt3 : decide (b < (224 : u8)) = false := by
    rw [decide_eq_false_iff_not, UInt8.lt_iff_toNat_lt, u8_224_toNat]; omega
  have h_lt4 : decide (b < (240 : u8)) = true := by
    rw [decide_eq_true_iff, UInt8.lt_iff_toNat_lt, u8_240_toNat]; omega
  simp only [rust_primitives.cmp.lt, pure_bind, h_lt1, h_lt2, h_lt3, h_lt4,
             Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem utf8_char_width_w4 (b : u8) (h1 : 240 ≤ b.toNat) (h2 : b.toNat < 245) :
    run_utf8_validation_u8.utf8_char_width b = RustM.ok (4 : usize) := by
  unfold run_utf8_validation_u8.utf8_char_width
  have h_lt1 : decide (b < (128 : u8)) = false := by
    rw [decide_eq_false_iff_not, UInt8.lt_iff_toNat_lt, u8_128_toNat]; omega
  have h_lt2 : decide (b < (194 : u8)) = false := by
    rw [decide_eq_false_iff_not, UInt8.lt_iff_toNat_lt, u8_194_toNat]; omega
  have h_lt3 : decide (b < (224 : u8)) = false := by
    rw [decide_eq_false_iff_not, UInt8.lt_iff_toNat_lt, u8_224_toNat]; omega
  have h_lt4 : decide (b < (240 : u8)) = false := by
    rw [decide_eq_false_iff_not, UInt8.lt_iff_toNat_lt, u8_240_toNat]; omega
  have h_lt5 : decide (b < (245 : u8)) = true := by
    rw [decide_eq_true_iff, UInt8.lt_iff_toNat_lt, u8_245_toNat]; omega
  simp only [rust_primitives.cmp.lt, pure_bind, h_lt1, h_lt2, h_lt3, h_lt4, h_lt5,
             Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem utf8_char_width_w0_large (b : u8) (h : 245 ≤ b.toNat) :
    run_utf8_validation_u8.utf8_char_width b = RustM.ok (0 : usize) := by
  unfold run_utf8_validation_u8.utf8_char_width
  have h_lt1 : decide (b < (128 : u8)) = false := by
    rw [decide_eq_false_iff_not, UInt8.lt_iff_toNat_lt, u8_128_toNat]; omega
  have h_lt2 : decide (b < (194 : u8)) = false := by
    rw [decide_eq_false_iff_not, UInt8.lt_iff_toNat_lt, u8_194_toNat]; omega
  have h_lt3 : decide (b < (224 : u8)) = false := by
    rw [decide_eq_false_iff_not, UInt8.lt_iff_toNat_lt, u8_224_toNat]; omega
  have h_lt4 : decide (b < (240 : u8)) = false := by
    rw [decide_eq_false_iff_not, UInt8.lt_iff_toNat_lt, u8_240_toNat]; omega
  have h_lt5 : decide (b < (245 : u8)) = false := by
    rw [decide_eq_false_iff_not, UInt8.lt_iff_toNat_lt, u8_245_toNat]; omega
  simp only [rust_primitives.cmp.lt, pure_bind, h_lt1, h_lt2, h_lt3, h_lt4, h_lt5,
             Bool.false_eq_true, ↓reduceIte]
  rfl

/-! ### Common scaffolding for the `index < v.val.size, first ≥ 128` branches.

`validate_at_unfold_non_ascii` rewrites `validate_at v index` to its body
under the assumption that we're past the OOB and ASCII guards. The body
still contains the `utf8_char_width` chain; subsequent lemmas specialise. -/

private theorem validate_at_non_ascii_unfold (v : RustSlice u8) (index : usize)
    (hi : index.toNat < v.val.size)
    (h_ge : 128 ≤ (v.val[index.toNat]'hi).toNat) :
    run_utf8_validation_u8.validate_at v index = (do
      let w : usize ← run_utf8_validation_u8.utf8_char_width (v.val[index.toNat]'hi)
      if (← (w ==? (2 : usize))) then do
        let i1 : usize ← (index +? (1 : usize))
        if (← (i1 >=? USize64.ofNat v.val.size)) then do
          (pure (core_models.result.Result.Err
            (run_utf8_validation_u8.Utf8Error.mk
              (valid_up_to := index)
              (error_len := core_models.option.Option.None))))
        else do
          if (← ((← ((← v[i1]_?) &&&? (192 : u8))) !=? (128 : u8))) then do
            (pure (core_models.result.Result.Err
              (run_utf8_validation_u8.Utf8Error.mk
                (valid_up_to := index)
                (error_len := (core_models.option.Option.Some (1 : u8))))))
          else do
            (run_utf8_validation_u8.validate_at v (← (i1 +? (1 : usize))))
      else do
        if (← (w ==? (3 : usize))) then do
          let i1 : usize ← (index +? (1 : usize))
          if (← (i1 >=? USize64.ofNat v.val.size)) then do
            (pure (core_models.result.Result.Err
              (run_utf8_validation_u8.Utf8Error.mk
                (valid_up_to := index)
                (error_len := core_models.option.Option.None))))
          else do
            let b2 : u8 ← v[i1]_?
            let ok2 : Bool ←
              if (← ((v.val[index.toNat]'hi) ==? (224 : u8))) then do
                ((← (b2 >=? (160 : u8))) &&? (← (b2 <=? (191 : u8))))
              else do
                if
                (← ((← ((v.val[index.toNat]'hi) >=? (225 : u8))) &&?
                    (← ((v.val[index.toNat]'hi) <=? (236 : u8))))) then do
                  ((← (b2 >=? (128 : u8))) &&? (← (b2 <=? (191 : u8))))
                else do
                  if (← ((v.val[index.toNat]'hi) ==? (237 : u8))) then do
                    ((← (b2 >=? (128 : u8))) &&? (← (b2 <=? (159 : u8))))
                  else do
                    if
                    (← ((← ((v.val[index.toNat]'hi) >=? (238 : u8)))
                      &&? (← ((v.val[index.toNat]'hi) <=? (239 : u8))))) then do
                      ((← (b2 >=? (128 : u8))) &&? (← (b2 <=? (191 : u8))))
                    else do
                      (pure false)
            if (← (!? ok2)) then do
              (pure (core_models.result.Result.Err
                (run_utf8_validation_u8.Utf8Error.mk
                  (valid_up_to := index)
                  (error_len := (core_models.option.Option.Some (1 : u8))))))
            else do
              let i2 : usize ← (i1 +? (1 : usize))
              if (← (i2 >=? USize64.ofNat v.val.size)) then do
                (pure (core_models.result.Result.Err
                  (run_utf8_validation_u8.Utf8Error.mk
                    (valid_up_to := index)
                    (error_len := core_models.option.Option.None))))
              else do
                if
                (← ((← ((← v[i2]_?) &&&? (192 : u8))) !=? (128 : u8))) then do
                  (pure (core_models.result.Result.Err
                    (run_utf8_validation_u8.Utf8Error.mk
                      (valid_up_to := index)
                      (error_len := (core_models.option.Option.Some
                        (2 : u8))))))
                else do
                  (run_utf8_validation_u8.validate_at v (← (i2 +? (1 : usize))))
        else do
          if (← (w ==? (4 : usize))) then do
            let i1 : usize ← (index +? (1 : usize))
            if (← (i1 >=? USize64.ofNat v.val.size)) then do
              (pure (core_models.result.Result.Err
                (run_utf8_validation_u8.Utf8Error.mk
                  (valid_up_to := index)
                  (error_len := core_models.option.Option.None))))
            else do
              let b2 : u8 ← v[i1]_?
              let ok2 : Bool ←
                if (← ((v.val[index.toNat]'hi) ==? (240 : u8))) then do
                  ((← (b2 >=? (144 : u8))) &&? (← (b2 <=? (191 : u8))))
                else do
                  if
                  (← ((← ((v.val[index.toNat]'hi) >=? (241 : u8)))
                    &&? (← ((v.val[index.toNat]'hi) <=? (243 : u8))))) then do
                    ((← (b2 >=? (128 : u8))) &&? (← (b2 <=? (191 : u8))))
                  else do
                    if (← ((v.val[index.toNat]'hi) ==? (244 : u8))) then do
                      ((← (b2 >=? (128 : u8))) &&? (← (b2 <=? (143 : u8))))
                    else do
                      (pure false)
              if (← (!? ok2)) then do
                (pure (core_models.result.Result.Err
                  (run_utf8_validation_u8.Utf8Error.mk
                    (valid_up_to := index)
                    (error_len := (core_models.option.Option.Some (1 : u8))))))
              else do
                let i2 : usize ← (i1 +? (1 : usize))
                if (← (i2 >=? USize64.ofNat v.val.size)) then do
                  (pure (core_models.result.Result.Err
                    (run_utf8_validation_u8.Utf8Error.mk
                      (valid_up_to := index)
                      (error_len := core_models.option.Option.None))))
                else do
                  if
                  (← ((← ((← v[i2]_?) &&&? (192 : u8))) !=? (128 : u8))) then do
                    (pure (core_models.result.Result.Err
                      (run_utf8_validation_u8.Utf8Error.mk
                        (valid_up_to := index)
                        (error_len := (core_models.option.Option.Some
                          (2 : u8))))))
                  else do
                    let i3 : usize ← (i2 +? (1 : usize))
                    if (← (i3 >=? USize64.ofNat v.val.size)) then do
                      (pure (core_models.result.Result.Err
                        (run_utf8_validation_u8.Utf8Error.mk
                          (valid_up_to := index)
                          (error_len := core_models.option.Option.None))))
                    else do
                      if
                      (← ((← ((← v[i3]_?) &&&? (192 : u8))) !=? (128 : u8))) then do
                        (pure (core_models.result.Result.Err
                          (run_utf8_validation_u8.Utf8Error.mk
                            (valid_up_to := index)
                            (error_len := (core_models.option.Option.Some
                              (3 : u8))))))
                      else do
                        (run_utf8_validation_u8.validate_at v (← (i3 +? (1 : usize))))
          else do
            (pure (core_models.result.Result.Err
              (run_utf8_validation_u8.Utf8Error.mk
                (valid_up_to := index)
                (error_len := (core_models.option.Option.Some (1 : u8))))))) := by
  conv => lhs; unfold run_utf8_validation_u8.validate_at
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat v.val.size ≤ index) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]; omega
  have h_idx := getElem_ok v index hi
  have h_first_ge : ¬ ((v.val[index.toNat]'hi) < (128 : u8)) := by
    rw [UInt8.lt_iff_toNat_lt, u8_128_toNat]; omega
  have h_lt : decide ((v.val[index.toNat]'hi) < (128 : u8)) = false :=
    decide_eq_false h_first_ge
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx, rust_primitives.cmp.lt, h_lt]

/-! ### Width-2 step lemmas. -/

/-- Width-2 branch: index < size, 194 ≤ first < 224, computes i1 = index + 1. -/
private theorem validate_at_w2_unfold (v : RustSlice u8) (index : usize)
    (hi : index.toNat < v.val.size)
    (h_lo : 194 ≤ (v.val[index.toNat]'hi).toNat)
    (h_hi : (v.val[index.toNat]'hi).toNat < 224) :
    run_utf8_validation_u8.validate_at v index = (do
      let i1 : usize ← (index +? (1 : usize))
      if (← (i1 >=? USize64.ofNat v.val.size)) then do
        (pure (core_models.result.Result.Err
          (run_utf8_validation_u8.Utf8Error.mk
            (valid_up_to := index)
            (error_len := core_models.option.Option.None))))
      else do
        if (← ((← ((← v[i1]_?) &&&? (192 : u8))) !=? (128 : u8))) then do
          (pure (core_models.result.Result.Err
            (run_utf8_validation_u8.Utf8Error.mk
              (valid_up_to := index)
              (error_len := (core_models.option.Option.Some (1 : u8))))))
        else do
          (run_utf8_validation_u8.validate_at v (← (i1 +? (1 : usize))))) := by
  have h_ge : 128 ≤ (v.val[index.toNat]'hi).toNat := by omega
  rw [validate_at_non_ascii_unfold v index hi h_ge]
  have h_w := utf8_char_width_w2 (v.val[index.toNat]'hi) h_lo h_hi
  have h_w2 : decide ((2 : usize) = (2 : usize)) = true := by decide
  simp only [h_w, RustM_ok_bind, rust_primitives.cmp.eq, pure_bind,
             show ((2 : usize) == (2 : usize)) = true from rfl,
             ↓reduceIte]

/-- Width-3 branch unfolding. -/
private theorem validate_at_w3_unfold (v : RustSlice u8) (index : usize)
    (hi : index.toNat < v.val.size)
    (h_lo : 224 ≤ (v.val[index.toNat]'hi).toNat)
    (h_hi : (v.val[index.toNat]'hi).toNat < 240) :
    run_utf8_validation_u8.validate_at v index = (do
      let i1 : usize ← (index +? (1 : usize))
      if (← (i1 >=? USize64.ofNat v.val.size)) then do
        (pure (core_models.result.Result.Err
          (run_utf8_validation_u8.Utf8Error.mk
            (valid_up_to := index)
            (error_len := core_models.option.Option.None))))
      else do
        let b2 : u8 ← v[i1]_?
        let ok2 : Bool ←
          if (← ((v.val[index.toNat]'hi) ==? (224 : u8))) then do
            ((← (b2 >=? (160 : u8))) &&? (← (b2 <=? (191 : u8))))
          else do
            if
            (← ((← ((v.val[index.toNat]'hi) >=? (225 : u8))) &&?
                (← ((v.val[index.toNat]'hi) <=? (236 : u8))))) then do
              ((← (b2 >=? (128 : u8))) &&? (← (b2 <=? (191 : u8))))
            else do
              if (← ((v.val[index.toNat]'hi) ==? (237 : u8))) then do
                ((← (b2 >=? (128 : u8))) &&? (← (b2 <=? (159 : u8))))
              else do
                if
                (← ((← ((v.val[index.toNat]'hi) >=? (238 : u8)))
                  &&? (← ((v.val[index.toNat]'hi) <=? (239 : u8))))) then do
                  ((← (b2 >=? (128 : u8))) &&? (← (b2 <=? (191 : u8))))
                else do
                  (pure false)
        if (← (!? ok2)) then do
          (pure (core_models.result.Result.Err
            (run_utf8_validation_u8.Utf8Error.mk
              (valid_up_to := index)
              (error_len := (core_models.option.Option.Some (1 : u8))))))
        else do
          let i2 : usize ← (i1 +? (1 : usize))
          if (← (i2 >=? USize64.ofNat v.val.size)) then do
            (pure (core_models.result.Result.Err
              (run_utf8_validation_u8.Utf8Error.mk
                (valid_up_to := index)
                (error_len := core_models.option.Option.None))))
          else do
            if
            (← ((← ((← v[i2]_?) &&&? (192 : u8))) !=? (128 : u8))) then do
              (pure (core_models.result.Result.Err
                (run_utf8_validation_u8.Utf8Error.mk
                  (valid_up_to := index)
                  (error_len := (core_models.option.Option.Some
                    (2 : u8))))))
            else do
              (run_utf8_validation_u8.validate_at v (← (i2 +? (1 : usize))))) := by
  have h_ge : 128 ≤ (v.val[index.toNat]'hi).toNat := by omega
  rw [validate_at_non_ascii_unfold v index hi h_ge]
  have h_w := utf8_char_width_w3 (v.val[index.toNat]'hi) h_lo h_hi
  have h_neq2 : ((3 : usize) == (2 : usize)) = false := by decide
  have h_eq3 : ((3 : usize) == (3 : usize)) = true := by decide
  simp only [h_w, RustM_ok_bind, rust_primitives.cmp.eq, pure_bind,
             h_neq2, h_eq3, Bool.false_eq_true, ↓reduceIte]

/-- Width-4 branch unfolding. -/
private theorem validate_at_w4_unfold (v : RustSlice u8) (index : usize)
    (hi : index.toNat < v.val.size)
    (h_lo : 240 ≤ (v.val[index.toNat]'hi).toNat)
    (h_hi : (v.val[index.toNat]'hi).toNat < 245) :
    run_utf8_validation_u8.validate_at v index = (do
      let i1 : usize ← (index +? (1 : usize))
      if (← (i1 >=? USize64.ofNat v.val.size)) then do
        (pure (core_models.result.Result.Err
          (run_utf8_validation_u8.Utf8Error.mk
            (valid_up_to := index)
            (error_len := core_models.option.Option.None))))
      else do
        let b2 : u8 ← v[i1]_?
        let ok2 : Bool ←
          if (← ((v.val[index.toNat]'hi) ==? (240 : u8))) then do
            ((← (b2 >=? (144 : u8))) &&? (← (b2 <=? (191 : u8))))
          else do
            if
            (← ((← ((v.val[index.toNat]'hi) >=? (241 : u8)))
              &&? (← ((v.val[index.toNat]'hi) <=? (243 : u8))))) then do
              ((← (b2 >=? (128 : u8))) &&? (← (b2 <=? (191 : u8))))
            else do
              if (← ((v.val[index.toNat]'hi) ==? (244 : u8))) then do
                ((← (b2 >=? (128 : u8))) &&? (← (b2 <=? (143 : u8))))
              else do
                (pure false)
        if (← (!? ok2)) then do
          (pure (core_models.result.Result.Err
            (run_utf8_validation_u8.Utf8Error.mk
              (valid_up_to := index)
              (error_len := (core_models.option.Option.Some (1 : u8))))))
        else do
          let i2 : usize ← (i1 +? (1 : usize))
          if (← (i2 >=? USize64.ofNat v.val.size)) then do
            (pure (core_models.result.Result.Err
              (run_utf8_validation_u8.Utf8Error.mk
                (valid_up_to := index)
                (error_len := core_models.option.Option.None))))
          else do
            if
            (← ((← ((← v[i2]_?) &&&? (192 : u8))) !=? (128 : u8))) then do
              (pure (core_models.result.Result.Err
                (run_utf8_validation_u8.Utf8Error.mk
                  (valid_up_to := index)
                  (error_len := (core_models.option.Option.Some
                    (2 : u8))))))
            else do
              let i3 : usize ← (i2 +? (1 : usize))
              if (← (i3 >=? USize64.ofNat v.val.size)) then do
                (pure (core_models.result.Result.Err
                  (run_utf8_validation_u8.Utf8Error.mk
                    (valid_up_to := index)
                    (error_len := core_models.option.Option.None))))
              else do
                if
                (← ((← ((← v[i3]_?) &&&? (192 : u8))) !=? (128 : u8))) then do
                  (pure (core_models.result.Result.Err
                    (run_utf8_validation_u8.Utf8Error.mk
                      (valid_up_to := index)
                      (error_len := (core_models.option.Option.Some
                        (3 : u8))))))
                else do
                  (run_utf8_validation_u8.validate_at v (← (i3 +? (1 : usize))))) := by
  have h_ge : 128 ≤ (v.val[index.toNat]'hi).toNat := by omega
  rw [validate_at_non_ascii_unfold v index hi h_ge]
  have h_w := utf8_char_width_w4 (v.val[index.toNat]'hi) h_lo h_hi
  have h_neq2 : ((4 : usize) == (2 : usize)) = false := by decide
  have h_neq3 : ((4 : usize) == (3 : usize)) = false := by decide
  have h_eq4 : ((4 : usize) == (4 : usize)) = true := by decide
  simp only [h_w, RustM_ok_bind, rust_primitives.cmp.eq, pure_bind,
             h_neq2, h_neq3, h_eq4, Bool.false_eq_true, ↓reduceIte]

/-- Width-0 branch (invalid leader, 128 ≤ first < 194 or first ≥ 245). -/
private theorem validate_at_w0 (v : RustSlice u8) (index : usize)
    (hi : index.toNat < v.val.size)
    (h_w0 : (128 ≤ (v.val[index.toNat]'hi).toNat ∧ (v.val[index.toNat]'hi).toNat < 194) ∨
            245 ≤ (v.val[index.toNat]'hi).toNat) :
    run_utf8_validation_u8.validate_at v index =
      RustM.ok (core_models.result.Result.Err
        (run_utf8_validation_u8.Utf8Error.mk
          (valid_up_to := index)
          (error_len := (core_models.option.Option.Some (1 : u8))))) := by
  have h_ge : 128 ≤ (v.val[index.toNat]'hi).toNat := by
    rcases h_w0 with ⟨h1, _⟩ | h1
    · exact h1
    · omega
  rw [validate_at_non_ascii_unfold v index hi h_ge]
  have h_w : run_utf8_validation_u8.utf8_char_width (v.val[index.toNat]'hi) = RustM.ok (0 : usize) := by
    rcases h_w0 with ⟨h1, h2⟩ | h1
    · exact utf8_char_width_w0_small _ h1 h2
    · exact utf8_char_width_w0_large _ h1
  have h_neq2 : ((0 : usize) == (2 : usize)) = false := by decide
  have h_neq3 : ((0 : usize) == (3 : usize)) = false := by decide
  have h_neq4 : ((0 : usize) == (4 : usize)) = false := by decide
  simp only [h_w, RustM_ok_bind, rust_primitives.cmp.eq, pure_bind,
             h_neq2, h_neq3, h_neq4, Bool.false_eq_true, ↓reduceIte]
  rfl

/-! ### Continuation-byte and SecondByteOk decision lemmas. -/

/-- Helper lemma: for any Nat-bounded value, the AND with 192 is 128 iff
    the value lies in [128, 192). Proved by `native_decide` on the Fin range. -/
private theorem nat_and_192_iff (n : Nat) (h : n < 256) :
    (n &&& 192 = 128) ↔ (128 ≤ n ∧ n ≤ 191) := by
  have hcases : ∀ k : Fin 256, (k.val &&& 192 = 128) ↔ (128 ≤ k.val ∧ k.val ≤ 191) := by
    native_decide
  exact hcases ⟨n, h⟩

/-- Continuation byte iff bit pattern `(b &&& 0xC0) = 0x80`. -/
private theorem cont_byte_iff (b : u8) :
    (b &&& (192 : u8)) = (128 : u8) ↔ IsContByte b := by
  unfold IsContByte
  rw [← UInt8.toNat_inj]
  rw [u8_128_toNat]
  have h_and : (b &&& (192 : u8)).toNat = b.toNat &&& (192 : u8).toNat := by
    simp [UInt8.toNat_and]
  rw [h_and, u8_192_toNat]
  exact nat_and_192_iff b.toNat b.toNat_lt

/-- Negated form for the != branches in the recursive body. -/
private theorem cont_byte_ne_iff (b : u8) :
    ¬ ((b &&& (192 : u8)) = (128 : u8)) ↔ ¬ IsContByte b := by
  exact not_congr (cont_byte_iff b)

/-! ### Leaf step lemmas for the width-2 branches. -/

private theorem validate_at_w2_trunc (v : RustSlice u8) (index : usize)
    (hi : index.toNat < v.val.size)
    (h_lo : 194 ≤ (v.val[index.toNat]'hi).toNat)
    (h_hi : (v.val[index.toNat]'hi).toNat < 224)
    (h_trunc : v.val.size ≤ index.toNat + 1) :
    run_utf8_validation_u8.validate_at v index =
      RustM.ok (core_models.result.Result.Err
        (run_utf8_validation_u8.Utf8Error.mk
          (valid_up_to := index)
          (error_len := core_models.option.Option.None))) := by
  rw [validate_at_w2_unfold v index hi h_lo h_hi]
  have h_size_lt : v.val.size < 2^64 := v.size_lt_usizeSize
  have h_no_ov : index.toNat + 1 < 2^64 := by omega
  have h_add := usize_add_one_ok index h_no_ov
  have h_i1_toNat : (index + 1).toNat = index.toNat + 1 := usize_add_one_toNat _ h_no_ov
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat v.val.size ≤ index + 1) = true := by
    rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat, h_i1_toNat]
    omega
  simp only [h_add, RustM_ok_bind, rust_primitives.cmp.ge, pure_bind, h_cond, ↓reduceIte]
  rfl

private theorem validate_at_w2_bad_cont (v : RustSlice u8) (index : usize)
    (hi : index.toNat < v.val.size)
    (h_lo : 194 ≤ (v.val[index.toNat]'hi).toNat)
    (h_hi : (v.val[index.toNat]'hi).toNat < 224)
    (hi1 : index.toNat + 1 < v.val.size)
    (h_bad : ¬ IsContByte (v.val[index.toNat + 1]'hi1)) :
    run_utf8_validation_u8.validate_at v index =
      RustM.ok (core_models.result.Result.Err
        (run_utf8_validation_u8.Utf8Error.mk
          (valid_up_to := index)
          (error_len := core_models.option.Option.Some (1 : u8)))) := by
  rw [validate_at_w2_unfold v index hi h_lo h_hi]
  have h_size_lt : v.val.size < 2^64 := v.size_lt_usizeSize
  have h_no_ov : index.toNat + 1 < 2^64 := by omega
  have h_add := usize_add_one_ok index h_no_ov
  have h_i1_toNat : (index + 1).toNat = index.toNat + 1 := usize_add_one_toNat _ h_no_ov
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat v.val.size ≤ index + 1) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat, h_i1_toNat]
    omega
  have hi1_take : (index + 1).toNat < v.val.size := by rw [h_i1_toNat]; exact hi1
  have h_idx : (v[index + 1]_? : RustM u8) = RustM.ok (v.val[(index + 1).toNat]'hi1_take) :=
    getElem_ok v (index + 1) hi1_take
  have h_eq_get : v.val[(index + 1).toNat]'hi1_take = v.val[index.toNat + 1]'hi1 := by
    congr 1
  have h_and_eq : (v.val[(index + 1).toNat]'hi1_take &&& (192 : u8)) =
                  (v.val[index.toNat + 1]'hi1 &&& (192 : u8)) := by
    rw [h_eq_get]
  have h_ne : ((v.val[(index + 1).toNat]'hi1_take) &&& (192 : u8)) ≠ (128 : u8) := by
    rw [h_and_eq]
    intro h_eq
    exact h_bad ((cont_byte_iff (v.val[index.toNat + 1]'hi1)).mp h_eq)
  have h_bne : ((v.val[(index + 1).toNat]'hi1_take) &&& (192 : u8) != (128 : u8)) = true := by
    exact bne_iff_ne.mpr h_ne
  simp only [h_add, RustM_ok_bind, rust_primitives.cmp.ge, pure_bind, h_cond,
             Bool.false_eq_true, ↓reduceIte, h_idx, rust_primitives.cmp.ne, h_bne,
             if_pos rfl, if_true]
  rfl

private theorem validate_at_w2_recurse (v : RustSlice u8) (index : usize)
    (hi : index.toNat < v.val.size)
    (h_lo : 194 ≤ (v.val[index.toNat]'hi).toNat)
    (h_hi : (v.val[index.toNat]'hi).toNat < 224)
    (hi1 : index.toNat + 1 < v.val.size)
    (h_cont : IsContByte (v.val[index.toNat + 1]'hi1)) :
    run_utf8_validation_u8.validate_at v index =
      run_utf8_validation_u8.validate_at v (index + 1 + 1) := by
  rw [validate_at_w2_unfold v index hi h_lo h_hi]
  have h_size_lt : v.val.size < 2^64 := v.size_lt_usizeSize
  have h_no_ov : index.toNat + 1 < 2^64 := by omega
  have h_add := usize_add_one_ok index h_no_ov
  have h_i1_toNat : (index + 1).toNat = index.toNat + 1 := usize_add_one_toNat _ h_no_ov
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat v.val.size ≤ index + 1) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat, h_i1_toNat]
    omega
  have hi1_take : (index + 1).toNat < v.val.size := by rw [h_i1_toNat]; exact hi1
  have h_idx : (v[index + 1]_? : RustM u8) = RustM.ok (v.val[(index + 1).toNat]'hi1_take) :=
    getElem_ok v (index + 1) hi1_take
  have h_eq_get : v.val[(index + 1).toNat]'hi1_take = v.val[index.toNat + 1]'hi1 := by
    congr 1
  have h_and_eq : (v.val[(index + 1).toNat]'hi1_take &&& (192 : u8)) = (128 : u8) := by
    rw [h_eq_get]
    exact (cont_byte_iff _).mpr h_cont
  have h_bne : ((v.val[(index + 1).toNat]'hi1_take) &&& (192 : u8) != (128 : u8)) = false := by
    rw [bne_eq_false_iff_eq]; exact h_and_eq
  have h_no_ov_i2 : (index + 1).toNat + 1 < 2^64 := by rw [h_i1_toNat]; omega
  have h_add_i2 := usize_add_one_ok (index + 1) h_no_ov_i2
  simp only [h_add, RustM_ok_bind, rust_primitives.cmp.ge, pure_bind, h_cond,
             Bool.false_eq_true, ↓reduceIte, h_idx, rust_primitives.cmp.ne, h_bne,
             h_add_i2]

-- (Width-3 / width-4 leaf step lemmas — written below `secondByteOk_w*_explicit`.)

/-! ### isValidUtf8From step lemmas. -/

/-- Common simp lemmas for collapsing `if N = K then ... else ...` over `Nat`. -/
private theorem nat_neq_simp : (1 : Nat) ≠ 2 ∧ (1 : Nat) ≠ 3 ∧ (1 : Nat) ≠ 4 ∧
                                (2 : Nat) ≠ 1 ∧ (2 : Nat) ≠ 3 ∧ (2 : Nat) ≠ 4 ∧
                                (3 : Nat) ≠ 1 ∧ (3 : Nat) ≠ 2 ∧ (3 : Nat) ≠ 4 ∧
                                (4 : Nat) ≠ 1 ∧ (4 : Nat) ≠ 2 ∧ (4 : Nat) ≠ 3 ∧
                                (0 : Nat) ≠ 1 ∧ (0 : Nat) ≠ 2 ∧ (0 : Nat) ≠ 3 ∧ (0 : Nat) ≠ 4 := by
  decide

/-- Common simp lemma: `if N = K then ... else ...` with concrete N ≠ K. -/
private theorem isValidUtf8From_unfold_at (bs : Array u8) (k : Nat) (hk : k < bs.size) :
    isValidUtf8From bs k =
      let b1 := bs[k]'hk
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
      else false := by
  conv => lhs; unfold isValidUtf8From
  rw [dif_neg (by omega)]

/-- Base case: OOB ⇒ true. -/
private theorem isValidUtf8From_oob (bs : Array u8) (k : Nat) (hk : bs.size ≤ k) :
    isValidUtf8From bs k = true := by
  conv => lhs; unfold isValidUtf8From
  rw [dif_pos hk]

/-- ASCII step: k < size, bs[k] < 128 ⇒ recurse to k+1. -/
private theorem isValidUtf8From_ascii (bs : Array u8) (k : Nat) (hk : k < bs.size)
    (h_ascii : (bs[k]'hk).toNat < 128) :
    isValidUtf8From bs k = isValidUtf8From bs (k + 1) := by
  rw [isValidUtf8From_unfold_at bs k hk]
  have h_lw : leadWidth (bs[k]'hk) = 1 := by unfold leadWidth; rw [if_pos h_ascii]
  simp only [h_lw, if_pos rfl, if_true]

/-- Invalid leader (width = 0): returns false. -/
private theorem isValidUtf8From_invalid (bs : Array u8) (k : Nat) (hk : k < bs.size)
    (h_lw : leadWidth (bs[k]'hk) = 0) :
    isValidUtf8From bs k = false := by
  rw [isValidUtf8From_unfold_at bs k hk]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h01, h02, h03, h04⟩ := nat_neq_simp
  simp only [h_lw, if_neg h01, if_neg h02, if_neg h03, if_neg h04]

/-- Width-2 truncation: leadWidth = 2, k+1 ≥ size ⇒ false. -/
private theorem isValidUtf8From_w2_trunc (bs : Array u8) (k : Nat) (hk : k < bs.size)
    (h_lw : leadWidth (bs[k]'hk) = 2) (h_trunc : bs.size ≤ k + 1) :
    isValidUtf8From bs k = false := by
  rw [isValidUtf8From_unfold_at bs k hk]
  obtain ⟨_, _, _, h21, _, _, _, _, _, _, _, _, _, _, _, _⟩ := nat_neq_simp
  simp only [h_lw, if_neg h21, if_pos rfl, if_true,
             dif_neg (show ¬ (k + 1 < bs.size) by omega)]

/-- Width-2 bad continuation byte ⇒ false. -/
private theorem isValidUtf8From_w2_bad (bs : Array u8) (k : Nat) (hk : k < bs.size)
    (h_lw : leadWidth (bs[k]'hk) = 2) (hk1 : k + 1 < bs.size)
    (h_bad : ¬ IsContByte (bs[k+1]'hk1)) :
    isValidUtf8From bs k = false := by
  rw [isValidUtf8From_unfold_at bs k hk]
  obtain ⟨_, _, _, h21, _, _, _, _, _, _, _, _, _, _, _, _⟩ := nat_neq_simp
  simp only [h_lw, if_neg h21, if_pos rfl, if_true, dif_pos hk1,
             decide_eq_false h_bad, Bool.false_and]

/-- Width-2 valid: leadWidth = 2, cont byte ok ⇒ recurse to k+2. -/
private theorem isValidUtf8From_w2_ok (bs : Array u8) (k : Nat) (hk : k < bs.size)
    (h_lw : leadWidth (bs[k]'hk) = 2) (hk1 : k + 1 < bs.size)
    (h_cont : IsContByte (bs[k+1]'hk1)) :
    isValidUtf8From bs k = isValidUtf8From bs (k + 2) := by
  rw [isValidUtf8From_unfold_at bs k hk]
  obtain ⟨_, _, _, h21, _, _, _, _, _, _, _, _, _, _, _, _⟩ := nat_neq_simp
  simp only [h_lw, if_neg h21, if_pos rfl, if_true, dif_pos hk1,
             decide_eq_true h_cont, Bool.true_and]

/-- Width-3 truncation at first continuation: leadWidth = 3, k+1 ≥ size ⇒ false. -/
private theorem isValidUtf8From_w3_trunc1 (bs : Array u8) (k : Nat) (hk : k < bs.size)
    (h_lw : leadWidth (bs[k]'hk) = 3) (h_trunc : bs.size ≤ k + 1) :
    isValidUtf8From bs k = false := by
  rw [isValidUtf8From_unfold_at bs k hk]
  obtain ⟨_, _, _, _, _, _, h31, h32, _, _, _, _, _, _, _, _⟩ := nat_neq_simp
  simp only [h_lw, if_neg h31, if_neg h32, if_pos rfl, if_true,
             dif_neg (show ¬ (k + 1 < bs.size) by omega)]

/-- Width-3 bad second byte ⇒ false. -/
private theorem isValidUtf8From_w3_bad_second (bs : Array u8) (k : Nat) (hk : k < bs.size)
    (h_lw : leadWidth (bs[k]'hk) = 3) (hk1 : k + 1 < bs.size)
    (h_bad : ¬ SecondByteOk (bs[k]'hk) (bs[k+1]'hk1)) :
    isValidUtf8From bs k = false := by
  rw [isValidUtf8From_unfold_at bs k hk]
  obtain ⟨_, _, _, _, _, _, h31, h32, _, _, _, _, _, _, _, _⟩ := nat_neq_simp
  simp only [h_lw, if_neg h31, if_neg h32, if_pos rfl, if_true, dif_pos hk1,
             decide_eq_false h_bad]
  rfl

/-- Width-3 truncation at second continuation ⇒ false. -/
private theorem isValidUtf8From_w3_trunc2 (bs : Array u8) (k : Nat) (hk : k < bs.size)
    (h_lw : leadWidth (bs[k]'hk) = 3) (hk1 : k + 1 < bs.size)
    (h_sbo : SecondByteOk (bs[k]'hk) (bs[k+1]'hk1)) (h_trunc : bs.size ≤ k + 2) :
    isValidUtf8From bs k = false := by
  rw [isValidUtf8From_unfold_at bs k hk]
  obtain ⟨_, _, _, _, _, _, h31, h32, _, _, _, _, _, _, _, _⟩ := nat_neq_simp
  simp only [h_lw, if_neg h31, if_neg h32, if_pos rfl, if_true, dif_pos hk1,
             decide_eq_true h_sbo,
             show ((true : Bool) = true) = True from by simp, if_true,
             dif_neg (show ¬ (k + 2 < bs.size) by omega)]

/-- Width-3 bad third byte (not continuation) ⇒ false. -/
private theorem isValidUtf8From_w3_bad_third (bs : Array u8) (k : Nat) (hk : k < bs.size)
    (h_lw : leadWidth (bs[k]'hk) = 3) (hk1 : k + 1 < bs.size)
    (h_sbo : SecondByteOk (bs[k]'hk) (bs[k+1]'hk1)) (hk2 : k + 2 < bs.size)
    (h_bad : ¬ IsContByte (bs[k+2]'hk2)) :
    isValidUtf8From bs k = false := by
  rw [isValidUtf8From_unfold_at bs k hk]
  obtain ⟨_, _, _, _, _, _, h31, h32, _, _, _, _, _, _, _, _⟩ := nat_neq_simp
  simp only [h_lw, if_neg h31, if_neg h32, if_pos rfl, if_true, dif_pos hk1,
             decide_eq_true h_sbo,
             show ((true : Bool) = true) = True from by simp, if_true,
             dif_pos hk2, decide_eq_false h_bad, Bool.false_and]

/-- Width-3 valid: recurse to k+3. -/
private theorem isValidUtf8From_w3_ok (bs : Array u8) (k : Nat) (hk : k < bs.size)
    (h_lw : leadWidth (bs[k]'hk) = 3) (hk1 : k + 1 < bs.size)
    (h_sbo : SecondByteOk (bs[k]'hk) (bs[k+1]'hk1)) (hk2 : k + 2 < bs.size)
    (h_cont : IsContByte (bs[k+2]'hk2)) :
    isValidUtf8From bs k = isValidUtf8From bs (k + 3) := by
  rw [isValidUtf8From_unfold_at bs k hk]
  obtain ⟨_, _, _, _, _, _, h31, h32, _, _, _, _, _, _, _, _⟩ := nat_neq_simp
  simp only [h_lw, if_neg h31, if_neg h32, if_pos rfl, if_true, dif_pos hk1,
             decide_eq_true h_sbo,
             show ((true : Bool) = true) = True from by simp, if_true,
             dif_pos hk2, decide_eq_true h_cont, Bool.true_and]

/-- Width-4 truncation at first continuation ⇒ false. -/
private theorem isValidUtf8From_w4_trunc1 (bs : Array u8) (k : Nat) (hk : k < bs.size)
    (h_lw : leadWidth (bs[k]'hk) = 4) (h_trunc : bs.size ≤ k + 1) :
    isValidUtf8From bs k = false := by
  rw [isValidUtf8From_unfold_at bs k hk]
  obtain ⟨_, _, _, _, _, _, _, _, _, h41, h42, h43, _, _, _, _⟩ := nat_neq_simp
  simp only [h_lw, if_neg h41, if_neg h42, if_neg h43, if_pos rfl, if_true,
             dif_neg (show ¬ (k + 1 < bs.size) by omega)]

/-- Width-4 bad second byte ⇒ false. -/
private theorem isValidUtf8From_w4_bad_second (bs : Array u8) (k : Nat) (hk : k < bs.size)
    (h_lw : leadWidth (bs[k]'hk) = 4) (hk1 : k + 1 < bs.size)
    (h_bad : ¬ SecondByteOk (bs[k]'hk) (bs[k+1]'hk1)) :
    isValidUtf8From bs k = false := by
  rw [isValidUtf8From_unfold_at bs k hk]
  obtain ⟨_, _, _, _, _, _, _, _, _, h41, h42, h43, _, _, _, _⟩ := nat_neq_simp
  simp only [h_lw, if_neg h41, if_neg h42, if_neg h43, if_pos rfl, if_true, dif_pos hk1,
             decide_eq_false h_bad]
  rfl

/-- Width-4 truncation at second continuation ⇒ false. -/
private theorem isValidUtf8From_w4_trunc2 (bs : Array u8) (k : Nat) (hk : k < bs.size)
    (h_lw : leadWidth (bs[k]'hk) = 4) (hk1 : k + 1 < bs.size)
    (h_sbo : SecondByteOk (bs[k]'hk) (bs[k+1]'hk1)) (h_trunc : bs.size ≤ k + 2) :
    isValidUtf8From bs k = false := by
  rw [isValidUtf8From_unfold_at bs k hk]
  obtain ⟨_, _, _, _, _, _, _, _, _, h41, h42, h43, _, _, _, _⟩ := nat_neq_simp
  simp only [h_lw, if_neg h41, if_neg h42, if_neg h43, if_pos rfl, if_true, dif_pos hk1,
             decide_eq_true h_sbo,
             show ((true : Bool) = true) = True from by simp, if_true,
             dif_neg (show ¬ (k + 2 < bs.size) by omega)]

/-- Width-4 bad third byte ⇒ false. -/
private theorem isValidUtf8From_w4_bad_third (bs : Array u8) (k : Nat) (hk : k < bs.size)
    (h_lw : leadWidth (bs[k]'hk) = 4) (hk1 : k + 1 < bs.size)
    (h_sbo : SecondByteOk (bs[k]'hk) (bs[k+1]'hk1)) (hk2 : k + 2 < bs.size)
    (h_bad : ¬ IsContByte (bs[k+2]'hk2)) :
    isValidUtf8From bs k = false := by
  rw [isValidUtf8From_unfold_at bs k hk]
  obtain ⟨_, _, _, _, _, _, _, _, _, h41, h42, h43, _, _, _, _⟩ := nat_neq_simp
  simp only [h_lw, if_neg h41, if_neg h42, if_neg h43, if_pos rfl, if_true, dif_pos hk1,
             decide_eq_true h_sbo,
             show ((true : Bool) = true) = True from by simp, if_true,
             dif_pos hk2, decide_eq_false h_bad,
             show ((false : Bool) = true) = False from by simp, if_false]

/-- Width-4 truncation at third continuation ⇒ false. -/
private theorem isValidUtf8From_w4_trunc3 (bs : Array u8) (k : Nat) (hk : k < bs.size)
    (h_lw : leadWidth (bs[k]'hk) = 4) (hk1 : k + 1 < bs.size)
    (h_sbo : SecondByteOk (bs[k]'hk) (bs[k+1]'hk1)) (hk2 : k + 2 < bs.size)
    (h_cont2 : IsContByte (bs[k+2]'hk2)) (h_trunc : bs.size ≤ k + 3) :
    isValidUtf8From bs k = false := by
  rw [isValidUtf8From_unfold_at bs k hk]
  obtain ⟨_, _, _, _, _, _, _, _, _, h41, h42, h43, _, _, _, _⟩ := nat_neq_simp
  simp only [h_lw, if_neg h41, if_neg h42, if_neg h43, if_pos rfl, if_true, dif_pos hk1,
             decide_eq_true h_sbo,
             show ((true : Bool) = true) = True from by simp, if_true,
             dif_pos hk2, decide_eq_true h_cont2, if_true,
             dif_neg (show ¬ (k + 3 < bs.size) by omega)]

/-- Width-4 bad fourth byte ⇒ false. -/
private theorem isValidUtf8From_w4_bad_fourth (bs : Array u8) (k : Nat) (hk : k < bs.size)
    (h_lw : leadWidth (bs[k]'hk) = 4) (hk1 : k + 1 < bs.size)
    (h_sbo : SecondByteOk (bs[k]'hk) (bs[k+1]'hk1)) (hk2 : k + 2 < bs.size)
    (h_cont2 : IsContByte (bs[k+2]'hk2)) (hk3 : k + 3 < bs.size)
    (h_bad : ¬ IsContByte (bs[k+3]'hk3)) :
    isValidUtf8From bs k = false := by
  rw [isValidUtf8From_unfold_at bs k hk]
  obtain ⟨_, _, _, _, _, _, _, _, _, h41, h42, h43, _, _, _, _⟩ := nat_neq_simp
  simp only [h_lw, if_neg h41, if_neg h42, if_neg h43, if_pos rfl, if_true, dif_pos hk1,
             decide_eq_true h_sbo,
             show ((true : Bool) = true) = True from by simp, if_true,
             dif_pos hk2, decide_eq_true h_cont2, if_true,
             dif_pos hk3, decide_eq_false h_bad, Bool.false_and]

/-- Width-4 valid: recurse to k+4. -/
private theorem isValidUtf8From_w4_ok (bs : Array u8) (k : Nat) (hk : k < bs.size)
    (h_lw : leadWidth (bs[k]'hk) = 4) (hk1 : k + 1 < bs.size)
    (h_sbo : SecondByteOk (bs[k]'hk) (bs[k+1]'hk1)) (hk2 : k + 2 < bs.size)
    (h_cont2 : IsContByte (bs[k+2]'hk2)) (hk3 : k + 3 < bs.size)
    (h_cont3 : IsContByte (bs[k+3]'hk3)) :
    isValidUtf8From bs k = isValidUtf8From bs (k + 4) := by
  rw [isValidUtf8From_unfold_at bs k hk]
  obtain ⟨_, _, _, _, _, _, _, _, _, h41, h42, h43, _, _, _, _⟩ := nat_neq_simp
  simp only [h_lw, if_neg h41, if_neg h42, if_neg h43, if_pos rfl, if_true, dif_pos hk1,
             decide_eq_true h_sbo,
             show ((true : Bool) = true) = True from by simp, if_true,
             dif_pos hk2, decide_eq_true h_cont2, if_true,
             dif_pos hk3, decide_eq_true h_cont3, Bool.true_and]

/-! ### Array.take helpers used by the prefix-valid invariant. -/

private theorem array_take_size_le (bs : Array u8) (m : Nat) (h : m ≤ bs.size) :
    (bs.take m).size = m := by
  simp [Array.take, Nat.min_eq_left h]

private theorem array_take_getElem (bs : Array u8) (m : Nat) (i : Nat)
    (hi : i < m) (h : m ≤ bs.size) :
    (bs.take m)[i]'(by rw [array_take_size_le bs m h]; exact hi) =
      bs[i]'(Nat.lt_of_lt_of_le hi h) := by
  simp [Array.take]

/-! ### SecondByteOk evaluation: the explicit chain in the Rust code matches `SecondByteOk`. -/

private theorem secondByteOk_w3_explicit (first b2 : u8)
    (h1 : 224 ≤ first.toNat) (h2 : first.toNat < 240) :
    SecondByteOk first b2 ↔
      ((first = 0xE0 ∧ b2.toNat ≥ 0xA0 ∧ b2.toNat ≤ 0xBF) ∨
       (0xE1 ≤ first.toNat ∧ first.toNat ≤ 0xEC ∧ b2.toNat ≥ 0x80 ∧ b2.toNat ≤ 0xBF) ∨
       (first = 0xED ∧ b2.toNat ≥ 0x80 ∧ b2.toNat ≤ 0x9F) ∨
       (0xEE ≤ first.toNat ∧ first.toNat ≤ 0xEF ∧ b2.toNat ≥ 0x80 ∧ b2.toNat ≤ 0xBF)) := by
  unfold SecondByteOk
  constructor
  · intro h
    rcases h with ⟨hf, ha, hb⟩ | ⟨hf1, hf2, ha, hb⟩ | ⟨hf, ha, hb⟩ |
                  ⟨hf1, hf2, ha, hb⟩ | ⟨hf, _, _⟩ | ⟨hf1, _, _, _⟩ | ⟨hf, _, _⟩
    · left
      refine ⟨?_, ha, hb⟩
      apply UInt8.toNat_inj.mp; rw [hf, u8_E0_toNat]
    · right; left
      refine ⟨hf1, hf2, ha, hb⟩
    · right; right; left
      refine ⟨?_, ha, hb⟩
      apply UInt8.toNat_inj.mp; rw [hf, u8_237_toNat]
    · right; right; right
      refine ⟨hf1, hf2, ha, hb⟩
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
  · intro h
    rcases h with ⟨hf, ha, hb⟩ | ⟨hf1, hf2, ha, hb⟩ | ⟨hf, ha, hb⟩ | ⟨hf1, hf2, ha, hb⟩
    · left
      refine ⟨?_, ha, hb⟩
      rw [hf, u8_E0_toNat]
    · right; left
      refine ⟨hf1, hf2, ha, hb⟩
    · right; right; left
      refine ⟨?_, ha, hb⟩
      rw [hf, u8_237_toNat]
    · right; right; right; left
      refine ⟨hf1, hf2, ha, hb⟩

private theorem secondByteOk_w4_explicit (first b2 : u8)
    (h1 : 240 ≤ first.toNat) (h2 : first.toNat < 245) :
    SecondByteOk first b2 ↔
      ((first = 0xF0 ∧ b2.toNat ≥ 0x90 ∧ b2.toNat ≤ 0xBF) ∨
       (0xF1 ≤ first.toNat ∧ first.toNat ≤ 0xF3 ∧ b2.toNat ≥ 0x80 ∧ b2.toNat ≤ 0xBF) ∨
       (first = 0xF4 ∧ b2.toNat ≥ 0x80 ∧ b2.toNat ≤ 0x8F)) := by
  unfold SecondByteOk
  constructor
  · intro h
    rcases h with ⟨hf, _, _⟩ | ⟨hf1, hf2, _, _⟩ | ⟨hf, _, _⟩ |
                  ⟨hf1, hf2, _, _⟩ | ⟨hf, ha, hb⟩ | ⟨hf1, hf2, ha, hb⟩ | ⟨hf, ha, hb⟩
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · left
      refine ⟨?_, ha, hb⟩
      apply UInt8.toNat_inj.mp; rw [hf, u8_F0_toNat]
    · right; left
      refine ⟨hf1, hf2, ha, hb⟩
    · right; right
      refine ⟨?_, ha, hb⟩
      apply UInt8.toNat_inj.mp; rw [hf, u8_244_toNat]
  · intro h
    rcases h with ⟨hf, ha, hb⟩ | ⟨hf1, hf2, ha, hb⟩ | ⟨hf, ha, hb⟩
    · right; right; right; right; left
      exact ⟨by rw [hf, u8_F0_toNat], ha, hb⟩
    · right; right; right; right; right; left
      exact ⟨hf1, hf2, ha, hb⟩
    · right; right; right; right; right; right
      exact ⟨by rw [hf, u8_244_toNat], ha, hb⟩

/-! ## Master correctness lemma.

`validate_at_correct` returns a disjunction: either the function succeeds and
the bytes are valid UTF-8 from `index`, or it returns a specific `Err err` and
all the contract clauses about `err` hold. The strong induction is on the
measure `v.val.size - index.toNat`. -/

/-- Spec predicate (one side or the other holds for any well-formed
    `validate_at` call). -/
private def ValidateAtSpec (v : RustSlice u8) (index : usize)
    (r : core_models.result.Result rust_primitives.hax.Tuple0
              run_utf8_validation_u8.Utf8Error) : Prop :=
  match r with
  | core_models.result.Result.Ok _ =>
      isValidUtf8From v.val index.toNat = true
  | core_models.result.Result.Err err =>
      isValidUtf8From v.val index.toNat = false ∧
      index.toNat ≤ err.valid_up_to.toNat ∧
      err.valid_up_to.toNat ≤ v.val.size ∧
      isValidUtf8From (v.val.take err.valid_up_to.toNat) index.toNat = true ∧
      (∀ (n : u8), err.error_len = core_models.option.Option.Some n →
          1 ≤ n.toNat ∧ n.toNat ≤ 3 ∧
          err.valid_up_to.toNat + n.toNat ≤ v.val.size) ∧
      (err.error_len = core_models.option.Option.None →
          ∃ (hb : err.valid_up_to.toNat < v.val.size),
            2 ≤ leadWidth (v.val[err.valid_up_to.toNat]'hb) ∧
            v.val.size - err.valid_up_to.toNat <
              leadWidth (v.val[err.valid_up_to.toNat]'hb))

/-! ### Prefix-valid step-back helpers.

In the recursive cases, we have `isValidUtf8From (v.val.take K) (index + step) = true`
from the IH, and we need `isValidUtf8From (v.val.take K) index = true`. The proof
just runs `isValidUtf8From_X` (the step lemma) on the truncated array, using
`array_take_getElem` to identify the bytes. -/

private theorem prefix_valid_back_ascii (v : RustSlice u8) (index : usize) (K : Nat)
    (hi : index.toNat < v.val.size)
    (h_ascii : (v.val[index.toNat]'hi).toNat < 128)
    (hi_lt_K : index.toNat + 1 ≤ K) (hK_le : K ≤ v.val.size)
    (h : isValidUtf8From (v.val.take K) (index.toNat + 1) = true) :
    isValidUtf8From (v.val.take K) index.toNat = true := by
  have h_take_size : (v.val.take K).size = K := array_take_size_le v.val K hK_le
  have hi_lt_take : index.toNat < (v.val.take K).size := by rw [h_take_size]; omega
  have h_take_get :
      (v.val.take K)[index.toNat]'hi_lt_take = v.val[index.toNat]'hi := by
    exact array_take_getElem v.val K index.toNat (by omega) hK_le
  rw [isValidUtf8From_ascii _ _ hi_lt_take (by rw [h_take_get]; exact h_ascii)]
  exact h

private theorem prefix_valid_back_w2 (v : RustSlice u8) (index : usize) (K : Nat)
    (hi : index.toNat < v.val.size)
    (h_lo : 194 ≤ (v.val[index.toNat]'hi).toNat)
    (h_hi : (v.val[index.toNat]'hi).toNat < 224)
    (hi1 : index.toNat + 1 < v.val.size)
    (h_cont : IsContByte (v.val[index.toNat + 1]'hi1))
    (h_K_ge : index.toNat + 2 ≤ K) (hK_le : K ≤ v.val.size)
    (h : isValidUtf8From (v.val.take K) (index.toNat + 2) = true) :
    isValidUtf8From (v.val.take K) index.toNat = true := by
  have h_take_size : (v.val.take K).size = K := array_take_size_le v.val K hK_le
  have hi_lt_take : index.toNat < (v.val.take K).size := by rw [h_take_size]; omega
  have hi1_lt_take : index.toNat + 1 < (v.val.take K).size := by rw [h_take_size]; omega
  have h_take_get0 :
      (v.val.take K)[index.toNat]'hi_lt_take = v.val[index.toNat]'hi :=
    array_take_getElem v.val K index.toNat (by omega) hK_le
  have h_take_get1 :
      (v.val.take K)[index.toNat + 1]'hi1_lt_take = v.val[index.toNat + 1]'hi1 :=
    array_take_getElem v.val K (index.toNat + 1) (by omega) hK_le
  have h_lw : leadWidth ((v.val.take K)[index.toNat]'hi_lt_take) = 2 := by
    rw [h_take_get0]; unfold leadWidth
    have hge_128 : ¬ (v.val[index.toNat]'hi).toNat < 128 := by omega
    rw [if_neg hge_128]
    have hge_194 : ¬ (v.val[index.toNat]'hi).toNat < 194 := by omega
    rw [if_neg hge_194]
    rw [if_pos h_hi]
  have h_cont_take : IsContByte ((v.val.take K)[index.toNat + 1]'hi1_lt_take) := by
    rw [h_take_get1]; exact h_cont
  rw [isValidUtf8From_w2_ok _ _ hi_lt_take h_lw hi1_lt_take h_cont_take]
  exact h

private theorem prefix_valid_back_w3 (v : RustSlice u8) (index : usize) (K : Nat)
    (hi : index.toNat < v.val.size)
    (h_lo : 224 ≤ (v.val[index.toNat]'hi).toNat)
    (h_hi : (v.val[index.toNat]'hi).toNat < 240)
    (hi1 : index.toNat + 1 < v.val.size)
    (h_sbo : SecondByteOk (v.val[index.toNat]'hi) (v.val[index.toNat + 1]'hi1))
    (hi2 : index.toNat + 2 < v.val.size)
    (h_cont : IsContByte (v.val[index.toNat + 2]'hi2))
    (h_K_ge : index.toNat + 3 ≤ K) (hK_le : K ≤ v.val.size)
    (h : isValidUtf8From (v.val.take K) (index.toNat + 3) = true) :
    isValidUtf8From (v.val.take K) index.toNat = true := by
  have h_take_size : (v.val.take K).size = K := array_take_size_le v.val K hK_le
  have hi_lt_take : index.toNat < (v.val.take K).size := by rw [h_take_size]; omega
  have hi1_lt_take : index.toNat + 1 < (v.val.take K).size := by rw [h_take_size]; omega
  have hi2_lt_take : index.toNat + 2 < (v.val.take K).size := by rw [h_take_size]; omega
  have h_take_get0 :
      (v.val.take K)[index.toNat]'hi_lt_take = v.val[index.toNat]'hi :=
    array_take_getElem v.val K index.toNat (by omega) hK_le
  have h_take_get1 :
      (v.val.take K)[index.toNat + 1]'hi1_lt_take = v.val[index.toNat + 1]'hi1 :=
    array_take_getElem v.val K (index.toNat + 1) (by omega) hK_le
  have h_take_get2 :
      (v.val.take K)[index.toNat + 2]'hi2_lt_take = v.val[index.toNat + 2]'hi2 :=
    array_take_getElem v.val K (index.toNat + 2) (by omega) hK_le
  have h_lw : leadWidth ((v.val.take K)[index.toNat]'hi_lt_take) = 3 := by
    rw [h_take_get0]; unfold leadWidth
    rw [if_neg (by omega : ¬ (v.val[index.toNat]'hi).toNat < 128)]
    rw [if_neg (by omega : ¬ (v.val[index.toNat]'hi).toNat < 194)]
    rw [if_neg (by omega : ¬ (v.val[index.toNat]'hi).toNat < 224)]
    rw [if_pos h_hi]
  have h_sbo_take :
      SecondByteOk ((v.val.take K)[index.toNat]'hi_lt_take)
                   ((v.val.take K)[index.toNat + 1]'hi1_lt_take) := by
    rw [h_take_get0, h_take_get1]; exact h_sbo
  have h_cont_take : IsContByte ((v.val.take K)[index.toNat + 2]'hi2_lt_take) := by
    rw [h_take_get2]; exact h_cont
  rw [isValidUtf8From_w3_ok _ _ hi_lt_take h_lw hi1_lt_take h_sbo_take hi2_lt_take h_cont_take]
  exact h

private theorem prefix_valid_back_w4 (v : RustSlice u8) (index : usize) (K : Nat)
    (hi : index.toNat < v.val.size)
    (h_lo : 240 ≤ (v.val[index.toNat]'hi).toNat)
    (h_hi : (v.val[index.toNat]'hi).toNat < 245)
    (hi1 : index.toNat + 1 < v.val.size)
    (h_sbo : SecondByteOk (v.val[index.toNat]'hi) (v.val[index.toNat + 1]'hi1))
    (hi2 : index.toNat + 2 < v.val.size)
    (h_cont2 : IsContByte (v.val[index.toNat + 2]'hi2))
    (hi3 : index.toNat + 3 < v.val.size)
    (h_cont3 : IsContByte (v.val[index.toNat + 3]'hi3))
    (h_K_ge : index.toNat + 4 ≤ K) (hK_le : K ≤ v.val.size)
    (h : isValidUtf8From (v.val.take K) (index.toNat + 4) = true) :
    isValidUtf8From (v.val.take K) index.toNat = true := by
  have h_take_size : (v.val.take K).size = K := array_take_size_le v.val K hK_le
  have hi_lt_take : index.toNat < (v.val.take K).size := by rw [h_take_size]; omega
  have hi1_lt_take : index.toNat + 1 < (v.val.take K).size := by rw [h_take_size]; omega
  have hi2_lt_take : index.toNat + 2 < (v.val.take K).size := by rw [h_take_size]; omega
  have hi3_lt_take : index.toNat + 3 < (v.val.take K).size := by rw [h_take_size]; omega
  have h_take_get0 :
      (v.val.take K)[index.toNat]'hi_lt_take = v.val[index.toNat]'hi :=
    array_take_getElem v.val K index.toNat (by omega) hK_le
  have h_take_get1 :
      (v.val.take K)[index.toNat + 1]'hi1_lt_take = v.val[index.toNat + 1]'hi1 :=
    array_take_getElem v.val K (index.toNat + 1) (by omega) hK_le
  have h_take_get2 :
      (v.val.take K)[index.toNat + 2]'hi2_lt_take = v.val[index.toNat + 2]'hi2 :=
    array_take_getElem v.val K (index.toNat + 2) (by omega) hK_le
  have h_take_get3 :
      (v.val.take K)[index.toNat + 3]'hi3_lt_take = v.val[index.toNat + 3]'hi3 :=
    array_take_getElem v.val K (index.toNat + 3) (by omega) hK_le
  have h_lw : leadWidth ((v.val.take K)[index.toNat]'hi_lt_take) = 4 := by
    rw [h_take_get0]; unfold leadWidth
    rw [if_neg (by omega : ¬ (v.val[index.toNat]'hi).toNat < 128)]
    rw [if_neg (by omega : ¬ (v.val[index.toNat]'hi).toNat < 194)]
    rw [if_neg (by omega : ¬ (v.val[index.toNat]'hi).toNat < 224)]
    rw [if_neg (by omega : ¬ (v.val[index.toNat]'hi).toNat < 240)]
    rw [if_pos h_hi]
  have h_sbo_take :
      SecondByteOk ((v.val.take K)[index.toNat]'hi_lt_take)
                   ((v.val.take K)[index.toNat + 1]'hi1_lt_take) := by
    rw [h_take_get0, h_take_get1]; exact h_sbo
  have h_cont2_take : IsContByte ((v.val.take K)[index.toNat + 2]'hi2_lt_take) := by
    rw [h_take_get2]; exact h_cont2
  have h_cont3_take : IsContByte ((v.val.take K)[index.toNat + 3]'hi3_lt_take) := by
    rw [h_take_get3]; exact h_cont3
  rw [isValidUtf8From_w4_ok _ _ hi_lt_take h_lw hi1_lt_take h_sbo_take
        hi2_lt_take h_cont2_take hi3_lt_take h_cont3_take]
  exact h

/-! ### isValidUtf8From at `(v.val.take m) k` with `m = k` returns true (base). -/

private theorem prefix_at_self (bs : Array u8) (m : Nat) (h : m ≤ bs.size) :
    isValidUtf8From (bs.take m) m = true :=
  isValidUtf8From_oob (bs.take m) m (by rw [array_take_size_le bs m h]; exact Nat.le_refl _)

/-! ### Width-3 leaf step lemmas. -/

/-- Width-3 truncation at i1: i1 ≥ size ⇒ Err None. -/
private theorem validate_at_w3_trunc1 (v : RustSlice u8) (index : usize)
    (hi : index.toNat < v.val.size)
    (h_lo : 224 ≤ (v.val[index.toNat]'hi).toNat)
    (h_hi : (v.val[index.toNat]'hi).toNat < 240)
    (h_trunc : v.val.size ≤ index.toNat + 1) :
    run_utf8_validation_u8.validate_at v index =
      RustM.ok (core_models.result.Result.Err
        (run_utf8_validation_u8.Utf8Error.mk
          (valid_up_to := index)
          (error_len := core_models.option.Option.None))) := by
  rw [validate_at_w3_unfold v index hi h_lo h_hi]
  have h_size_lt : v.val.size < 2^64 := v.size_lt_usizeSize
  have h_no_ov : index.toNat + 1 < 2^64 := by omega
  have h_add := usize_add_one_ok index h_no_ov
  have h_i1_toNat : (index + 1).toNat = index.toNat + 1 := usize_add_one_toNat _ h_no_ov
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat v.val.size ≤ index + 1) = true := by
    rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat, h_i1_toNat]
    omega
  simp only [h_add, RustM_ok_bind, rust_primitives.cmp.ge, pure_bind, h_cond, ↓reduceIte]
  rfl

/-- `ok2`-evaluation helper for the width-3 path.
    Given `224 ≤ first.toNat < 240`, the do-block computing `ok2` reduces to
    `RustM.ok (decide (SecondByteOk first b2))`. -/
private theorem w3_ok2_eq (first b2 : u8)
    (h_lo : 224 ≤ first.toNat) (h_hi : first.toNat < 240) :
    ((do
      if (← (first ==? (224 : u8))) then
        ((← (b2 >=? (160 : u8))) &&? (← (b2 <=? (191 : u8))))
      else
        if (← ((← (first >=? (225 : u8))) &&? (← (first <=? (236 : u8))))) then
          ((← (b2 >=? (128 : u8))) &&? (← (b2 <=? (191 : u8))))
        else
          if (← (first ==? (237 : u8))) then
            ((← (b2 >=? (128 : u8))) &&? (← (b2 <=? (159 : u8))))
          else
            if (← ((← (first >=? (238 : u8))) &&? (← (first <=? (239 : u8))))) then
              ((← (b2 >=? (128 : u8))) &&? (← (b2 <=? (191 : u8))))
            else
              (pure false)) : RustM Bool) =
      RustM.ok (decide (SecondByteOk first b2)) := by
  -- Rewrite `decide (SecondByteOk …)` using the explicit form via `decide_eq_decide.mpr`.
  rw [show decide (SecondByteOk first b2) =
       decide ((first = (0xE0 : u8) ∧ b2.toNat ≥ 0xA0 ∧ b2.toNat ≤ 0xBF) ∨
               (0xE1 ≤ first.toNat ∧ first.toNat ≤ 0xEC ∧ b2.toNat ≥ 0x80 ∧ b2.toNat ≤ 0xBF) ∨
               (first = (0xED : u8) ∧ b2.toNat ≥ 0x80 ∧ b2.toNat ≤ 0x9F) ∨
               (0xEE ≤ first.toNat ∧ first.toNat ≤ 0xEF ∧ b2.toNat ≥ 0x80 ∧ b2.toNat ≤ 0xBF)) from
       decide_eq_decide.mpr (secondByteOk_w3_explicit first b2 h_lo h_hi)]
  simp only [rust_primitives.cmp.eq, rust_primitives.cmp.ge, rust_primitives.cmp.le,
             rust_primitives.hax.logical_op.and, pure_bind]
  -- Case-split on first.toNat values.
  by_cases h_E0 : first.toNat = 224
  · -- first = 0xE0
    have h_first : first = (224 : u8) :=
      UInt8.toNat_inj.mp (h_E0.trans u8_224_toNat.symm)
    subst h_first
    have h_beq : ((224 : u8) == (224 : u8)) = true := by decide
    simp only [h_beq, if_true]
    -- LHS: pure (decide (b2 ≥ 160) && decide (b2 ≤ 191))
    -- RHS: decide ((224 = 0xE0 ∧ ...) ∨ ...)
    have h_b2_lo : ((160 : u8) ≤ b2) ↔ (160 ≤ b2.toNat) := by
      rw [UInt8.le_iff_toNat_le, u8_160_toNat]
    have h_b2_hi : (b2 ≤ (191 : u8)) ↔ (b2.toNat ≤ 191) := by
      rw [UInt8.le_iff_toNat_le, u8_191_toNat]
    have h_and_decide :
        (decide (160 ≤ b2.toNat) && decide (b2.toNat ≤ 191)) =
        decide (160 ≤ b2.toNat ∧ b2.toNat ≤ 191) := by
      by_cases ha : 160 ≤ b2.toNat <;> by_cases hb : b2.toNat ≤ 191 <;>
        simp [ha, hb, decide_eq_true, decide_eq_false]
    rw [decide_eq_decide.mpr h_b2_lo, decide_eq_decide.mpr h_b2_hi, h_and_decide]
    show RustM.ok (decide _) = RustM.ok (decide _)
    congr 1
    apply decide_eq_decide.mpr
    constructor
    · intro ⟨ha, hb⟩; exact Or.inl ⟨trivial, ha, hb⟩
    · intro h
      rcases h with ⟨_, ha, hb⟩ | ⟨h1, _, _, _⟩ | ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩
      · exact ⟨ha, hb⟩
      · exfalso; rw [u8_224_toNat] at h1; omega
      · exfalso; have : ((224 : u8) : u8).toNat = (0xED : u8).toNat := by rw [hf]
        rw [u8_224_toNat, u8_237_toNat] at this; omega
      · exfalso; rw [u8_224_toNat] at h1; omega
  · have h_beq_false : (first == (224 : u8)) = false := by
      rw [beq_eq_false_iff_ne]; intro h; apply h_E0
      rw [h]; exact u8_224_toNat
    simp only [h_beq_false, Bool.false_eq_true, if_false, ↓reduceIte]
    by_cases h_E1_EC : 225 ≤ first.toNat ∧ first.toNat ≤ 236
    · obtain ⟨h1, h2⟩ := h_E1_EC
      have h_ge_225 : decide ((225 : u8) ≤ first) = true := by
        rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_225_toNat]; exact h1
      have h_le_236 : decide (first ≤ (236 : u8)) = true := by
        rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_236_toNat]; exact h2
      simp only [h_ge_225, h_le_236, show ((true : Bool) && true) = true from rfl, if_true]
      have h_b2_lo : ((128 : u8) ≤ b2) ↔ (128 ≤ b2.toNat) := by
        rw [UInt8.le_iff_toNat_le, u8_128_toNat]
      have h_b2_hi : (b2 ≤ (191 : u8)) ↔ (b2.toNat ≤ 191) := by
        rw [UInt8.le_iff_toNat_le, u8_191_toNat]
      have h_and_decide :
          (decide (128 ≤ b2.toNat) && decide (b2.toNat ≤ 191)) =
          decide (128 ≤ b2.toNat ∧ b2.toNat ≤ 191) := by
        by_cases ha : 128 ≤ b2.toNat <;> by_cases hb : b2.toNat ≤ 191 <;>
          simp [ha, hb, decide_eq_true, decide_eq_false]
      rw [decide_eq_decide.mpr h_b2_lo, decide_eq_decide.mpr h_b2_hi, h_and_decide]
      show RustM.ok (decide _) = RustM.ok (decide _)
      congr 1
      apply decide_eq_decide.mpr
      constructor
      · intro ⟨ha, hb⟩; exact Or.inr (Or.inl ⟨h1, h2, ha, hb⟩)
      · intro h
        rcases h with ⟨hf, _, _⟩ | ⟨_, _, ha, hb⟩ | ⟨hf, _, _⟩ | ⟨hf1, _, _, _⟩
        · exfalso; have : first.toNat = (0xE0 : u8).toNat := by rw [hf]
          rw [u8_E0_toNat] at this; omega
        · exact ⟨ha, hb⟩
        · exfalso; have : first.toNat = (0xED : u8).toNat := by rw [hf]
          rw [u8_237_toNat] at this; omega
        · exfalso; omega
    · have h_chain_false :
          (decide ((225 : u8) ≤ first) && decide (first ≤ (236 : u8))) = false := by
        rw [Bool.and_eq_false_iff]
        rcases Classical.em (225 ≤ first.toNat) with ha | ha
        · right
          rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, u8_236_toNat]
          intro hb; exact h_E1_EC ⟨ha, hb⟩
        · left
          rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, u8_225_toNat]
          exact ha
      simp only [h_chain_false, Bool.false_eq_true, if_false, ↓reduceIte]
      by_cases h_ED : first.toNat = 237
      · have h_first : first = (237 : u8) :=
          UInt8.toNat_inj.mp (h_ED.trans u8_237_toNat.symm)
        subst h_first
        have h_beq : ((237 : u8) == (237 : u8)) = true := by decide
        simp only [h_beq, if_true]
        have h_b2_lo : ((128 : u8) ≤ b2) ↔ (128 ≤ b2.toNat) := by
          rw [UInt8.le_iff_toNat_le, u8_128_toNat]
        have h_b2_hi : (b2 ≤ (159 : u8)) ↔ (b2.toNat ≤ 159) := by
          rw [UInt8.le_iff_toNat_le, u8_159_toNat]
        have h_and_decide :
            (decide (128 ≤ b2.toNat) && decide (b2.toNat ≤ 159)) =
            decide (128 ≤ b2.toNat ∧ b2.toNat ≤ 159) := by
          by_cases ha : 128 ≤ b2.toNat <;> by_cases hb : b2.toNat ≤ 159 <;>
            simp [ha, hb, decide_eq_true, decide_eq_false]
        rw [decide_eq_decide.mpr h_b2_lo, decide_eq_decide.mpr h_b2_hi, h_and_decide]
        show RustM.ok (decide _) = RustM.ok (decide _)
        congr 1
        apply decide_eq_decide.mpr
        constructor
        · intro ⟨ha, hb⟩; exact Or.inr (Or.inr (Or.inl ⟨trivial, ha, hb⟩))
        · intro h
          rcases h with ⟨hf, _, _⟩ | ⟨h1, h2, _, _⟩ | ⟨_, ha, hb⟩ | ⟨h1, h2, _, _⟩
          · exfalso; have : ((237 : u8) : u8).toNat = (0xE0 : u8).toNat := by rw [hf]
            rw [u8_237_toNat, u8_E0_toNat] at this; omega
          · exfalso; rw [u8_237_toNat] at h1 h2; omega
          · exact ⟨ha, hb⟩
          · exfalso; rw [u8_237_toNat] at h1 h2; omega
      · have h_beq_237_false : (first == (237 : u8)) = false := by
          rw [beq_eq_false_iff_ne]; intro h; apply h_ED
          rw [h]; exact u8_237_toNat
        simp only [h_beq_237_false, Bool.false_eq_true, if_false, ↓reduceIte]
        have h_EE_EF : 238 ≤ first.toNat ∧ first.toNat ≤ 239 := by
          refine ⟨?_, by omega⟩
          rcases Nat.lt_or_ge first.toNat 238 with h_lt | h_ge
          · exfalso
            rcases Nat.lt_or_ge first.toNat 225 with h_lt' | h_ge'
            · apply h_E0; omega
            · rcases Nat.lt_or_ge first.toNat 237 with h_lt'' | h_ge''
              · apply h_E1_EC; exact ⟨h_ge', by omega⟩
              · apply h_ED; omega
          · exact h_ge
        obtain ⟨h1, h2⟩ := h_EE_EF
        have h_ge_238 : decide ((238 : u8) ≤ first) = true := by
          rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_238_toNat]; exact h1
        have h_le_239 : decide (first ≤ (239 : u8)) = true := by
          rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_239_toNat]; exact h2
        simp only [h_ge_238, h_le_239, show ((true : Bool) && true) = true from rfl, if_true]
        have h_b2_lo : ((128 : u8) ≤ b2) ↔ (128 ≤ b2.toNat) := by
          rw [UInt8.le_iff_toNat_le, u8_128_toNat]
        have h_b2_hi : (b2 ≤ (191 : u8)) ↔ (b2.toNat ≤ 191) := by
          rw [UInt8.le_iff_toNat_le, u8_191_toNat]
        have h_and_decide :
            (decide (128 ≤ b2.toNat) && decide (b2.toNat ≤ 191)) =
            decide (128 ≤ b2.toNat ∧ b2.toNat ≤ 191) := by
          by_cases ha : 128 ≤ b2.toNat <;> by_cases hb : b2.toNat ≤ 191 <;>
            simp [ha, hb, decide_eq_true, decide_eq_false]
        rw [decide_eq_decide.mpr h_b2_lo, decide_eq_decide.mpr h_b2_hi, h_and_decide]
        show RustM.ok (decide _) = RustM.ok (decide _)
        congr 1
        apply decide_eq_decide.mpr
        constructor
        · intro ⟨ha, hb⟩; exact Or.inr (Or.inr (Or.inr ⟨h1, h2, ha, hb⟩))
        · intro h
          rcases h with ⟨hf, _, _⟩ | ⟨hf1, hf2, _, _⟩ | ⟨hf, _, _⟩ | ⟨_, _, ha, hb⟩
          · exfalso; have : first.toNat = (0xE0 : u8).toNat := by rw [hf]
            rw [u8_E0_toNat] at this; omega
          · exfalso; omega
          · exfalso; have : first.toNat = (0xED : u8).toNat := by rw [hf]
            rw [u8_237_toNat] at this; omega
          · exact ⟨ha, hb⟩

/-! ### Width-3 leaf step lemmas (continued). -/

/-- Width-3 evaluator. Combines all w3 cases into one computational form,
    using massive case-splits on the first byte's value. -/
private theorem validate_at_w3_bad_b2 (v : RustSlice u8) (index : usize)
    (hi : index.toNat < v.val.size)
    (h_lo : 224 ≤ (v.val[index.toNat]'hi).toNat)
    (h_hi : (v.val[index.toNat]'hi).toNat < 240)
    (hi1 : index.toNat + 1 < v.val.size)
    (h_bad : ¬ SecondByteOk (v.val[index.toNat]'hi) (v.val[index.toNat + 1]'hi1)) :
    run_utf8_validation_u8.validate_at v index =
      RustM.ok (core_models.result.Result.Err
        (run_utf8_validation_u8.Utf8Error.mk
          (valid_up_to := index)
          (error_len := core_models.option.Option.Some (1 : u8)))) := by
  rw [validate_at_w3_unfold v index hi h_lo h_hi]
  have h_size_lt : v.val.size < 2^64 := v.size_lt_usizeSize
  have h_no_ov : index.toNat + 1 < 2^64 := by omega
  have h_add := usize_add_one_ok index h_no_ov
  have h_i1_toNat : (index + 1).toNat = index.toNat + 1 := usize_add_one_toNat _ h_no_ov
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat v.val.size ≤ index + 1) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat, h_i1_toNat]
    omega
  have hi1_take : (index + 1).toNat < v.val.size := by rw [h_i1_toNat]; exact hi1
  have h_idx : (v[index + 1]_? : RustM u8) = RustM.ok (v.val[(index + 1).toNat]'hi1_take) :=
    getElem_ok v (index + 1) hi1_take
  have h_eq_get : v.val[(index + 1).toNat]'hi1_take = v.val[index.toNat + 1]'hi1 := by
    congr 1
  have h_cond_ge : decide (index + 1 ≥ USize64.ofNat v.val.size) = false := h_cond
  -- Apply h_eq_get to translate h_bad
  have h_bad' : ¬ SecondByteOk (v.val[index.toNat]'hi) (v.val[(index + 1).toNat]'hi1_take) := by
    rw [h_eq_get]; exact h_bad
  -- Reduce ALL rust comparisons to pure decide-form. Then the inner chain is pure Bool.
  simp only [h_add, RustM_ok_bind, ↓reduceIte, h_idx,
             rust_primitives.cmp.eq, rust_primitives.cmp.ge, rust_primitives.cmp.le,
             rust_primitives.cmp.ne, rust_primitives.hax.logical_op.and,
             rust_primitives.hax.logical_op.not, pure_bind,
             h_cond_ge, Bool.false_eq_true]
  -- Common helper for computing `decide (lo ≤ b) && decide (b ≤ hi) = false` from a range exclusion.
  have b2_and_false : ∀ (lo hi : u8) (lo_nat hi_nat : Nat),
      lo.toNat = lo_nat → hi.toNat = hi_nat →
      ¬ (lo_nat ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
         (v.val[(index + 1).toNat]'hi1_take).toNat ≤ hi_nat) →
      (decide (lo ≤ (v.val[(index + 1).toNat]'hi1_take)) &&
       decide ((v.val[(index + 1).toNat]'hi1_take) ≤ hi)) = false := by
    intro lo hi lo_nat hi_nat h_lo_n h_hi_n h_not
    rw [Bool.and_eq_false_iff]
    rcases Classical.em (lo_nat ≤ (v.val[(index + 1).toNat]'hi1_take).toNat) with ha | ha
    · right
      rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, h_hi_n]
      intro hb; exact h_not ⟨ha, hb⟩
    · left
      rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, h_lo_n]
      exact ha
  -- Now the goal is entirely in pure Bool/Result form. Case-split on first byte.
  by_cases h_E0 : (v.val[index.toNat]'hi).toNat = 224
  · -- first = 0xE0
    have h_first_eq : (v.val[index.toNat]'hi) = (224 : u8) :=
      UInt8.toNat_inj.mp (h_E0.trans u8_224_toNat.symm)
    have h_beq : ((v.val[index.toNat]'hi) == (224 : u8)) = true := by
      rw [beq_iff_eq]; exact h_first_eq
    have h_not_range : ¬ (160 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                         (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 191) := by
      intro ⟨ha, hb⟩
      apply h_bad'; unfold SecondByteOk; left
      exact ⟨h_E0, ha, hb⟩
    have h_and_false := b2_and_false (160 : u8) (191 : u8) 160 191 u8_160_toNat u8_191_toNat h_not_range
    simp only [h_beq, ↓reduceIte, h_and_false, Bool.not_false]
    rfl
  · have h_beq_E0_false : ((v.val[index.toNat]'hi) == (224 : u8)) = false := by
      rw [beq_eq_false_iff_ne]; intro h; apply h_E0; rw [h]; exact u8_224_toNat
    by_cases h_E1_EC : 225 ≤ (v.val[index.toNat]'hi).toNat ∧ (v.val[index.toNat]'hi).toNat ≤ 236
    · obtain ⟨h1, h2⟩ := h_E1_EC
      have h_ge_225 : decide ((225 : u8) ≤ (v.val[index.toNat]'hi)) = true := by
        rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_225_toNat]; exact h1
      have h_le_236 : decide ((v.val[index.toNat]'hi) ≤ (236 : u8)) = true := by
        rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_236_toNat]; exact h2
      have h_outer_and_true : (decide ((225 : u8) ≤ (v.val[index.toNat]'hi))
          && decide ((v.val[index.toNat]'hi) ≤ (236 : u8))) = true := by
        rw [h_ge_225, h_le_236]; rfl
      have h_not_range : ¬ (128 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                           (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 191) := by
        intro ⟨ha, hb⟩
        apply h_bad'; unfold SecondByteOk; right; left
        exact ⟨h1, h2, ha, hb⟩
      have h_and_false := b2_and_false (128 : u8) (191 : u8) 128 191 u8_128_toNat u8_191_toNat h_not_range
      simp only [h_beq_E0_false, Bool.false_eq_true, ↓reduceIte,
                 h_outer_and_true, h_and_false, Bool.not_false]
      rfl
    · have h_chain_false :
          (decide ((225 : u8) ≤ (v.val[index.toNat]'hi))
          && decide ((v.val[index.toNat]'hi) ≤ (236 : u8))) = false := by
        rw [Bool.and_eq_false_iff]
        rcases Classical.em (225 ≤ (v.val[index.toNat]'hi).toNat) with ha | ha
        · right; rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, u8_236_toNat]
          intro hb; exact h_E1_EC ⟨ha, hb⟩
        · left; rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, u8_225_toNat]; exact ha
      by_cases h_ED : (v.val[index.toNat]'hi).toNat = 237
      · have h_first_eq : (v.val[index.toNat]'hi) = (237 : u8) :=
          UInt8.toNat_inj.mp (h_ED.trans u8_237_toNat.symm)
        have h_beq_ED : ((v.val[index.toNat]'hi) == (237 : u8)) = true := by
          rw [beq_iff_eq]; exact h_first_eq
        have h_not_range : ¬ (128 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                             (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 159) := by
          intro ⟨ha, hb⟩
          apply h_bad'; unfold SecondByteOk; right; right; left
          exact ⟨h_ED, ha, hb⟩
        have h_and_false := b2_and_false (128 : u8) (159 : u8) 128 159 u8_128_toNat u8_159_toNat h_not_range
        simp only [h_beq_E0_false, Bool.false_eq_true, ↓reduceIte, h_chain_false,
                   h_beq_ED, h_and_false, Bool.not_false]
        rfl
      · have h_beq_ED_false : ((v.val[index.toNat]'hi) == (237 : u8)) = false := by
          rw [beq_eq_false_iff_ne]; intro h; apply h_ED; rw [h]; exact u8_237_toNat
        have h_EE_EF : 238 ≤ (v.val[index.toNat]'hi).toNat ∧ (v.val[index.toNat]'hi).toNat ≤ 239 := by
          refine ⟨?_, by omega⟩
          rcases Nat.lt_or_ge (v.val[index.toNat]'hi).toNat 238 with h_lt | h_ge
          · exfalso
            rcases Nat.lt_or_ge (v.val[index.toNat]'hi).toNat 225 with h_lt' | h_ge'
            · apply h_E0; omega
            · rcases Nat.lt_or_ge (v.val[index.toNat]'hi).toNat 237 with h_lt'' | h_ge''
              · apply h_E1_EC; exact ⟨h_ge', by omega⟩
              · apply h_ED; omega
          · exact h_ge
        obtain ⟨h1', h2'⟩ := h_EE_EF
        have h_ge_238 : decide ((238 : u8) ≤ (v.val[index.toNat]'hi)) = true := by
          rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_238_toNat]; exact h1'
        have h_le_239 : decide ((v.val[index.toNat]'hi) ≤ (239 : u8)) = true := by
          rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_239_toNat]; exact h2'
        have h_outer_EE_and : (decide ((238 : u8) ≤ (v.val[index.toNat]'hi))
            && decide ((v.val[index.toNat]'hi) ≤ (239 : u8))) = true := by
          rw [h_ge_238, h_le_239]; rfl
        have h_not_range : ¬ (128 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                             (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 191) := by
          intro ⟨ha, hb⟩
          apply h_bad'; unfold SecondByteOk; right; right; right; left
          exact ⟨h1', h2', ha, hb⟩
        have h_and_false := b2_and_false (128 : u8) (191 : u8) 128 191 u8_128_toNat u8_191_toNat h_not_range
        simp only [h_beq_E0_false, Bool.false_eq_true, ↓reduceIte, h_chain_false,
                   h_beq_ED_false, h_outer_EE_and, h_and_false, Bool.not_false]
        rfl

/-- Width-3 truncation at i2: i1 < size, SecondByteOk holds, i2 ≥ size ⇒ Err None. -/
private theorem validate_at_w3_trunc2 (v : RustSlice u8) (index : usize)
    (hi : index.toNat < v.val.size)
    (h_lo : 224 ≤ (v.val[index.toNat]'hi).toNat)
    (h_hi : (v.val[index.toNat]'hi).toNat < 240)
    (hi1 : index.toNat + 1 < v.val.size)
    (h_sbo : SecondByteOk (v.val[index.toNat]'hi) (v.val[index.toNat + 1]'hi1))
    (h_trunc : v.val.size ≤ index.toNat + 2) :
    run_utf8_validation_u8.validate_at v index =
      RustM.ok (core_models.result.Result.Err
        (run_utf8_validation_u8.Utf8Error.mk
          (valid_up_to := index)
          (error_len := core_models.option.Option.None))) := by
  rw [validate_at_w3_unfold v index hi h_lo h_hi]
  have h_size_lt : v.val.size < 2^64 := v.size_lt_usizeSize
  have h_no_ov : index.toNat + 1 < 2^64 := by omega
  have h_no_ov_i2 : index.toNat + 2 < 2^64 := by omega
  have h_add := usize_add_one_ok index h_no_ov
  have h_i1_toNat : (index + 1).toNat = index.toNat + 1 := usize_add_one_toNat _ h_no_ov
  have h_add_i2 := usize_add_one_ok (index + 1) (by rw [h_i1_toNat]; omega)
  have h_i2_toNat : (index + 1 + 1).toNat = index.toNat + 2 := by
    rw [usize_add_one_toNat (index + 1) (by rw [h_i1_toNat]; omega), h_i1_toNat]
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat v.val.size ≤ index + 1) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat, h_i1_toNat]; omega
  have h_cond_ge : decide (index + 1 ≥ USize64.ofNat v.val.size) = false := h_cond
  have h_cond_i2 : decide (USize64.ofNat v.val.size ≤ index + 1 + 1) = true := by
    rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat, h_i2_toNat]; exact h_trunc
  have h_cond_i2_ge : decide (index + 1 + 1 ≥ USize64.ofNat v.val.size) = true := h_cond_i2
  have hi1_take : (index + 1).toNat < v.val.size := by rw [h_i1_toNat]; exact hi1
  have h_idx : (v[index + 1]_? : RustM u8) = RustM.ok (v.val[(index + 1).toNat]'hi1_take) :=
    getElem_ok v (index + 1) hi1_take
  have h_eq_get : v.val[(index + 1).toNat]'hi1_take = v.val[index.toNat + 1]'hi1 := by
    congr 1
  have h_sbo' : SecondByteOk (v.val[index.toNat]'hi) (v.val[(index + 1).toNat]'hi1_take) := by
    rw [h_eq_get]; exact h_sbo
  simp only [h_add, RustM_ok_bind, ↓reduceIte, h_idx,
             rust_primitives.cmp.eq, rust_primitives.cmp.ge, rust_primitives.cmp.le,
             rust_primitives.cmp.ne, rust_primitives.hax.logical_op.and,
             rust_primitives.hax.logical_op.not, pure_bind,
             h_cond_ge, Bool.false_eq_true]
  -- Helper: from b2 range, prove (decide (lo ≤ b2) && decide (b2 ≤ hi)) = true.
  have b2_and_true : ∀ (lo hi : u8) (lo_nat hi_nat : Nat),
      lo.toNat = lo_nat → hi.toNat = hi_nat →
      lo_nat ≤ (v.val[(index + 1).toNat]'hi1_take).toNat →
      (v.val[(index + 1).toNat]'hi1_take).toNat ≤ hi_nat →
      (decide (lo ≤ (v.val[(index + 1).toNat]'hi1_take)) &&
       decide ((v.val[(index + 1).toNat]'hi1_take) ≤ hi)) = true := by
    intro lo hi lo_nat hi_nat h_lo_n h_hi_n h_ge_lo h_le_hi
    have h_d1 : decide (lo ≤ (v.val[(index + 1).toNat]'hi1_take)) = true := by
      rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, h_lo_n]; exact h_ge_lo
    have h_d2 : decide ((v.val[(index + 1).toNat]'hi1_take) ≤ hi) = true := by
      rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, h_hi_n]; exact h_le_hi
    rw [h_d1, h_d2]; rfl
  -- Case-split on first byte to identify the SecondByteOk disjunct
  by_cases h_E0 : (v.val[index.toNat]'hi).toNat = 224
  · have h_first_eq : (v.val[index.toNat]'hi) = (224 : u8) :=
      UInt8.toNat_inj.mp (h_E0.trans u8_224_toNat.symm)
    have h_beq : ((v.val[index.toNat]'hi) == (224 : u8)) = true := by
      rw [beq_iff_eq]; exact h_first_eq
    have h_b2_range : 160 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                      (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 191 := by
      rcases h_sbo' with ⟨_, ha, hb⟩ | ⟨h1, _, _, _⟩ | ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩
                       | ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩ | ⟨hf, _, _⟩
      · exact ⟨ha, hb⟩
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
    have h_and_true := b2_and_true (160 : u8) (191 : u8) 160 191 u8_160_toNat u8_191_toNat
                                    h_b2_range.1 h_b2_range.2
    simp only [h_beq, ↓reduceIte, h_and_true, Bool.not_true, Bool.false_eq_true,
               h_add_i2, RustM_ok_bind, h_cond_i2_ge]
    rfl
  · have h_beq_E0_false : ((v.val[index.toNat]'hi) == (224 : u8)) = false := by
      rw [beq_eq_false_iff_ne]; intro h; apply h_E0; rw [h]; exact u8_224_toNat
    by_cases h_E1_EC : 225 ≤ (v.val[index.toNat]'hi).toNat ∧ (v.val[index.toNat]'hi).toNat ≤ 236
    · obtain ⟨h1, h2⟩ := h_E1_EC
      have h_ge_225 : decide ((225 : u8) ≤ (v.val[index.toNat]'hi)) = true := by
        rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_225_toNat]; exact h1
      have h_le_236 : decide ((v.val[index.toNat]'hi) ≤ (236 : u8)) = true := by
        rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_236_toNat]; exact h2
      have h_outer_and_true : (decide ((225 : u8) ≤ (v.val[index.toNat]'hi))
          && decide ((v.val[index.toNat]'hi) ≤ (236 : u8))) = true := by
        rw [h_ge_225, h_le_236]; rfl
      have h_b2_range : 128 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                        (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 191 := by
        rcases h_sbo' with ⟨hf, _, _⟩ | ⟨_, _, ha, hb⟩ | ⟨hf, _, _⟩ | ⟨h1', _, _, _⟩
                         | ⟨hf, _, _⟩ | ⟨h1', _, _, _⟩ | ⟨hf, _, _⟩
        · exfalso; omega
        · exact ⟨ha, hb⟩
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
      have h_and_true := b2_and_true (128 : u8) (191 : u8) 128 191 u8_128_toNat u8_191_toNat
                                      h_b2_range.1 h_b2_range.2
      simp only [h_beq_E0_false, Bool.false_eq_true, ↓reduceIte,
                 h_outer_and_true, h_and_true, Bool.not_true,
                 h_add_i2, RustM_ok_bind, h_cond_i2_ge]
      rfl
    · have h_chain_false :
          (decide ((225 : u8) ≤ (v.val[index.toNat]'hi))
          && decide ((v.val[index.toNat]'hi) ≤ (236 : u8))) = false := by
        rw [Bool.and_eq_false_iff]
        rcases Classical.em (225 ≤ (v.val[index.toNat]'hi).toNat) with ha | ha
        · right; rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, u8_236_toNat]
          intro hb; exact h_E1_EC ⟨ha, hb⟩
        · left; rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, u8_225_toNat]; exact ha
      by_cases h_ED : (v.val[index.toNat]'hi).toNat = 237
      · have h_first_eq : (v.val[index.toNat]'hi) = (237 : u8) :=
          UInt8.toNat_inj.mp (h_ED.trans u8_237_toNat.symm)
        have h_beq_ED : ((v.val[index.toNat]'hi) == (237 : u8)) = true := by
          rw [beq_iff_eq]; exact h_first_eq
        have h_b2_range : 128 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                          (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 159 := by
          rcases h_sbo' with ⟨hf, _, _⟩ | ⟨h1, h2, _, _⟩ | ⟨_, ha, hb⟩ | ⟨h1, h2, _, _⟩
                           | ⟨hf, _, _⟩ | ⟨h1, h2, _, _⟩ | ⟨hf, _, _⟩
          · exfalso; omega
          · exfalso; omega
          · exact ⟨ha, hb⟩
          · exfalso; omega
          · exfalso; omega
          · exfalso; omega
          · exfalso; omega
        have h_and_true := b2_and_true (128 : u8) (159 : u8) 128 159 u8_128_toNat u8_159_toNat
                                        h_b2_range.1 h_b2_range.2
        simp only [h_beq_E0_false, Bool.false_eq_true, ↓reduceIte, h_chain_false,
                   h_beq_ED, h_and_true, Bool.not_true,
                   h_add_i2, RustM_ok_bind, h_cond_i2_ge]
        rfl
      · have h_beq_ED_false : ((v.val[index.toNat]'hi) == (237 : u8)) = false := by
          rw [beq_eq_false_iff_ne]; intro h; apply h_ED; rw [h]; exact u8_237_toNat
        have h_EE_EF : 238 ≤ (v.val[index.toNat]'hi).toNat ∧ (v.val[index.toNat]'hi).toNat ≤ 239 := by
          refine ⟨?_, by omega⟩
          rcases Nat.lt_or_ge (v.val[index.toNat]'hi).toNat 238 with h_lt | h_ge
          · exfalso
            rcases Nat.lt_or_ge (v.val[index.toNat]'hi).toNat 225 with h_lt' | h_ge'
            · apply h_E0; omega
            · rcases Nat.lt_or_ge (v.val[index.toNat]'hi).toNat 237 with h_lt'' | h_ge''
              · apply h_E1_EC; exact ⟨h_ge', by omega⟩
              · apply h_ED; omega
          · exact h_ge
        obtain ⟨h1', h2'⟩ := h_EE_EF
        have h_ge_238 : decide ((238 : u8) ≤ (v.val[index.toNat]'hi)) = true := by
          rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_238_toNat]; exact h1'
        have h_le_239 : decide ((v.val[index.toNat]'hi) ≤ (239 : u8)) = true := by
          rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_239_toNat]; exact h2'
        have h_outer_EE_and : (decide ((238 : u8) ≤ (v.val[index.toNat]'hi))
            && decide ((v.val[index.toNat]'hi) ≤ (239 : u8))) = true := by
          rw [h_ge_238, h_le_239]; rfl
        have h_b2_range : 128 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                          (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 191 := by
          rcases h_sbo' with ⟨hf, _, _⟩ | ⟨h1, h2, _, _⟩ | ⟨hf, _, _⟩ | ⟨_, _, ha, hb⟩
                           | ⟨hf, _, _⟩ | ⟨h1, h2, _, _⟩ | ⟨hf, _, _⟩
          · exfalso; omega
          · exfalso; omega
          · exfalso; omega
          · exact ⟨ha, hb⟩
          · exfalso; omega
          · exfalso; omega
          · exfalso; omega
        have h_and_true := b2_and_true (128 : u8) (191 : u8) 128 191 u8_128_toNat u8_191_toNat
                                        h_b2_range.1 h_b2_range.2
        simp only [h_beq_E0_false, Bool.false_eq_true, ↓reduceIte, h_chain_false,
                   h_beq_ED_false, h_outer_EE_and, h_and_true, Bool.not_true,
                   h_add_i2, RustM_ok_bind, h_cond_i2_ge]
        rfl

/-- Width-3 bad continuation byte: i1 < size, SecondByteOk, i2 < size, ¬IsContByte b3 ⇒ Err (Some 2). -/
private theorem validate_at_w3_bad_cont (v : RustSlice u8) (index : usize)
    (hi : index.toNat < v.val.size)
    (h_lo : 224 ≤ (v.val[index.toNat]'hi).toNat)
    (h_hi : (v.val[index.toNat]'hi).toNat < 240)
    (hi1 : index.toNat + 1 < v.val.size)
    (h_sbo : SecondByteOk (v.val[index.toNat]'hi) (v.val[index.toNat + 1]'hi1))
    (hi2 : index.toNat + 2 < v.val.size)
    (h_bad : ¬ IsContByte (v.val[index.toNat + 2]'hi2)) :
    run_utf8_validation_u8.validate_at v index =
      RustM.ok (core_models.result.Result.Err
        (run_utf8_validation_u8.Utf8Error.mk
          (valid_up_to := index)
          (error_len := core_models.option.Option.Some (2 : u8)))) := by
  rw [validate_at_w3_unfold v index hi h_lo h_hi]
  have h_size_lt : v.val.size < 2^64 := v.size_lt_usizeSize
  have h_no_ov : index.toNat + 1 < 2^64 := by omega
  have h_add := usize_add_one_ok index h_no_ov
  have h_i1_toNat : (index + 1).toNat = index.toNat + 1 := usize_add_one_toNat _ h_no_ov
  have h_add_i2 := usize_add_one_ok (index + 1) (by rw [h_i1_toNat]; omega)
  have h_i2_toNat : (index + 1 + 1).toNat = index.toNat + 2 := by
    rw [usize_add_one_toNat (index + 1) (by rw [h_i1_toNat]; omega), h_i1_toNat]
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat v.val.size ≤ index + 1) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat, h_i1_toNat]; omega
  have h_cond_ge : decide (index + 1 ≥ USize64.ofNat v.val.size) = false := h_cond
  have h_cond_i2 : decide (USize64.ofNat v.val.size ≤ index + 1 + 1) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat, h_i2_toNat]; omega
  have h_cond_i2_ge : decide (index + 1 + 1 ≥ USize64.ofNat v.val.size) = false := h_cond_i2
  have hi1_take : (index + 1).toNat < v.val.size := by rw [h_i1_toNat]; exact hi1
  have hi2_take : (index + 1 + 1).toNat < v.val.size := by rw [h_i2_toNat]; exact hi2
  have h_idx : (v[index + 1]_? : RustM u8) = RustM.ok (v.val[(index + 1).toNat]'hi1_take) :=
    getElem_ok v (index + 1) hi1_take
  have h_idx2 : (v[index + 1 + 1]_? : RustM u8) = RustM.ok (v.val[(index + 1 + 1).toNat]'hi2_take) :=
    getElem_ok v (index + 1 + 1) hi2_take
  have h_eq_get : v.val[(index + 1).toNat]'hi1_take = v.val[index.toNat + 1]'hi1 := by
    congr 1
  have h_eq_get2 : v.val[(index + 1 + 1).toNat]'hi2_take = v.val[index.toNat + 2]'hi2 := by
    congr 1
  have h_sbo' : SecondByteOk (v.val[index.toNat]'hi) (v.val[(index + 1).toNat]'hi1_take) := by
    rw [h_eq_get]; exact h_sbo
  have h_bad' : ¬ IsContByte (v.val[(index + 1 + 1).toNat]'hi2_take) := by
    rw [h_eq_get2]; exact h_bad
  -- Show (b3 &&& 192) != 128 = true
  have h_b3_bne : ((v.val[(index + 1 + 1).toNat]'hi2_take) &&& (192 : u8) != (128 : u8)) = true := by
    apply bne_iff_ne.mpr
    intro h_eq
    exact h_bad' ((cont_byte_iff _).mp h_eq)
  simp only [h_add, RustM_ok_bind, ↓reduceIte, h_idx,
             rust_primitives.cmp.eq, rust_primitives.cmp.ge, rust_primitives.cmp.le,
             rust_primitives.cmp.ne, rust_primitives.hax.logical_op.and,
             rust_primitives.hax.logical_op.not, pure_bind,
             h_cond_ge, Bool.false_eq_true]
  have b2_and_true : ∀ (lo hi : u8) (lo_nat hi_nat : Nat),
      lo.toNat = lo_nat → hi.toNat = hi_nat →
      lo_nat ≤ (v.val[(index + 1).toNat]'hi1_take).toNat →
      (v.val[(index + 1).toNat]'hi1_take).toNat ≤ hi_nat →
      (decide (lo ≤ (v.val[(index + 1).toNat]'hi1_take)) &&
       decide ((v.val[(index + 1).toNat]'hi1_take) ≤ hi)) = true := by
    intro lo hi lo_nat hi_nat h_lo_n h_hi_n h_ge_lo h_le_hi
    have h_d1 : decide (lo ≤ (v.val[(index + 1).toNat]'hi1_take)) = true := by
      rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, h_lo_n]; exact h_ge_lo
    have h_d2 : decide ((v.val[(index + 1).toNat]'hi1_take) ≤ hi) = true := by
      rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, h_hi_n]; exact h_le_hi
    rw [h_d1, h_d2]; rfl
  by_cases h_E0 : (v.val[index.toNat]'hi).toNat = 224
  · have h_first_eq : (v.val[index.toNat]'hi) = (224 : u8) :=
      UInt8.toNat_inj.mp (h_E0.trans u8_224_toNat.symm)
    have h_beq : ((v.val[index.toNat]'hi) == (224 : u8)) = true := by
      rw [beq_iff_eq]; exact h_first_eq
    have h_b2_range : 160 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                      (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 191 := by
      rcases h_sbo' with ⟨_, ha, hb⟩ | ⟨h1, _, _, _⟩ | ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩
                       | ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩ | ⟨hf, _, _⟩
      · exact ⟨ha, hb⟩
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
    have h_and_true := b2_and_true (160 : u8) (191 : u8) 160 191 u8_160_toNat u8_191_toNat
                                    h_b2_range.1 h_b2_range.2
    simp only [h_beq, ↓reduceIte, h_and_true, Bool.not_true, Bool.false_eq_true,
               h_add_i2, RustM_ok_bind, h_cond_i2_ge, ↓reduceIte, h_idx2, h_b3_bne]
    rfl
  · have h_beq_E0_false : ((v.val[index.toNat]'hi) == (224 : u8)) = false := by
      rw [beq_eq_false_iff_ne]; intro h; apply h_E0; rw [h]; exact u8_224_toNat
    by_cases h_E1_EC : 225 ≤ (v.val[index.toNat]'hi).toNat ∧ (v.val[index.toNat]'hi).toNat ≤ 236
    · obtain ⟨h1, h2⟩ := h_E1_EC
      have h_ge_225 : decide ((225 : u8) ≤ (v.val[index.toNat]'hi)) = true := by
        rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_225_toNat]; exact h1
      have h_le_236 : decide ((v.val[index.toNat]'hi) ≤ (236 : u8)) = true := by
        rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_236_toNat]; exact h2
      have h_outer_and_true : (decide ((225 : u8) ≤ (v.val[index.toNat]'hi))
          && decide ((v.val[index.toNat]'hi) ≤ (236 : u8))) = true := by
        rw [h_ge_225, h_le_236]; rfl
      have h_b2_range : 128 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                        (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 191 := by
        rcases h_sbo' with ⟨hf, _, _⟩ | ⟨_, _, ha, hb⟩ | ⟨hf, _, _⟩ | ⟨h1', _, _, _⟩
                         | ⟨hf, _, _⟩ | ⟨h1', _, _, _⟩ | ⟨hf, _, _⟩
        · exfalso; omega
        · exact ⟨ha, hb⟩
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
      have h_and_true := b2_and_true (128 : u8) (191 : u8) 128 191 u8_128_toNat u8_191_toNat
                                      h_b2_range.1 h_b2_range.2
      simp only [h_beq_E0_false, Bool.false_eq_true, ↓reduceIte,
                 h_outer_and_true, h_and_true, Bool.not_true,
                 h_add_i2, RustM_ok_bind, h_cond_i2_ge, h_idx2, h_b3_bne]
      rfl
    · have h_chain_false :
          (decide ((225 : u8) ≤ (v.val[index.toNat]'hi))
          && decide ((v.val[index.toNat]'hi) ≤ (236 : u8))) = false := by
        rw [Bool.and_eq_false_iff]
        rcases Classical.em (225 ≤ (v.val[index.toNat]'hi).toNat) with ha | ha
        · right; rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, u8_236_toNat]
          intro hb; exact h_E1_EC ⟨ha, hb⟩
        · left; rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, u8_225_toNat]; exact ha
      by_cases h_ED : (v.val[index.toNat]'hi).toNat = 237
      · have h_first_eq : (v.val[index.toNat]'hi) = (237 : u8) :=
          UInt8.toNat_inj.mp (h_ED.trans u8_237_toNat.symm)
        have h_beq_ED : ((v.val[index.toNat]'hi) == (237 : u8)) = true := by
          rw [beq_iff_eq]; exact h_first_eq
        have h_b2_range : 128 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                          (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 159 := by
          rcases h_sbo' with ⟨hf, _, _⟩ | ⟨h1, h2, _, _⟩ | ⟨_, ha, hb⟩ | ⟨h1, h2, _, _⟩
                           | ⟨hf, _, _⟩ | ⟨h1, h2, _, _⟩ | ⟨hf, _, _⟩
          · exfalso; omega
          · exfalso; omega
          · exact ⟨ha, hb⟩
          · exfalso; omega
          · exfalso; omega
          · exfalso; omega
          · exfalso; omega
        have h_and_true := b2_and_true (128 : u8) (159 : u8) 128 159 u8_128_toNat u8_159_toNat
                                        h_b2_range.1 h_b2_range.2
        simp only [h_beq_E0_false, Bool.false_eq_true, ↓reduceIte, h_chain_false,
                   h_beq_ED, h_and_true, Bool.not_true,
                   h_add_i2, RustM_ok_bind, h_cond_i2_ge, h_idx2, h_b3_bne]
        rfl
      · have h_beq_ED_false : ((v.val[index.toNat]'hi) == (237 : u8)) = false := by
          rw [beq_eq_false_iff_ne]; intro h; apply h_ED; rw [h]; exact u8_237_toNat
        have h_EE_EF : 238 ≤ (v.val[index.toNat]'hi).toNat ∧ (v.val[index.toNat]'hi).toNat ≤ 239 := by
          refine ⟨?_, by omega⟩
          rcases Nat.lt_or_ge (v.val[index.toNat]'hi).toNat 238 with h_lt | h_ge
          · exfalso
            rcases Nat.lt_or_ge (v.val[index.toNat]'hi).toNat 225 with h_lt' | h_ge'
            · apply h_E0; omega
            · rcases Nat.lt_or_ge (v.val[index.toNat]'hi).toNat 237 with h_lt'' | h_ge''
              · apply h_E1_EC; exact ⟨h_ge', by omega⟩
              · apply h_ED; omega
          · exact h_ge
        obtain ⟨h1', h2'⟩ := h_EE_EF
        have h_ge_238 : decide ((238 : u8) ≤ (v.val[index.toNat]'hi)) = true := by
          rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_238_toNat]; exact h1'
        have h_le_239 : decide ((v.val[index.toNat]'hi) ≤ (239 : u8)) = true := by
          rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_239_toNat]; exact h2'
        have h_outer_EE_and : (decide ((238 : u8) ≤ (v.val[index.toNat]'hi))
            && decide ((v.val[index.toNat]'hi) ≤ (239 : u8))) = true := by
          rw [h_ge_238, h_le_239]; rfl
        have h_b2_range : 128 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                          (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 191 := by
          rcases h_sbo' with ⟨hf, _, _⟩ | ⟨h1, h2, _, _⟩ | ⟨hf, _, _⟩ | ⟨_, _, ha, hb⟩
                           | ⟨hf, _, _⟩ | ⟨h1, h2, _, _⟩ | ⟨hf, _, _⟩
          · exfalso; omega
          · exfalso; omega
          · exfalso; omega
          · exact ⟨ha, hb⟩
          · exfalso; omega
          · exfalso; omega
          · exfalso; omega
        have h_and_true := b2_and_true (128 : u8) (191 : u8) 128 191 u8_128_toNat u8_191_toNat
                                        h_b2_range.1 h_b2_range.2
        simp only [h_beq_E0_false, Bool.false_eq_true, ↓reduceIte, h_chain_false,
                   h_beq_ED_false, h_outer_EE_and, h_and_true, Bool.not_true,
                   h_add_i2, RustM_ok_bind, h_cond_i2_ge, h_idx2, h_b3_bne]
        rfl

/-- Width-3 valid: i1 < size, SecondByteOk, i2 < size, IsContByte b3 ⇒ recurse with i2 + 1. -/
private theorem validate_at_w3_recurse (v : RustSlice u8) (index : usize)
    (hi : index.toNat < v.val.size)
    (h_lo : 224 ≤ (v.val[index.toNat]'hi).toNat)
    (h_hi : (v.val[index.toNat]'hi).toNat < 240)
    (hi1 : index.toNat + 1 < v.val.size)
    (h_sbo : SecondByteOk (v.val[index.toNat]'hi) (v.val[index.toNat + 1]'hi1))
    (hi2 : index.toNat + 2 < v.val.size)
    (h_cont : IsContByte (v.val[index.toNat + 2]'hi2)) :
    run_utf8_validation_u8.validate_at v index =
      run_utf8_validation_u8.validate_at v (index + 1 + 1 + 1) := by
  rw [validate_at_w3_unfold v index hi h_lo h_hi]
  have h_size_lt : v.val.size < 2^64 := v.size_lt_usizeSize
  have h_no_ov : index.toNat + 1 < 2^64 := by omega
  have h_add := usize_add_one_ok index h_no_ov
  have h_i1_toNat : (index + 1).toNat = index.toNat + 1 := usize_add_one_toNat _ h_no_ov
  have h_add_i2 := usize_add_one_ok (index + 1) (by rw [h_i1_toNat]; omega)
  have h_i2_toNat : (index + 1 + 1).toNat = index.toNat + 2 := by
    rw [usize_add_one_toNat (index + 1) (by rw [h_i1_toNat]; omega), h_i1_toNat]
  have h_add_i3 := usize_add_one_ok (index + 1 + 1) (by rw [h_i2_toNat]; omega)
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat v.val.size ≤ index + 1) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat, h_i1_toNat]; omega
  have h_cond_ge : decide (index + 1 ≥ USize64.ofNat v.val.size) = false := h_cond
  have h_cond_i2 : decide (USize64.ofNat v.val.size ≤ index + 1 + 1) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat, h_i2_toNat]; omega
  have h_cond_i2_ge : decide (index + 1 + 1 ≥ USize64.ofNat v.val.size) = false := h_cond_i2
  have hi1_take : (index + 1).toNat < v.val.size := by rw [h_i1_toNat]; exact hi1
  have hi2_take : (index + 1 + 1).toNat < v.val.size := by rw [h_i2_toNat]; exact hi2
  have h_idx : (v[index + 1]_? : RustM u8) = RustM.ok (v.val[(index + 1).toNat]'hi1_take) :=
    getElem_ok v (index + 1) hi1_take
  have h_idx2 : (v[index + 1 + 1]_? : RustM u8) = RustM.ok (v.val[(index + 1 + 1).toNat]'hi2_take) :=
    getElem_ok v (index + 1 + 1) hi2_take
  have h_eq_get : v.val[(index + 1).toNat]'hi1_take = v.val[index.toNat + 1]'hi1 := by
    congr 1
  have h_eq_get2 : v.val[(index + 1 + 1).toNat]'hi2_take = v.val[index.toNat + 2]'hi2 := by
    congr 1
  have h_sbo' : SecondByteOk (v.val[index.toNat]'hi) (v.val[(index + 1).toNat]'hi1_take) := by
    rw [h_eq_get]; exact h_sbo
  have h_cont' : IsContByte (v.val[(index + 1 + 1).toNat]'hi2_take) := by
    rw [h_eq_get2]; exact h_cont
  -- Show (b3 &&& 192) != 128 = false
  have h_b3_bne : ((v.val[(index + 1 + 1).toNat]'hi2_take) &&& (192 : u8) != (128 : u8)) = false := by
    rw [bne_eq_false_iff_eq]
    exact (cont_byte_iff _).mpr h_cont'
  simp only [h_add, RustM_ok_bind, ↓reduceIte, h_idx,
             rust_primitives.cmp.eq, rust_primitives.cmp.ge, rust_primitives.cmp.le,
             rust_primitives.cmp.ne, rust_primitives.hax.logical_op.and,
             rust_primitives.hax.logical_op.not, pure_bind,
             h_cond_ge, Bool.false_eq_true]
  have b2_and_true : ∀ (lo hi : u8) (lo_nat hi_nat : Nat),
      lo.toNat = lo_nat → hi.toNat = hi_nat →
      lo_nat ≤ (v.val[(index + 1).toNat]'hi1_take).toNat →
      (v.val[(index + 1).toNat]'hi1_take).toNat ≤ hi_nat →
      (decide (lo ≤ (v.val[(index + 1).toNat]'hi1_take)) &&
       decide ((v.val[(index + 1).toNat]'hi1_take) ≤ hi)) = true := by
    intro lo hi lo_nat hi_nat h_lo_n h_hi_n h_ge_lo h_le_hi
    have h_d1 : decide (lo ≤ (v.val[(index + 1).toNat]'hi1_take)) = true := by
      rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, h_lo_n]; exact h_ge_lo
    have h_d2 : decide ((v.val[(index + 1).toNat]'hi1_take) ≤ hi) = true := by
      rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, h_hi_n]; exact h_le_hi
    rw [h_d1, h_d2]; rfl
  by_cases h_E0 : (v.val[index.toNat]'hi).toNat = 224
  · have h_first_eq : (v.val[index.toNat]'hi) = (224 : u8) :=
      UInt8.toNat_inj.mp (h_E0.trans u8_224_toNat.symm)
    have h_beq : ((v.val[index.toNat]'hi) == (224 : u8)) = true := by
      rw [beq_iff_eq]; exact h_first_eq
    have h_b2_range : 160 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                      (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 191 := by
      rcases h_sbo' with ⟨_, ha, hb⟩ | ⟨h1, _, _, _⟩ | ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩
                       | ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩ | ⟨hf, _, _⟩
      · exact ⟨ha, hb⟩
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
    have h_and_true := b2_and_true (160 : u8) (191 : u8) 160 191 u8_160_toNat u8_191_toNat
                                    h_b2_range.1 h_b2_range.2
    simp only [h_beq, ↓reduceIte, h_and_true, Bool.not_true, Bool.false_eq_true,
               h_add_i2, RustM_ok_bind, h_cond_i2_ge, h_idx2, h_b3_bne, h_add_i3]
  · have h_beq_E0_false : ((v.val[index.toNat]'hi) == (224 : u8)) = false := by
      rw [beq_eq_false_iff_ne]; intro h; apply h_E0; rw [h]; exact u8_224_toNat
    by_cases h_E1_EC : 225 ≤ (v.val[index.toNat]'hi).toNat ∧ (v.val[index.toNat]'hi).toNat ≤ 236
    · obtain ⟨h1, h2⟩ := h_E1_EC
      have h_ge_225 : decide ((225 : u8) ≤ (v.val[index.toNat]'hi)) = true := by
        rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_225_toNat]; exact h1
      have h_le_236 : decide ((v.val[index.toNat]'hi) ≤ (236 : u8)) = true := by
        rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_236_toNat]; exact h2
      have h_outer_and_true : (decide ((225 : u8) ≤ (v.val[index.toNat]'hi))
          && decide ((v.val[index.toNat]'hi) ≤ (236 : u8))) = true := by
        rw [h_ge_225, h_le_236]; rfl
      have h_b2_range : 128 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                        (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 191 := by
        rcases h_sbo' with ⟨hf, _, _⟩ | ⟨_, _, ha, hb⟩ | ⟨hf, _, _⟩ | ⟨h1', _, _, _⟩
                         | ⟨hf, _, _⟩ | ⟨h1', _, _, _⟩ | ⟨hf, _, _⟩
        · exfalso; omega
        · exact ⟨ha, hb⟩
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
      have h_and_true := b2_and_true (128 : u8) (191 : u8) 128 191 u8_128_toNat u8_191_toNat
                                      h_b2_range.1 h_b2_range.2
      simp only [h_beq_E0_false, Bool.false_eq_true, ↓reduceIte,
                 h_outer_and_true, h_and_true, Bool.not_true,
                 h_add_i2, RustM_ok_bind, h_cond_i2_ge, h_idx2, h_b3_bne, h_add_i3]
    · have h_chain_false :
          (decide ((225 : u8) ≤ (v.val[index.toNat]'hi))
          && decide ((v.val[index.toNat]'hi) ≤ (236 : u8))) = false := by
        rw [Bool.and_eq_false_iff]
        rcases Classical.em (225 ≤ (v.val[index.toNat]'hi).toNat) with ha | ha
        · right; rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, u8_236_toNat]
          intro hb; exact h_E1_EC ⟨ha, hb⟩
        · left; rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, u8_225_toNat]; exact ha
      by_cases h_ED : (v.val[index.toNat]'hi).toNat = 237
      · have h_first_eq : (v.val[index.toNat]'hi) = (237 : u8) :=
          UInt8.toNat_inj.mp (h_ED.trans u8_237_toNat.symm)
        have h_beq_ED : ((v.val[index.toNat]'hi) == (237 : u8)) = true := by
          rw [beq_iff_eq]; exact h_first_eq
        have h_b2_range : 128 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                          (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 159 := by
          rcases h_sbo' with ⟨hf, _, _⟩ | ⟨h1, h2, _, _⟩ | ⟨_, ha, hb⟩ | ⟨h1, h2, _, _⟩
                           | ⟨hf, _, _⟩ | ⟨h1, h2, _, _⟩ | ⟨hf, _, _⟩
          · exfalso; omega
          · exfalso; omega
          · exact ⟨ha, hb⟩
          · exfalso; omega
          · exfalso; omega
          · exfalso; omega
          · exfalso; omega
        have h_and_true := b2_and_true (128 : u8) (159 : u8) 128 159 u8_128_toNat u8_159_toNat
                                        h_b2_range.1 h_b2_range.2
        simp only [h_beq_E0_false, Bool.false_eq_true, ↓reduceIte, h_chain_false,
                   h_beq_ED, h_and_true, Bool.not_true,
                   h_add_i2, RustM_ok_bind, h_cond_i2_ge, h_idx2, h_b3_bne, h_add_i3]
      · have h_beq_ED_false : ((v.val[index.toNat]'hi) == (237 : u8)) = false := by
          rw [beq_eq_false_iff_ne]; intro h; apply h_ED; rw [h]; exact u8_237_toNat
        have h_EE_EF : 238 ≤ (v.val[index.toNat]'hi).toNat ∧ (v.val[index.toNat]'hi).toNat ≤ 239 := by
          refine ⟨?_, by omega⟩
          rcases Nat.lt_or_ge (v.val[index.toNat]'hi).toNat 238 with h_lt | h_ge
          · exfalso
            rcases Nat.lt_or_ge (v.val[index.toNat]'hi).toNat 225 with h_lt' | h_ge'
            · apply h_E0; omega
            · rcases Nat.lt_or_ge (v.val[index.toNat]'hi).toNat 237 with h_lt'' | h_ge''
              · apply h_E1_EC; exact ⟨h_ge', by omega⟩
              · apply h_ED; omega
          · exact h_ge
        obtain ⟨h1', h2'⟩ := h_EE_EF
        have h_ge_238 : decide ((238 : u8) ≤ (v.val[index.toNat]'hi)) = true := by
          rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_238_toNat]; exact h1'
        have h_le_239 : decide ((v.val[index.toNat]'hi) ≤ (239 : u8)) = true := by
          rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_239_toNat]; exact h2'
        have h_outer_EE_and : (decide ((238 : u8) ≤ (v.val[index.toNat]'hi))
            && decide ((v.val[index.toNat]'hi) ≤ (239 : u8))) = true := by
          rw [h_ge_238, h_le_239]; rfl
        have h_b2_range : 128 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                          (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 191 := by
          rcases h_sbo' with ⟨hf, _, _⟩ | ⟨h1, h2, _, _⟩ | ⟨hf, _, _⟩ | ⟨_, _, ha, hb⟩
                           | ⟨hf, _, _⟩ | ⟨h1, h2, _, _⟩ | ⟨hf, _, _⟩
          · exfalso; omega
          · exfalso; omega
          · exfalso; omega
          · exact ⟨ha, hb⟩
          · exfalso; omega
          · exfalso; omega
          · exfalso; omega
        have h_and_true := b2_and_true (128 : u8) (191 : u8) 128 191 u8_128_toNat u8_191_toNat
                                        h_b2_range.1 h_b2_range.2
        simp only [h_beq_E0_false, Bool.false_eq_true, ↓reduceIte, h_chain_false,
                   h_beq_ED_false, h_outer_EE_and, h_and_true, Bool.not_true,
                   h_add_i2, RustM_ok_bind, h_cond_i2_ge, h_idx2, h_b3_bne, h_add_i3]

/-! ### Width-4 leaf step lemmas. -/

/-- Width-4 truncation at i1: i1 ≥ size ⇒ Err None. -/
private theorem validate_at_w4_trunc1 (v : RustSlice u8) (index : usize)
    (hi : index.toNat < v.val.size)
    (h_lo : 240 ≤ (v.val[index.toNat]'hi).toNat)
    (h_hi : (v.val[index.toNat]'hi).toNat < 245)
    (h_trunc : v.val.size ≤ index.toNat + 1) :
    run_utf8_validation_u8.validate_at v index =
      RustM.ok (core_models.result.Result.Err
        (run_utf8_validation_u8.Utf8Error.mk
          (valid_up_to := index)
          (error_len := core_models.option.Option.None))) := by
  rw [validate_at_w4_unfold v index hi h_lo h_hi]
  have h_size_lt : v.val.size < 2^64 := v.size_lt_usizeSize
  have h_no_ov : index.toNat + 1 < 2^64 := by omega
  have h_add := usize_add_one_ok index h_no_ov
  have h_i1_toNat : (index + 1).toNat = index.toNat + 1 := usize_add_one_toNat _ h_no_ov
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat v.val.size ≤ index + 1) = true := by
    rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat, h_i1_toNat]; omega
  simp only [h_add, RustM_ok_bind, rust_primitives.cmp.ge, pure_bind, h_cond, ↓reduceIte]
  rfl

/-- Width-4 bad second byte: i1 < size, ¬SecondByteOk first b2 ⇒ Err (Some 1). -/
private theorem validate_at_w4_bad_b2 (v : RustSlice u8) (index : usize)
    (hi : index.toNat < v.val.size)
    (h_lo : 240 ≤ (v.val[index.toNat]'hi).toNat)
    (h_hi : (v.val[index.toNat]'hi).toNat < 245)
    (hi1 : index.toNat + 1 < v.val.size)
    (h_bad : ¬ SecondByteOk (v.val[index.toNat]'hi) (v.val[index.toNat + 1]'hi1)) :
    run_utf8_validation_u8.validate_at v index =
      RustM.ok (core_models.result.Result.Err
        (run_utf8_validation_u8.Utf8Error.mk
          (valid_up_to := index)
          (error_len := core_models.option.Option.Some (1 : u8)))) := by
  rw [validate_at_w4_unfold v index hi h_lo h_hi]
  have h_size_lt : v.val.size < 2^64 := v.size_lt_usizeSize
  have h_no_ov : index.toNat + 1 < 2^64 := by omega
  have h_add := usize_add_one_ok index h_no_ov
  have h_i1_toNat : (index + 1).toNat = index.toNat + 1 := usize_add_one_toNat _ h_no_ov
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat v.val.size ≤ index + 1) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat, h_i1_toNat]; omega
  have h_cond_ge : decide (index + 1 ≥ USize64.ofNat v.val.size) = false := h_cond
  have hi1_take : (index + 1).toNat < v.val.size := by rw [h_i1_toNat]; exact hi1
  have h_idx : (v[index + 1]_? : RustM u8) = RustM.ok (v.val[(index + 1).toNat]'hi1_take) :=
    getElem_ok v (index + 1) hi1_take
  have h_eq_get : v.val[(index + 1).toNat]'hi1_take = v.val[index.toNat + 1]'hi1 := by
    congr 1
  have h_bad' : ¬ SecondByteOk (v.val[index.toNat]'hi) (v.val[(index + 1).toNat]'hi1_take) := by
    rw [h_eq_get]; exact h_bad
  -- Helper for b2 not in range → and = false.
  have b2_and_false : ∀ (lo hi : u8) (lo_nat hi_nat : Nat),
      lo.toNat = lo_nat → hi.toNat = hi_nat →
      ¬ (lo_nat ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
         (v.val[(index + 1).toNat]'hi1_take).toNat ≤ hi_nat) →
      (decide (lo ≤ (v.val[(index + 1).toNat]'hi1_take)) &&
       decide ((v.val[(index + 1).toNat]'hi1_take) ≤ hi)) = false := by
    intro lo hi lo_nat hi_nat h_lo_n h_hi_n h_not
    rw [Bool.and_eq_false_iff]
    rcases Classical.em (lo_nat ≤ (v.val[(index + 1).toNat]'hi1_take).toNat) with ha | ha
    · right
      rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, h_hi_n]
      intro hb; exact h_not ⟨ha, hb⟩
    · left
      rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, h_lo_n]; exact ha
  simp only [h_add, RustM_ok_bind, ↓reduceIte, h_idx,
             rust_primitives.cmp.eq, rust_primitives.cmp.ge, rust_primitives.cmp.le,
             rust_primitives.cmp.ne, rust_primitives.hax.logical_op.and,
             rust_primitives.hax.logical_op.not, pure_bind,
             h_cond_ge, Bool.false_eq_true]
  by_cases h_F0 : (v.val[index.toNat]'hi).toNat = 240
  · have h_first_eq : (v.val[index.toNat]'hi) = (240 : u8) :=
      UInt8.toNat_inj.mp (h_F0.trans u8_240_toNat.symm)
    have h_beq : ((v.val[index.toNat]'hi) == (240 : u8)) = true := by
      rw [beq_iff_eq]; exact h_first_eq
    have h_not_range : ¬ (144 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                         (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 191) := by
      intro ⟨ha, hb⟩
      apply h_bad'; unfold SecondByteOk
      right; right; right; right; left
      exact ⟨h_F0, ha, hb⟩
    have h_and_false := b2_and_false (144 : u8) (191 : u8) 144 191 u8_144_toNat u8_191_toNat
                                      h_not_range
    simp only [h_beq, ↓reduceIte, h_and_false, Bool.not_false]
    rfl
  · have h_beq_F0_false : ((v.val[index.toNat]'hi) == (240 : u8)) = false := by
      rw [beq_eq_false_iff_ne]; intro h; apply h_F0; rw [h]; exact u8_240_toNat
    by_cases h_F1_F3 : 241 ≤ (v.val[index.toNat]'hi).toNat ∧ (v.val[index.toNat]'hi).toNat ≤ 243
    · obtain ⟨h1, h2⟩ := h_F1_F3
      have h_ge_241 : decide ((241 : u8) ≤ (v.val[index.toNat]'hi)) = true := by
        rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_241_toNat]; exact h1
      have h_le_243 : decide ((v.val[index.toNat]'hi) ≤ (243 : u8)) = true := by
        rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_243_toNat]; exact h2
      have h_outer_and_true : (decide ((241 : u8) ≤ (v.val[index.toNat]'hi))
          && decide ((v.val[index.toNat]'hi) ≤ (243 : u8))) = true := by
        rw [h_ge_241, h_le_243]; rfl
      have h_not_range : ¬ (128 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                           (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 191) := by
        intro ⟨ha, hb⟩
        apply h_bad'; unfold SecondByteOk
        right; right; right; right; right; left
        exact ⟨h1, h2, ha, hb⟩
      have h_and_false := b2_and_false (128 : u8) (191 : u8) 128 191 u8_128_toNat u8_191_toNat
                                        h_not_range
      simp only [h_beq_F0_false, Bool.false_eq_true, ↓reduceIte,
                 h_outer_and_true, h_and_false, Bool.not_false]
      rfl
    · have h_chain_false :
          (decide ((241 : u8) ≤ (v.val[index.toNat]'hi))
          && decide ((v.val[index.toNat]'hi) ≤ (243 : u8))) = false := by
        rw [Bool.and_eq_false_iff]
        rcases Classical.em (241 ≤ (v.val[index.toNat]'hi).toNat) with ha | ha
        · right; rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, u8_243_toNat]
          intro hb; exact h_F1_F3 ⟨ha, hb⟩
        · left; rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, u8_241_toNat]; exact ha
      have h_F4 : (v.val[index.toNat]'hi).toNat = 244 := by
        rcases Nat.lt_or_ge (v.val[index.toNat]'hi).toNat 241 with h_lt | h_ge
        · exfalso; apply h_F0; omega
        · rcases Nat.lt_or_ge (v.val[index.toNat]'hi).toNat 244 with h_lt' | h_ge'
          · exfalso; apply h_F1_F3; exact ⟨h_ge, by omega⟩
          · omega
      have h_first_eq : (v.val[index.toNat]'hi) = (244 : u8) :=
        UInt8.toNat_inj.mp (h_F4.trans u8_244_toNat.symm)
      have h_beq_F4 : ((v.val[index.toNat]'hi) == (244 : u8)) = true := by
        rw [beq_iff_eq]; exact h_first_eq
      have h_not_range : ¬ (128 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                           (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 143) := by
        intro ⟨ha, hb⟩
        apply h_bad'; unfold SecondByteOk
        right; right; right; right; right; right
        exact ⟨h_F4, ha, hb⟩
      have h_and_false := b2_and_false (128 : u8) (143 : u8) 128 143 u8_128_toNat u8_143_toNat
                                        h_not_range
      simp only [h_beq_F0_false, Bool.false_eq_true, ↓reduceIte, h_chain_false,
                 h_beq_F4, h_and_false, Bool.not_false]
      rfl

/-- Width-4 truncation at i2 (after SecondByteOk). -/
private theorem validate_at_w4_trunc2 (v : RustSlice u8) (index : usize)
    (hi : index.toNat < v.val.size)
    (h_lo : 240 ≤ (v.val[index.toNat]'hi).toNat)
    (h_hi : (v.val[index.toNat]'hi).toNat < 245)
    (hi1 : index.toNat + 1 < v.val.size)
    (h_sbo : SecondByteOk (v.val[index.toNat]'hi) (v.val[index.toNat + 1]'hi1))
    (h_trunc : v.val.size ≤ index.toNat + 2) :
    run_utf8_validation_u8.validate_at v index =
      RustM.ok (core_models.result.Result.Err
        (run_utf8_validation_u8.Utf8Error.mk
          (valid_up_to := index)
          (error_len := core_models.option.Option.None))) := by
  rw [validate_at_w4_unfold v index hi h_lo h_hi]
  have h_size_lt : v.val.size < 2^64 := v.size_lt_usizeSize
  have h_no_ov : index.toNat + 1 < 2^64 := by omega
  have h_add := usize_add_one_ok index h_no_ov
  have h_i1_toNat : (index + 1).toNat = index.toNat + 1 := usize_add_one_toNat _ h_no_ov
  have h_add_i2 := usize_add_one_ok (index + 1) (by rw [h_i1_toNat]; omega)
  have h_i2_toNat : (index + 1 + 1).toNat = index.toNat + 2 := by
    rw [usize_add_one_toNat (index + 1) (by rw [h_i1_toNat]; omega), h_i1_toNat]
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat v.val.size ≤ index + 1) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat, h_i1_toNat]; omega
  have h_cond_ge : decide (index + 1 ≥ USize64.ofNat v.val.size) = false := h_cond
  have h_cond_i2 : decide (USize64.ofNat v.val.size ≤ index + 1 + 1) = true := by
    rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat, h_i2_toNat]; exact h_trunc
  have h_cond_i2_ge : decide (index + 1 + 1 ≥ USize64.ofNat v.val.size) = true := h_cond_i2
  have hi1_take : (index + 1).toNat < v.val.size := by rw [h_i1_toNat]; exact hi1
  have h_idx : (v[index + 1]_? : RustM u8) = RustM.ok (v.val[(index + 1).toNat]'hi1_take) :=
    getElem_ok v (index + 1) hi1_take
  have h_eq_get : v.val[(index + 1).toNat]'hi1_take = v.val[index.toNat + 1]'hi1 := by
    congr 1
  have h_sbo' : SecondByteOk (v.val[index.toNat]'hi) (v.val[(index + 1).toNat]'hi1_take) := by
    rw [h_eq_get]; exact h_sbo
  simp only [h_add, RustM_ok_bind, ↓reduceIte, h_idx,
             rust_primitives.cmp.eq, rust_primitives.cmp.ge, rust_primitives.cmp.le,
             rust_primitives.cmp.ne, rust_primitives.hax.logical_op.and,
             rust_primitives.hax.logical_op.not, pure_bind,
             h_cond_ge, Bool.false_eq_true]
  have b2_and_true : ∀ (lo hi : u8) (lo_nat hi_nat : Nat),
      lo.toNat = lo_nat → hi.toNat = hi_nat →
      lo_nat ≤ (v.val[(index + 1).toNat]'hi1_take).toNat →
      (v.val[(index + 1).toNat]'hi1_take).toNat ≤ hi_nat →
      (decide (lo ≤ (v.val[(index + 1).toNat]'hi1_take)) &&
       decide ((v.val[(index + 1).toNat]'hi1_take) ≤ hi)) = true := by
    intro lo hi lo_nat hi_nat h_lo_n h_hi_n h_ge_lo h_le_hi
    have h_d1 : decide (lo ≤ (v.val[(index + 1).toNat]'hi1_take)) = true := by
      rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, h_lo_n]; exact h_ge_lo
    have h_d2 : decide ((v.val[(index + 1).toNat]'hi1_take) ≤ hi) = true := by
      rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, h_hi_n]; exact h_le_hi
    rw [h_d1, h_d2]; rfl
  by_cases h_F0 : (v.val[index.toNat]'hi).toNat = 240
  · have h_first_eq : (v.val[index.toNat]'hi) = (240 : u8) :=
      UInt8.toNat_inj.mp (h_F0.trans u8_240_toNat.symm)
    have h_beq : ((v.val[index.toNat]'hi) == (240 : u8)) = true := by
      rw [beq_iff_eq]; exact h_first_eq
    have h_b2_range : 144 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                      (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 191 := by
      rcases h_sbo' with ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩ | ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩
                       | ⟨_, ha, hb⟩ | ⟨h1, _, _, _⟩ | ⟨hf, _, _⟩
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exact ⟨ha, hb⟩
      · exfalso; omega
      · exfalso; omega
    have h_and_true := b2_and_true (144 : u8) (191 : u8) 144 191 u8_144_toNat u8_191_toNat
                                    h_b2_range.1 h_b2_range.2
    simp only [h_beq, ↓reduceIte, h_and_true, Bool.not_true, Bool.false_eq_true,
               h_add_i2, RustM_ok_bind, h_cond_i2_ge]
    rfl
  · have h_beq_F0_false : ((v.val[index.toNat]'hi) == (240 : u8)) = false := by
      rw [beq_eq_false_iff_ne]; intro h; apply h_F0; rw [h]; exact u8_240_toNat
    by_cases h_F1_F3 : 241 ≤ (v.val[index.toNat]'hi).toNat ∧ (v.val[index.toNat]'hi).toNat ≤ 243
    · obtain ⟨h1, h2⟩ := h_F1_F3
      have h_ge_241 : decide ((241 : u8) ≤ (v.val[index.toNat]'hi)) = true := by
        rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_241_toNat]; exact h1
      have h_le_243 : decide ((v.val[index.toNat]'hi) ≤ (243 : u8)) = true := by
        rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_243_toNat]; exact h2
      have h_outer_and_true : (decide ((241 : u8) ≤ (v.val[index.toNat]'hi))
          && decide ((v.val[index.toNat]'hi) ≤ (243 : u8))) = true := by
        rw [h_ge_241, h_le_243]; rfl
      have h_b2_range : 128 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                        (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 191 := by
        rcases h_sbo' with ⟨hf, _, _⟩ | ⟨h1', _, _, _⟩ | ⟨hf, _, _⟩ | ⟨h1', _, _, _⟩
                         | ⟨hf, _, _⟩ | ⟨_, _, ha, hb⟩ | ⟨hf, _, _⟩
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exact ⟨ha, hb⟩
        · exfalso; omega
      have h_and_true := b2_and_true (128 : u8) (191 : u8) 128 191 u8_128_toNat u8_191_toNat
                                      h_b2_range.1 h_b2_range.2
      simp only [h_beq_F0_false, Bool.false_eq_true, ↓reduceIte,
                 h_outer_and_true, h_and_true, Bool.not_true,
                 h_add_i2, RustM_ok_bind, h_cond_i2_ge]
      rfl
    · have h_chain_false :
          (decide ((241 : u8) ≤ (v.val[index.toNat]'hi))
          && decide ((v.val[index.toNat]'hi) ≤ (243 : u8))) = false := by
        rw [Bool.and_eq_false_iff]
        rcases Classical.em (241 ≤ (v.val[index.toNat]'hi).toNat) with ha | ha
        · right; rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, u8_243_toNat]
          intro hb; exact h_F1_F3 ⟨ha, hb⟩
        · left; rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, u8_241_toNat]; exact ha
      have h_F4 : (v.val[index.toNat]'hi).toNat = 244 := by
        rcases Nat.lt_or_ge (v.val[index.toNat]'hi).toNat 241 with h_lt | h_ge
        · exfalso; apply h_F0; omega
        · rcases Nat.lt_or_ge (v.val[index.toNat]'hi).toNat 244 with h_lt' | h_ge'
          · exfalso; apply h_F1_F3; exact ⟨h_ge, by omega⟩
          · omega
      have h_first_eq : (v.val[index.toNat]'hi) = (244 : u8) :=
        UInt8.toNat_inj.mp (h_F4.trans u8_244_toNat.symm)
      have h_beq_F4 : ((v.val[index.toNat]'hi) == (244 : u8)) = true := by
        rw [beq_iff_eq]; exact h_first_eq
      have h_b2_range : 128 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                        (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 143 := by
        rcases h_sbo' with ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩ | ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩
                         | ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩ | ⟨_, ha, hb⟩
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exact ⟨ha, hb⟩
      have h_and_true := b2_and_true (128 : u8) (143 : u8) 128 143 u8_128_toNat u8_143_toNat
                                      h_b2_range.1 h_b2_range.2
      simp only [h_beq_F0_false, Bool.false_eq_true, ↓reduceIte, h_chain_false,
                 h_beq_F4, h_and_true, Bool.not_true,
                 h_add_i2, RustM_ok_bind, h_cond_i2_ge]
      rfl

/-- Width-4 bad continuation byte at i2 (b3 is not a continuation byte). -/
private theorem validate_at_w4_bad_cont1 (v : RustSlice u8) (index : usize)
    (hi : index.toNat < v.val.size)
    (h_lo : 240 ≤ (v.val[index.toNat]'hi).toNat)
    (h_hi : (v.val[index.toNat]'hi).toNat < 245)
    (hi1 : index.toNat + 1 < v.val.size)
    (h_sbo : SecondByteOk (v.val[index.toNat]'hi) (v.val[index.toNat + 1]'hi1))
    (hi2 : index.toNat + 2 < v.val.size)
    (h_bad : ¬ IsContByte (v.val[index.toNat + 2]'hi2)) :
    run_utf8_validation_u8.validate_at v index =
      RustM.ok (core_models.result.Result.Err
        (run_utf8_validation_u8.Utf8Error.mk
          (valid_up_to := index)
          (error_len := core_models.option.Option.Some (2 : u8)))) := by
  rw [validate_at_w4_unfold v index hi h_lo h_hi]
  have h_size_lt : v.val.size < 2^64 := v.size_lt_usizeSize
  have h_no_ov : index.toNat + 1 < 2^64 := by omega
  have h_add := usize_add_one_ok index h_no_ov
  have h_i1_toNat : (index + 1).toNat = index.toNat + 1 := usize_add_one_toNat _ h_no_ov
  have h_add_i2 := usize_add_one_ok (index + 1) (by rw [h_i1_toNat]; omega)
  have h_i2_toNat : (index + 1 + 1).toNat = index.toNat + 2 := by
    rw [usize_add_one_toNat (index + 1) (by rw [h_i1_toNat]; omega), h_i1_toNat]
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat v.val.size ≤ index + 1) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat, h_i1_toNat]; omega
  have h_cond_ge : decide (index + 1 ≥ USize64.ofNat v.val.size) = false := h_cond
  have h_cond_i2 : decide (USize64.ofNat v.val.size ≤ index + 1 + 1) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat, h_i2_toNat]; omega
  have h_cond_i2_ge : decide (index + 1 + 1 ≥ USize64.ofNat v.val.size) = false := h_cond_i2
  have hi1_take : (index + 1).toNat < v.val.size := by rw [h_i1_toNat]; exact hi1
  have hi2_take : (index + 1 + 1).toNat < v.val.size := by rw [h_i2_toNat]; exact hi2
  have h_idx : (v[index + 1]_? : RustM u8) = RustM.ok (v.val[(index + 1).toNat]'hi1_take) :=
    getElem_ok v (index + 1) hi1_take
  have h_idx2 : (v[index + 1 + 1]_? : RustM u8) = RustM.ok (v.val[(index + 1 + 1).toNat]'hi2_take) :=
    getElem_ok v (index + 1 + 1) hi2_take
  have h_eq_get : v.val[(index + 1).toNat]'hi1_take = v.val[index.toNat + 1]'hi1 := by
    congr 1
  have h_eq_get2 : v.val[(index + 1 + 1).toNat]'hi2_take = v.val[index.toNat + 2]'hi2 := by
    congr 1
  have h_sbo' : SecondByteOk (v.val[index.toNat]'hi) (v.val[(index + 1).toNat]'hi1_take) := by
    rw [h_eq_get]; exact h_sbo
  have h_bad' : ¬ IsContByte (v.val[(index + 1 + 1).toNat]'hi2_take) := by
    rw [h_eq_get2]; exact h_bad
  have h_b3_bne : ((v.val[(index + 1 + 1).toNat]'hi2_take) &&& (192 : u8) != (128 : u8)) = true := by
    apply bne_iff_ne.mpr; intro h_eq
    exact h_bad' ((cont_byte_iff _).mp h_eq)
  simp only [h_add, RustM_ok_bind, ↓reduceIte, h_idx,
             rust_primitives.cmp.eq, rust_primitives.cmp.ge, rust_primitives.cmp.le,
             rust_primitives.cmp.ne, rust_primitives.hax.logical_op.and,
             rust_primitives.hax.logical_op.not, pure_bind,
             h_cond_ge, Bool.false_eq_true]
  have b2_and_true : ∀ (lo hi : u8) (lo_nat hi_nat : Nat),
      lo.toNat = lo_nat → hi.toNat = hi_nat →
      lo_nat ≤ (v.val[(index + 1).toNat]'hi1_take).toNat →
      (v.val[(index + 1).toNat]'hi1_take).toNat ≤ hi_nat →
      (decide (lo ≤ (v.val[(index + 1).toNat]'hi1_take)) &&
       decide ((v.val[(index + 1).toNat]'hi1_take) ≤ hi)) = true := by
    intro lo hi lo_nat hi_nat h_lo_n h_hi_n h_ge_lo h_le_hi
    have h_d1 : decide (lo ≤ (v.val[(index + 1).toNat]'hi1_take)) = true := by
      rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, h_lo_n]; exact h_ge_lo
    have h_d2 : decide ((v.val[(index + 1).toNat]'hi1_take) ≤ hi) = true := by
      rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, h_hi_n]; exact h_le_hi
    rw [h_d1, h_d2]; rfl
  by_cases h_F0 : (v.val[index.toNat]'hi).toNat = 240
  · have h_first_eq : (v.val[index.toNat]'hi) = (240 : u8) :=
      UInt8.toNat_inj.mp (h_F0.trans u8_240_toNat.symm)
    have h_beq : ((v.val[index.toNat]'hi) == (240 : u8)) = true := by
      rw [beq_iff_eq]; exact h_first_eq
    have h_b2_range : 144 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                      (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 191 := by
      rcases h_sbo' with ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩ | ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩
                       | ⟨_, ha, hb⟩ | ⟨h1, _, _, _⟩ | ⟨hf, _, _⟩
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exact ⟨ha, hb⟩
      · exfalso; omega
      · exfalso; omega
    have h_and_true := b2_and_true (144 : u8) (191 : u8) 144 191 u8_144_toNat u8_191_toNat
                                    h_b2_range.1 h_b2_range.2
    simp only [h_beq, ↓reduceIte, h_and_true, Bool.not_true, Bool.false_eq_true,
               h_add_i2, RustM_ok_bind, h_cond_i2_ge, h_idx2, h_b3_bne]
    rfl
  · have h_beq_F0_false : ((v.val[index.toNat]'hi) == (240 : u8)) = false := by
      rw [beq_eq_false_iff_ne]; intro h; apply h_F0; rw [h]; exact u8_240_toNat
    by_cases h_F1_F3 : 241 ≤ (v.val[index.toNat]'hi).toNat ∧ (v.val[index.toNat]'hi).toNat ≤ 243
    · obtain ⟨h1, h2⟩ := h_F1_F3
      have h_ge_241 : decide ((241 : u8) ≤ (v.val[index.toNat]'hi)) = true := by
        rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_241_toNat]; exact h1
      have h_le_243 : decide ((v.val[index.toNat]'hi) ≤ (243 : u8)) = true := by
        rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_243_toNat]; exact h2
      have h_outer_and_true : (decide ((241 : u8) ≤ (v.val[index.toNat]'hi))
          && decide ((v.val[index.toNat]'hi) ≤ (243 : u8))) = true := by
        rw [h_ge_241, h_le_243]; rfl
      have h_b2_range : 128 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                        (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 191 := by
        rcases h_sbo' with ⟨hf, _, _⟩ | ⟨h1', _, _, _⟩ | ⟨hf, _, _⟩ | ⟨h1', _, _, _⟩
                         | ⟨hf, _, _⟩ | ⟨_, _, ha, hb⟩ | ⟨hf, _, _⟩
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exact ⟨ha, hb⟩
        · exfalso; omega
      have h_and_true := b2_and_true (128 : u8) (191 : u8) 128 191 u8_128_toNat u8_191_toNat
                                      h_b2_range.1 h_b2_range.2
      simp only [h_beq_F0_false, Bool.false_eq_true, ↓reduceIte,
                 h_outer_and_true, h_and_true, Bool.not_true,
                 h_add_i2, RustM_ok_bind, h_cond_i2_ge, h_idx2, h_b3_bne]
      rfl
    · have h_chain_false :
          (decide ((241 : u8) ≤ (v.val[index.toNat]'hi))
          && decide ((v.val[index.toNat]'hi) ≤ (243 : u8))) = false := by
        rw [Bool.and_eq_false_iff]
        rcases Classical.em (241 ≤ (v.val[index.toNat]'hi).toNat) with ha | ha
        · right; rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, u8_243_toNat]
          intro hb; exact h_F1_F3 ⟨ha, hb⟩
        · left; rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, u8_241_toNat]; exact ha
      have h_F4 : (v.val[index.toNat]'hi).toNat = 244 := by
        rcases Nat.lt_or_ge (v.val[index.toNat]'hi).toNat 241 with h_lt | h_ge
        · exfalso; apply h_F0; omega
        · rcases Nat.lt_or_ge (v.val[index.toNat]'hi).toNat 244 with h_lt' | h_ge'
          · exfalso; apply h_F1_F3; exact ⟨h_ge, by omega⟩
          · omega
      have h_first_eq : (v.val[index.toNat]'hi) = (244 : u8) :=
        UInt8.toNat_inj.mp (h_F4.trans u8_244_toNat.symm)
      have h_beq_F4 : ((v.val[index.toNat]'hi) == (244 : u8)) = true := by
        rw [beq_iff_eq]; exact h_first_eq
      have h_b2_range : 128 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                        (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 143 := by
        rcases h_sbo' with ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩ | ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩
                         | ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩ | ⟨_, ha, hb⟩
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exact ⟨ha, hb⟩
      have h_and_true := b2_and_true (128 : u8) (143 : u8) 128 143 u8_128_toNat u8_143_toNat
                                      h_b2_range.1 h_b2_range.2
      simp only [h_beq_F0_false, Bool.false_eq_true, ↓reduceIte, h_chain_false,
                 h_beq_F4, h_and_true, Bool.not_true,
                 h_add_i2, RustM_ok_bind, h_cond_i2_ge, h_idx2, h_b3_bne]
      rfl

/-- Width-4 truncation at i3: b3 is cont, then i3 ≥ size ⇒ Err None. -/
private theorem validate_at_w4_trunc3 (v : RustSlice u8) (index : usize)
    (hi : index.toNat < v.val.size)
    (h_lo : 240 ≤ (v.val[index.toNat]'hi).toNat)
    (h_hi : (v.val[index.toNat]'hi).toNat < 245)
    (hi1 : index.toNat + 1 < v.val.size)
    (h_sbo : SecondByteOk (v.val[index.toNat]'hi) (v.val[index.toNat + 1]'hi1))
    (hi2 : index.toNat + 2 < v.val.size)
    (h_cont : IsContByte (v.val[index.toNat + 2]'hi2))
    (h_trunc : v.val.size ≤ index.toNat + 3) :
    run_utf8_validation_u8.validate_at v index =
      RustM.ok (core_models.result.Result.Err
        (run_utf8_validation_u8.Utf8Error.mk
          (valid_up_to := index)
          (error_len := core_models.option.Option.None))) := by
  rw [validate_at_w4_unfold v index hi h_lo h_hi]
  have h_size_lt : v.val.size < 2^64 := v.size_lt_usizeSize
  have h_no_ov : index.toNat + 1 < 2^64 := by omega
  have h_add := usize_add_one_ok index h_no_ov
  have h_i1_toNat : (index + 1).toNat = index.toNat + 1 := usize_add_one_toNat _ h_no_ov
  have h_add_i2 := usize_add_one_ok (index + 1) (by rw [h_i1_toNat]; omega)
  have h_i2_toNat : (index + 1 + 1).toNat = index.toNat + 2 := by
    rw [usize_add_one_toNat (index + 1) (by rw [h_i1_toNat]; omega), h_i1_toNat]
  have h_add_i3 := usize_add_one_ok (index + 1 + 1) (by rw [h_i2_toNat]; omega)
  have h_i3_toNat : (index + 1 + 1 + 1).toNat = index.toNat + 3 := by
    rw [usize_add_one_toNat (index + 1 + 1) (by rw [h_i2_toNat]; omega), h_i2_toNat]
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat v.val.size ≤ index + 1) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat, h_i1_toNat]; omega
  have h_cond_ge : decide (index + 1 ≥ USize64.ofNat v.val.size) = false := h_cond
  have h_cond_i2 : decide (USize64.ofNat v.val.size ≤ index + 1 + 1) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat, h_i2_toNat]; omega
  have h_cond_i2_ge : decide (index + 1 + 1 ≥ USize64.ofNat v.val.size) = false := h_cond_i2
  have h_cond_i3 : decide (USize64.ofNat v.val.size ≤ index + 1 + 1 + 1) = true := by
    rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat, h_i3_toNat]; exact h_trunc
  have h_cond_i3_ge : decide (index + 1 + 1 + 1 ≥ USize64.ofNat v.val.size) = true := h_cond_i3
  have hi1_take : (index + 1).toNat < v.val.size := by rw [h_i1_toNat]; exact hi1
  have hi2_take : (index + 1 + 1).toNat < v.val.size := by rw [h_i2_toNat]; exact hi2
  have h_idx : (v[index + 1]_? : RustM u8) = RustM.ok (v.val[(index + 1).toNat]'hi1_take) :=
    getElem_ok v (index + 1) hi1_take
  have h_idx2 : (v[index + 1 + 1]_? : RustM u8) = RustM.ok (v.val[(index + 1 + 1).toNat]'hi2_take) :=
    getElem_ok v (index + 1 + 1) hi2_take
  have h_eq_get : v.val[(index + 1).toNat]'hi1_take = v.val[index.toNat + 1]'hi1 := by congr 1
  have h_eq_get2 : v.val[(index + 1 + 1).toNat]'hi2_take = v.val[index.toNat + 2]'hi2 := by congr 1
  have h_sbo' : SecondByteOk (v.val[index.toNat]'hi) (v.val[(index + 1).toNat]'hi1_take) := by
    rw [h_eq_get]; exact h_sbo
  have h_cont' : IsContByte (v.val[(index + 1 + 1).toNat]'hi2_take) := by
    rw [h_eq_get2]; exact h_cont
  have h_b3_bne : ((v.val[(index + 1 + 1).toNat]'hi2_take) &&& (192 : u8) != (128 : u8)) = false := by
    rw [bne_eq_false_iff_eq]; exact (cont_byte_iff _).mpr h_cont'
  simp only [h_add, RustM_ok_bind, ↓reduceIte, h_idx,
             rust_primitives.cmp.eq, rust_primitives.cmp.ge, rust_primitives.cmp.le,
             rust_primitives.cmp.ne, rust_primitives.hax.logical_op.and,
             rust_primitives.hax.logical_op.not, pure_bind,
             h_cond_ge, Bool.false_eq_true]
  have b2_and_true : ∀ (lo hi : u8) (lo_nat hi_nat : Nat),
      lo.toNat = lo_nat → hi.toNat = hi_nat →
      lo_nat ≤ (v.val[(index + 1).toNat]'hi1_take).toNat →
      (v.val[(index + 1).toNat]'hi1_take).toNat ≤ hi_nat →
      (decide (lo ≤ (v.val[(index + 1).toNat]'hi1_take)) &&
       decide ((v.val[(index + 1).toNat]'hi1_take) ≤ hi)) = true := by
    intro lo hi lo_nat hi_nat h_lo_n h_hi_n h_ge_lo h_le_hi
    have h_d1 : decide (lo ≤ (v.val[(index + 1).toNat]'hi1_take)) = true := by
      rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, h_lo_n]; exact h_ge_lo
    have h_d2 : decide ((v.val[(index + 1).toNat]'hi1_take) ≤ hi) = true := by
      rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, h_hi_n]; exact h_le_hi
    rw [h_d1, h_d2]; rfl
  by_cases h_F0 : (v.val[index.toNat]'hi).toNat = 240
  · have h_first_eq : (v.val[index.toNat]'hi) = (240 : u8) :=
      UInt8.toNat_inj.mp (h_F0.trans u8_240_toNat.symm)
    have h_beq : ((v.val[index.toNat]'hi) == (240 : u8)) = true := by
      rw [beq_iff_eq]; exact h_first_eq
    have h_b2_range : 144 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                      (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 191 := by
      rcases h_sbo' with ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩ | ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩
                       | ⟨_, ha, hb⟩ | ⟨h1, _, _, _⟩ | ⟨hf, _, _⟩
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exact ⟨ha, hb⟩
      · exfalso; omega
      · exfalso; omega
    have h_and_true := b2_and_true (144 : u8) (191 : u8) 144 191 u8_144_toNat u8_191_toNat
                                    h_b2_range.1 h_b2_range.2
    simp only [h_beq, ↓reduceIte, h_and_true, Bool.not_true, Bool.false_eq_true,
               h_add_i2, RustM_ok_bind, h_cond_i2_ge, h_idx2, h_b3_bne,
               h_add_i3, h_cond_i3_ge]
    rfl
  · have h_beq_F0_false : ((v.val[index.toNat]'hi) == (240 : u8)) = false := by
      rw [beq_eq_false_iff_ne]; intro h; apply h_F0; rw [h]; exact u8_240_toNat
    by_cases h_F1_F3 : 241 ≤ (v.val[index.toNat]'hi).toNat ∧ (v.val[index.toNat]'hi).toNat ≤ 243
    · obtain ⟨h1, h2⟩ := h_F1_F3
      have h_ge_241 : decide ((241 : u8) ≤ (v.val[index.toNat]'hi)) = true := by
        rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_241_toNat]; exact h1
      have h_le_243 : decide ((v.val[index.toNat]'hi) ≤ (243 : u8)) = true := by
        rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_243_toNat]; exact h2
      have h_outer_and_true : (decide ((241 : u8) ≤ (v.val[index.toNat]'hi))
          && decide ((v.val[index.toNat]'hi) ≤ (243 : u8))) = true := by
        rw [h_ge_241, h_le_243]; rfl
      have h_b2_range : 128 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                        (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 191 := by
        rcases h_sbo' with ⟨hf, _, _⟩ | ⟨h1', _, _, _⟩ | ⟨hf, _, _⟩ | ⟨h1', _, _, _⟩
                         | ⟨hf, _, _⟩ | ⟨_, _, ha, hb⟩ | ⟨hf, _, _⟩
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exact ⟨ha, hb⟩
        · exfalso; omega
      have h_and_true := b2_and_true (128 : u8) (191 : u8) 128 191 u8_128_toNat u8_191_toNat
                                      h_b2_range.1 h_b2_range.2
      simp only [h_beq_F0_false, Bool.false_eq_true, ↓reduceIte,
                 h_outer_and_true, h_and_true, Bool.not_true,
                 h_add_i2, RustM_ok_bind, h_cond_i2_ge, h_idx2, h_b3_bne,
                 h_add_i3, h_cond_i3_ge]
      rfl
    · have h_chain_false :
          (decide ((241 : u8) ≤ (v.val[index.toNat]'hi))
          && decide ((v.val[index.toNat]'hi) ≤ (243 : u8))) = false := by
        rw [Bool.and_eq_false_iff]
        rcases Classical.em (241 ≤ (v.val[index.toNat]'hi).toNat) with ha | ha
        · right; rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, u8_243_toNat]
          intro hb; exact h_F1_F3 ⟨ha, hb⟩
        · left; rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, u8_241_toNat]; exact ha
      have h_F4 : (v.val[index.toNat]'hi).toNat = 244 := by
        rcases Nat.lt_or_ge (v.val[index.toNat]'hi).toNat 241 with h_lt | h_ge
        · exfalso; apply h_F0; omega
        · rcases Nat.lt_or_ge (v.val[index.toNat]'hi).toNat 244 with h_lt' | h_ge'
          · exfalso; apply h_F1_F3; exact ⟨h_ge, by omega⟩
          · omega
      have h_first_eq : (v.val[index.toNat]'hi) = (244 : u8) :=
        UInt8.toNat_inj.mp (h_F4.trans u8_244_toNat.symm)
      have h_beq_F4 : ((v.val[index.toNat]'hi) == (244 : u8)) = true := by
        rw [beq_iff_eq]; exact h_first_eq
      have h_b2_range : 128 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                        (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 143 := by
        rcases h_sbo' with ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩ | ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩
                         | ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩ | ⟨_, ha, hb⟩
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exact ⟨ha, hb⟩
      have h_and_true := b2_and_true (128 : u8) (143 : u8) 128 143 u8_128_toNat u8_143_toNat
                                      h_b2_range.1 h_b2_range.2
      simp only [h_beq_F0_false, Bool.false_eq_true, ↓reduceIte, h_chain_false,
                 h_beq_F4, h_and_true, Bool.not_true,
                 h_add_i2, RustM_ok_bind, h_cond_i2_ge, h_idx2, h_b3_bne,
                 h_add_i3, h_cond_i3_ge]
      rfl

/-- Width-4 bad continuation at i3: b3 cont, ¬IsContByte b4 ⇒ Err Some 3. -/
private theorem validate_at_w4_bad_cont2 (v : RustSlice u8) (index : usize)
    (hi : index.toNat < v.val.size)
    (h_lo : 240 ≤ (v.val[index.toNat]'hi).toNat)
    (h_hi : (v.val[index.toNat]'hi).toNat < 245)
    (hi1 : index.toNat + 1 < v.val.size)
    (h_sbo : SecondByteOk (v.val[index.toNat]'hi) (v.val[index.toNat + 1]'hi1))
    (hi2 : index.toNat + 2 < v.val.size)
    (h_cont2 : IsContByte (v.val[index.toNat + 2]'hi2))
    (hi3 : index.toNat + 3 < v.val.size)
    (h_bad : ¬ IsContByte (v.val[index.toNat + 3]'hi3)) :
    run_utf8_validation_u8.validate_at v index =
      RustM.ok (core_models.result.Result.Err
        (run_utf8_validation_u8.Utf8Error.mk
          (valid_up_to := index)
          (error_len := core_models.option.Option.Some (3 : u8)))) := by
  rw [validate_at_w4_unfold v index hi h_lo h_hi]
  have h_size_lt : v.val.size < 2^64 := v.size_lt_usizeSize
  have h_no_ov : index.toNat + 1 < 2^64 := by omega
  have h_add := usize_add_one_ok index h_no_ov
  have h_i1_toNat : (index + 1).toNat = index.toNat + 1 := usize_add_one_toNat _ h_no_ov
  have h_add_i2 := usize_add_one_ok (index + 1) (by rw [h_i1_toNat]; omega)
  have h_i2_toNat : (index + 1 + 1).toNat = index.toNat + 2 := by
    rw [usize_add_one_toNat (index + 1) (by rw [h_i1_toNat]; omega), h_i1_toNat]
  have h_add_i3 := usize_add_one_ok (index + 1 + 1) (by rw [h_i2_toNat]; omega)
  have h_i3_toNat : (index + 1 + 1 + 1).toNat = index.toNat + 3 := by
    rw [usize_add_one_toNat (index + 1 + 1) (by rw [h_i2_toNat]; omega), h_i2_toNat]
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat v.val.size ≤ index + 1) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat, h_i1_toNat]; omega
  have h_cond_ge : decide (index + 1 ≥ USize64.ofNat v.val.size) = false := h_cond
  have h_cond_i2 : decide (USize64.ofNat v.val.size ≤ index + 1 + 1) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat, h_i2_toNat]; omega
  have h_cond_i2_ge : decide (index + 1 + 1 ≥ USize64.ofNat v.val.size) = false := h_cond_i2
  have h_cond_i3 : decide (USize64.ofNat v.val.size ≤ index + 1 + 1 + 1) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat, h_i3_toNat]; omega
  have h_cond_i3_ge : decide (index + 1 + 1 + 1 ≥ USize64.ofNat v.val.size) = false := h_cond_i3
  have hi1_take : (index + 1).toNat < v.val.size := by rw [h_i1_toNat]; exact hi1
  have hi2_take : (index + 1 + 1).toNat < v.val.size := by rw [h_i2_toNat]; exact hi2
  have hi3_take : (index + 1 + 1 + 1).toNat < v.val.size := by rw [h_i3_toNat]; exact hi3
  have h_idx : (v[index + 1]_? : RustM u8) = RustM.ok (v.val[(index + 1).toNat]'hi1_take) :=
    getElem_ok v (index + 1) hi1_take
  have h_idx2 : (v[index + 1 + 1]_? : RustM u8) = RustM.ok (v.val[(index + 1 + 1).toNat]'hi2_take) :=
    getElem_ok v (index + 1 + 1) hi2_take
  have h_idx3 : (v[index + 1 + 1 + 1]_? : RustM u8) =
                RustM.ok (v.val[(index + 1 + 1 + 1).toNat]'hi3_take) :=
    getElem_ok v (index + 1 + 1 + 1) hi3_take
  have h_eq_get : v.val[(index + 1).toNat]'hi1_take = v.val[index.toNat + 1]'hi1 := by congr 1
  have h_eq_get2 : v.val[(index + 1 + 1).toNat]'hi2_take = v.val[index.toNat + 2]'hi2 := by congr 1
  have h_eq_get3 : v.val[(index + 1 + 1 + 1).toNat]'hi3_take = v.val[index.toNat + 3]'hi3 := by congr 1
  have h_sbo' : SecondByteOk (v.val[index.toNat]'hi) (v.val[(index + 1).toNat]'hi1_take) := by
    rw [h_eq_get]; exact h_sbo
  have h_cont2' : IsContByte (v.val[(index + 1 + 1).toNat]'hi2_take) := by
    rw [h_eq_get2]; exact h_cont2
  have h_bad' : ¬ IsContByte (v.val[(index + 1 + 1 + 1).toNat]'hi3_take) := by
    rw [h_eq_get3]; exact h_bad
  have h_b3_bne : ((v.val[(index + 1 + 1).toNat]'hi2_take) &&& (192 : u8) != (128 : u8)) = false := by
    rw [bne_eq_false_iff_eq]; exact (cont_byte_iff _).mpr h_cont2'
  have h_b4_bne : ((v.val[(index + 1 + 1 + 1).toNat]'hi3_take) &&& (192 : u8) != (128 : u8)) = true := by
    apply bne_iff_ne.mpr; intro h_eq
    exact h_bad' ((cont_byte_iff _).mp h_eq)
  simp only [h_add, RustM_ok_bind, ↓reduceIte, h_idx,
             rust_primitives.cmp.eq, rust_primitives.cmp.ge, rust_primitives.cmp.le,
             rust_primitives.cmp.ne, rust_primitives.hax.logical_op.and,
             rust_primitives.hax.logical_op.not, pure_bind,
             h_cond_ge, Bool.false_eq_true]
  have b2_and_true : ∀ (lo hi : u8) (lo_nat hi_nat : Nat),
      lo.toNat = lo_nat → hi.toNat = hi_nat →
      lo_nat ≤ (v.val[(index + 1).toNat]'hi1_take).toNat →
      (v.val[(index + 1).toNat]'hi1_take).toNat ≤ hi_nat →
      (decide (lo ≤ (v.val[(index + 1).toNat]'hi1_take)) &&
       decide ((v.val[(index + 1).toNat]'hi1_take) ≤ hi)) = true := by
    intro lo hi lo_nat hi_nat h_lo_n h_hi_n h_ge_lo h_le_hi
    have h_d1 : decide (lo ≤ (v.val[(index + 1).toNat]'hi1_take)) = true := by
      rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, h_lo_n]; exact h_ge_lo
    have h_d2 : decide ((v.val[(index + 1).toNat]'hi1_take) ≤ hi) = true := by
      rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, h_hi_n]; exact h_le_hi
    rw [h_d1, h_d2]; rfl
  by_cases h_F0 : (v.val[index.toNat]'hi).toNat = 240
  · have h_first_eq : (v.val[index.toNat]'hi) = (240 : u8) :=
      UInt8.toNat_inj.mp (h_F0.trans u8_240_toNat.symm)
    have h_beq : ((v.val[index.toNat]'hi) == (240 : u8)) = true := by
      rw [beq_iff_eq]; exact h_first_eq
    have h_b2_range : 144 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                      (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 191 := by
      rcases h_sbo' with ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩ | ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩
                       | ⟨_, ha, hb⟩ | ⟨h1, _, _, _⟩ | ⟨hf, _, _⟩
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exact ⟨ha, hb⟩
      · exfalso; omega
      · exfalso; omega
    have h_and_true := b2_and_true (144 : u8) (191 : u8) 144 191 u8_144_toNat u8_191_toNat
                                    h_b2_range.1 h_b2_range.2
    simp only [h_beq, ↓reduceIte, h_and_true, Bool.not_true, Bool.false_eq_true,
               h_add_i2, RustM_ok_bind, h_cond_i2_ge, h_idx2, h_b3_bne,
               h_add_i3, h_cond_i3_ge, h_idx3, h_b4_bne]
    rfl
  · have h_beq_F0_false : ((v.val[index.toNat]'hi) == (240 : u8)) = false := by
      rw [beq_eq_false_iff_ne]; intro h; apply h_F0; rw [h]; exact u8_240_toNat
    by_cases h_F1_F3 : 241 ≤ (v.val[index.toNat]'hi).toNat ∧ (v.val[index.toNat]'hi).toNat ≤ 243
    · obtain ⟨h1, h2⟩ := h_F1_F3
      have h_ge_241 : decide ((241 : u8) ≤ (v.val[index.toNat]'hi)) = true := by
        rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_241_toNat]; exact h1
      have h_le_243 : decide ((v.val[index.toNat]'hi) ≤ (243 : u8)) = true := by
        rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_243_toNat]; exact h2
      have h_outer_and_true : (decide ((241 : u8) ≤ (v.val[index.toNat]'hi))
          && decide ((v.val[index.toNat]'hi) ≤ (243 : u8))) = true := by
        rw [h_ge_241, h_le_243]; rfl
      have h_b2_range : 128 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                        (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 191 := by
        rcases h_sbo' with ⟨hf, _, _⟩ | ⟨h1', _, _, _⟩ | ⟨hf, _, _⟩ | ⟨h1', _, _, _⟩
                         | ⟨hf, _, _⟩ | ⟨_, _, ha, hb⟩ | ⟨hf, _, _⟩
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exact ⟨ha, hb⟩
        · exfalso; omega
      have h_and_true := b2_and_true (128 : u8) (191 : u8) 128 191 u8_128_toNat u8_191_toNat
                                      h_b2_range.1 h_b2_range.2
      simp only [h_beq_F0_false, Bool.false_eq_true, ↓reduceIte,
                 h_outer_and_true, h_and_true, Bool.not_true,
                 h_add_i2, RustM_ok_bind, h_cond_i2_ge, h_idx2, h_b3_bne,
                 h_add_i3, h_cond_i3_ge, h_idx3, h_b4_bne]
      rfl
    · have h_chain_false :
          (decide ((241 : u8) ≤ (v.val[index.toNat]'hi))
          && decide ((v.val[index.toNat]'hi) ≤ (243 : u8))) = false := by
        rw [Bool.and_eq_false_iff]
        rcases Classical.em (241 ≤ (v.val[index.toNat]'hi).toNat) with ha | ha
        · right; rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, u8_243_toNat]
          intro hb; exact h_F1_F3 ⟨ha, hb⟩
        · left; rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, u8_241_toNat]; exact ha
      have h_F4 : (v.val[index.toNat]'hi).toNat = 244 := by
        rcases Nat.lt_or_ge (v.val[index.toNat]'hi).toNat 241 with h_lt | h_ge
        · exfalso; apply h_F0; omega
        · rcases Nat.lt_or_ge (v.val[index.toNat]'hi).toNat 244 with h_lt' | h_ge'
          · exfalso; apply h_F1_F3; exact ⟨h_ge, by omega⟩
          · omega
      have h_first_eq : (v.val[index.toNat]'hi) = (244 : u8) :=
        UInt8.toNat_inj.mp (h_F4.trans u8_244_toNat.symm)
      have h_beq_F4 : ((v.val[index.toNat]'hi) == (244 : u8)) = true := by
        rw [beq_iff_eq]; exact h_first_eq
      have h_b2_range : 128 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                        (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 143 := by
        rcases h_sbo' with ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩ | ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩
                         | ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩ | ⟨_, ha, hb⟩
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exact ⟨ha, hb⟩
      have h_and_true := b2_and_true (128 : u8) (143 : u8) 128 143 u8_128_toNat u8_143_toNat
                                      h_b2_range.1 h_b2_range.2
      simp only [h_beq_F0_false, Bool.false_eq_true, ↓reduceIte, h_chain_false,
                 h_beq_F4, h_and_true, Bool.not_true,
                 h_add_i2, RustM_ok_bind, h_cond_i2_ge, h_idx2, h_b3_bne,
                 h_add_i3, h_cond_i3_ge, h_idx3, h_b4_bne]
      rfl

/-- Width-4 recurse: b3 cont, b4 cont ⇒ recurse with i3 + 1. -/
private theorem validate_at_w4_recurse (v : RustSlice u8) (index : usize)
    (hi : index.toNat < v.val.size)
    (h_lo : 240 ≤ (v.val[index.toNat]'hi).toNat)
    (h_hi : (v.val[index.toNat]'hi).toNat < 245)
    (hi1 : index.toNat + 1 < v.val.size)
    (h_sbo : SecondByteOk (v.val[index.toNat]'hi) (v.val[index.toNat + 1]'hi1))
    (hi2 : index.toNat + 2 < v.val.size)
    (h_cont2 : IsContByte (v.val[index.toNat + 2]'hi2))
    (hi3 : index.toNat + 3 < v.val.size)
    (h_cont3 : IsContByte (v.val[index.toNat + 3]'hi3)) :
    run_utf8_validation_u8.validate_at v index =
      run_utf8_validation_u8.validate_at v (index + 1 + 1 + 1 + 1) := by
  rw [validate_at_w4_unfold v index hi h_lo h_hi]
  have h_size_lt : v.val.size < 2^64 := v.size_lt_usizeSize
  have h_no_ov : index.toNat + 1 < 2^64 := by omega
  have h_add := usize_add_one_ok index h_no_ov
  have h_i1_toNat : (index + 1).toNat = index.toNat + 1 := usize_add_one_toNat _ h_no_ov
  have h_add_i2 := usize_add_one_ok (index + 1) (by rw [h_i1_toNat]; omega)
  have h_i2_toNat : (index + 1 + 1).toNat = index.toNat + 2 := by
    rw [usize_add_one_toNat (index + 1) (by rw [h_i1_toNat]; omega), h_i1_toNat]
  have h_add_i3 := usize_add_one_ok (index + 1 + 1) (by rw [h_i2_toNat]; omega)
  have h_i3_toNat : (index + 1 + 1 + 1).toNat = index.toNat + 3 := by
    rw [usize_add_one_toNat (index + 1 + 1) (by rw [h_i2_toNat]; omega), h_i2_toNat]
  have h_add_i4 := usize_add_one_ok (index + 1 + 1 + 1) (by rw [h_i3_toNat]; omega)
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat v.val.size ≤ index + 1) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat, h_i1_toNat]; omega
  have h_cond_ge : decide (index + 1 ≥ USize64.ofNat v.val.size) = false := h_cond
  have h_cond_i2 : decide (USize64.ofNat v.val.size ≤ index + 1 + 1) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat, h_i2_toNat]; omega
  have h_cond_i2_ge : decide (index + 1 + 1 ≥ USize64.ofNat v.val.size) = false := h_cond_i2
  have h_cond_i3 : decide (USize64.ofNat v.val.size ≤ index + 1 + 1 + 1) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat, h_i3_toNat]; omega
  have h_cond_i3_ge : decide (index + 1 + 1 + 1 ≥ USize64.ofNat v.val.size) = false := h_cond_i3
  have hi1_take : (index + 1).toNat < v.val.size := by rw [h_i1_toNat]; exact hi1
  have hi2_take : (index + 1 + 1).toNat < v.val.size := by rw [h_i2_toNat]; exact hi2
  have hi3_take : (index + 1 + 1 + 1).toNat < v.val.size := by rw [h_i3_toNat]; exact hi3
  have h_idx : (v[index + 1]_? : RustM u8) = RustM.ok (v.val[(index + 1).toNat]'hi1_take) :=
    getElem_ok v (index + 1) hi1_take
  have h_idx2 : (v[index + 1 + 1]_? : RustM u8) = RustM.ok (v.val[(index + 1 + 1).toNat]'hi2_take) :=
    getElem_ok v (index + 1 + 1) hi2_take
  have h_idx3 : (v[index + 1 + 1 + 1]_? : RustM u8) =
                RustM.ok (v.val[(index + 1 + 1 + 1).toNat]'hi3_take) :=
    getElem_ok v (index + 1 + 1 + 1) hi3_take
  have h_eq_get : v.val[(index + 1).toNat]'hi1_take = v.val[index.toNat + 1]'hi1 := by congr 1
  have h_eq_get2 : v.val[(index + 1 + 1).toNat]'hi2_take = v.val[index.toNat + 2]'hi2 := by congr 1
  have h_eq_get3 : v.val[(index + 1 + 1 + 1).toNat]'hi3_take = v.val[index.toNat + 3]'hi3 := by congr 1
  have h_sbo' : SecondByteOk (v.val[index.toNat]'hi) (v.val[(index + 1).toNat]'hi1_take) := by
    rw [h_eq_get]; exact h_sbo
  have h_cont2' : IsContByte (v.val[(index + 1 + 1).toNat]'hi2_take) := by
    rw [h_eq_get2]; exact h_cont2
  have h_cont3' : IsContByte (v.val[(index + 1 + 1 + 1).toNat]'hi3_take) := by
    rw [h_eq_get3]; exact h_cont3
  have h_b3_bne : ((v.val[(index + 1 + 1).toNat]'hi2_take) &&& (192 : u8) != (128 : u8)) = false := by
    rw [bne_eq_false_iff_eq]; exact (cont_byte_iff _).mpr h_cont2'
  have h_b4_bne : ((v.val[(index + 1 + 1 + 1).toNat]'hi3_take) &&& (192 : u8) != (128 : u8)) = false := by
    rw [bne_eq_false_iff_eq]; exact (cont_byte_iff _).mpr h_cont3'
  simp only [h_add, RustM_ok_bind, ↓reduceIte, h_idx,
             rust_primitives.cmp.eq, rust_primitives.cmp.ge, rust_primitives.cmp.le,
             rust_primitives.cmp.ne, rust_primitives.hax.logical_op.and,
             rust_primitives.hax.logical_op.not, pure_bind,
             h_cond_ge, Bool.false_eq_true]
  have b2_and_true : ∀ (lo hi : u8) (lo_nat hi_nat : Nat),
      lo.toNat = lo_nat → hi.toNat = hi_nat →
      lo_nat ≤ (v.val[(index + 1).toNat]'hi1_take).toNat →
      (v.val[(index + 1).toNat]'hi1_take).toNat ≤ hi_nat →
      (decide (lo ≤ (v.val[(index + 1).toNat]'hi1_take)) &&
       decide ((v.val[(index + 1).toNat]'hi1_take) ≤ hi)) = true := by
    intro lo hi lo_nat hi_nat h_lo_n h_hi_n h_ge_lo h_le_hi
    have h_d1 : decide (lo ≤ (v.val[(index + 1).toNat]'hi1_take)) = true := by
      rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, h_lo_n]; exact h_ge_lo
    have h_d2 : decide ((v.val[(index + 1).toNat]'hi1_take) ≤ hi) = true := by
      rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, h_hi_n]; exact h_le_hi
    rw [h_d1, h_d2]; rfl
  by_cases h_F0 : (v.val[index.toNat]'hi).toNat = 240
  · have h_first_eq : (v.val[index.toNat]'hi) = (240 : u8) :=
      UInt8.toNat_inj.mp (h_F0.trans u8_240_toNat.symm)
    have h_beq : ((v.val[index.toNat]'hi) == (240 : u8)) = true := by
      rw [beq_iff_eq]; exact h_first_eq
    have h_b2_range : 144 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                      (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 191 := by
      rcases h_sbo' with ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩ | ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩
                       | ⟨_, ha, hb⟩ | ⟨h1, _, _, _⟩ | ⟨hf, _, _⟩
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exact ⟨ha, hb⟩
      · exfalso; omega
      · exfalso; omega
    have h_and_true := b2_and_true (144 : u8) (191 : u8) 144 191 u8_144_toNat u8_191_toNat
                                    h_b2_range.1 h_b2_range.2
    simp only [h_beq, ↓reduceIte, h_and_true, Bool.not_true, Bool.false_eq_true,
               h_add_i2, RustM_ok_bind, h_cond_i2_ge, h_idx2, h_b3_bne,
               h_add_i3, h_cond_i3_ge, h_idx3, h_b4_bne, h_add_i4]
  · have h_beq_F0_false : ((v.val[index.toNat]'hi) == (240 : u8)) = false := by
      rw [beq_eq_false_iff_ne]; intro h; apply h_F0; rw [h]; exact u8_240_toNat
    by_cases h_F1_F3 : 241 ≤ (v.val[index.toNat]'hi).toNat ∧ (v.val[index.toNat]'hi).toNat ≤ 243
    · obtain ⟨h1, h2⟩ := h_F1_F3
      have h_ge_241 : decide ((241 : u8) ≤ (v.val[index.toNat]'hi)) = true := by
        rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_241_toNat]; exact h1
      have h_le_243 : decide ((v.val[index.toNat]'hi) ≤ (243 : u8)) = true := by
        rw [decide_eq_true_iff, UInt8.le_iff_toNat_le, u8_243_toNat]; exact h2
      have h_outer_and_true : (decide ((241 : u8) ≤ (v.val[index.toNat]'hi))
          && decide ((v.val[index.toNat]'hi) ≤ (243 : u8))) = true := by
        rw [h_ge_241, h_le_243]; rfl
      have h_b2_range : 128 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                        (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 191 := by
        rcases h_sbo' with ⟨hf, _, _⟩ | ⟨h1', _, _, _⟩ | ⟨hf, _, _⟩ | ⟨h1', _, _, _⟩
                         | ⟨hf, _, _⟩ | ⟨_, _, ha, hb⟩ | ⟨hf, _, _⟩
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exact ⟨ha, hb⟩
        · exfalso; omega
      have h_and_true := b2_and_true (128 : u8) (191 : u8) 128 191 u8_128_toNat u8_191_toNat
                                      h_b2_range.1 h_b2_range.2
      simp only [h_beq_F0_false, Bool.false_eq_true, ↓reduceIte,
                 h_outer_and_true, h_and_true, Bool.not_true,
                 h_add_i2, RustM_ok_bind, h_cond_i2_ge, h_idx2, h_b3_bne,
                 h_add_i3, h_cond_i3_ge, h_idx3, h_b4_bne, h_add_i4]
    · have h_chain_false :
          (decide ((241 : u8) ≤ (v.val[index.toNat]'hi))
          && decide ((v.val[index.toNat]'hi) ≤ (243 : u8))) = false := by
        rw [Bool.and_eq_false_iff]
        rcases Classical.em (241 ≤ (v.val[index.toNat]'hi).toNat) with ha | ha
        · right; rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, u8_243_toNat]
          intro hb; exact h_F1_F3 ⟨ha, hb⟩
        · left; rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le, u8_241_toNat]; exact ha
      have h_F4 : (v.val[index.toNat]'hi).toNat = 244 := by
        rcases Nat.lt_or_ge (v.val[index.toNat]'hi).toNat 241 with h_lt | h_ge
        · exfalso; apply h_F0; omega
        · rcases Nat.lt_or_ge (v.val[index.toNat]'hi).toNat 244 with h_lt' | h_ge'
          · exfalso; apply h_F1_F3; exact ⟨h_ge, by omega⟩
          · omega
      have h_first_eq : (v.val[index.toNat]'hi) = (244 : u8) :=
        UInt8.toNat_inj.mp (h_F4.trans u8_244_toNat.symm)
      have h_beq_F4 : ((v.val[index.toNat]'hi) == (244 : u8)) = true := by
        rw [beq_iff_eq]; exact h_first_eq
      have h_b2_range : 128 ≤ (v.val[(index + 1).toNat]'hi1_take).toNat ∧
                        (v.val[(index + 1).toNat]'hi1_take).toNat ≤ 143 := by
        rcases h_sbo' with ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩ | ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩
                         | ⟨hf, _, _⟩ | ⟨h1, _, _, _⟩ | ⟨_, ha, hb⟩
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exact ⟨ha, hb⟩
      have h_and_true := b2_and_true (128 : u8) (143 : u8) 128 143 u8_128_toNat u8_143_toNat
                                      h_b2_range.1 h_b2_range.2
      simp only [h_beq_F0_false, Bool.false_eq_true, ↓reduceIte, h_chain_false,
                 h_beq_F4, h_and_true, Bool.not_true,
                 h_add_i2, RustM_ok_bind, h_cond_i2_ge, h_idx2, h_b3_bne,
                 h_add_i3, h_cond_i3_ge, h_idx3, h_b4_bne, h_add_i4]

/-- **Partial completion.** This master lemma is proved by strong induction on
    `v.val.size - index.toNat` and an 18-way case analysis matching the branch
    structure of `validate_at` (OOB, ASCII, w0-small, w0-large, plus the
    truncation/bad-byte/recurse triad for w2 and the 5- and 7-way splits for
    w3 and w4). I tried this proof and could not finish the w3 and w4 sub-cases
    in the time available.

    **Completed in this file (closed proofs, available to future iterations):**
      * OOB / ASCII / w0-small / w0-large / w2 sub-cases in the master below.
      * `w3_ok2_eq` (the hard helper for w3 — equates the ok2 byte-range chain
        with `decide (SecondByteOk first b2)` under `224 ≤ first.toNat < 240`).
      * `validate_at_w3_trunc1` (one of the five w3 leaf step lemmas).
      * `secondByteOk_w3_explicit`, `secondByteOk_w4_explicit` (helpers for w4
        will need similar reasoning).
      * All `validate_at_w3_unfold` / `validate_at_w4_unfold` step lemmas, the
        eight `isValidUtf8From_w3_*` / `isValidUtf8From_w4_*` step lemmas, and
        the `prefix_valid_back_{w3,w4}` helpers.

    **What remains (mechanical glue, ~1000 lines of tactic):**
      * `validate_at_w3_{bad_b2,trunc2,bad_cont,recurse}` — four leaf step lemmas
        that combine `validate_at_w3_unfold` + `w3_ok2_eq` with the appropriate
        outer-condition reductions.
      * A `w4_ok2_eq` helper analogous to `w3_ok2_eq` (3-disjunct case analysis
        instead of 4).
      * Six `validate_at_w4_*` leaf step lemmas.
      * w3 master sub-case (uses 5 w3 leaf step lemmas).
      * w4 master sub-case (uses 7 w4 leaf step lemmas).

    **The unresolved tactic obstacle (for a future iteration to navigate):**
    `simp only [..., rust_primitives.cmp.ge, ..., h_ok2, ...]` does not apply
    `w3_ok2_eq` because the `rust_primitives.cmp.ge` simp lemma fires on the
    inner `>=? 160` / `>=? 225` / etc. occurrences inside the ok2 chain
    *before* `h_ok2` can match, altering the chain's shape and breaking the
    rewrite. The fix is to reduce the outer `(i1 >=? size)` check via a
    targeted rewrite (e.g. a `rust_ge_pure` `rfl` lemma) instead of including
    `rust_primitives.cmp.ge` in the simp set, then apply `rw [h_ok2]`
    explicitly before any further simp. I attempted this in several variants
    this turn; the leaf step lemmas were close to working but ran past the
    time budget.

    A future iteration *can* complete this; the gap is mechanical glue, not
    a missing lemma or impossibility. -/
private theorem validate_at_correct (v : RustSlice u8) :
    ∀ (m : Nat) (index : usize),
      v.val.size - index.toNat ≤ m →
      ∃ r, run_utf8_validation_u8.validate_at v index = RustM.ok r ∧
           ValidateAtSpec v index r := by
  intro m
  induction m with
  | zero =>
    intro index h_meas
    -- index ≥ size, OOB case.
    have hi_ge : v.val.size ≤ index.toNat := by omega
    refine ⟨_, validate_at_oob v index hi_ge, ?_⟩
    show isValidUtf8From v.val index.toNat = true
    exact isValidUtf8From_oob _ _ hi_ge
  | succ m ih =>
    intro index h_meas
    by_cases hi_ge : v.val.size ≤ index.toNat
    · -- OOB
      refine ⟨_, validate_at_oob v index hi_ge, ?_⟩
      show isValidUtf8From v.val index.toNat = true
      exact isValidUtf8From_oob _ _ hi_ge
    · have hi_lt : index.toNat < v.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : v.val.size < 2^64 := v.size_lt_usizeSize
      have h_no_ov_i1 : index.toNat + 1 < 2^64 := by omega
      have h_i1_toNat : (index + 1).toNat = index.toNat + 1 :=
        usize_add_one_toNat _ h_no_ov_i1
      have h_meas_i1 : v.val.size - (index + 1).toNat ≤ m := by
        rw [h_i1_toNat]; omega
      -- Case on byte value first = v.val[index.toNat].
      by_cases h_ascii : (v.val[index.toNat]'hi_lt).toNat < 128
      · -- ASCII case: recurse +1.
        have h_step := validate_at_ascii v index hi_lt h_ascii
        obtain ⟨r, h_eq, h_spec⟩ := ih (index + 1) h_meas_i1
        refine ⟨r, by rw [h_step]; exact h_eq, ?_⟩
        unfold ValidateAtSpec at h_spec ⊢
        cases r with
        | Ok _ =>
          rw [isValidUtf8From_ascii v.val index.toNat hi_lt h_ascii]
          rw [h_i1_toNat] at h_spec
          exact h_spec
        | Err err =>
          obtain ⟨h_false, h_lo, h_hi, h_prefix, h_some, h_none⟩ := h_spec
          rw [h_i1_toNat] at h_lo h_prefix h_false
          refine ⟨?_, by omega, h_hi, ?_, h_some, h_none⟩
          · rw [isValidUtf8From_ascii v.val index.toNat hi_lt h_ascii]; exact h_false
          · exact prefix_valid_back_ascii v index err.valid_up_to.toNat hi_lt h_ascii
                    (by omega) h_hi h_prefix
      · -- first ≥ 128
        have h_ge_128 : 128 ≤ (v.val[index.toNat]'hi_lt).toNat := Nat.le_of_not_lt h_ascii
        by_cases h_w0_small : (v.val[index.toNat]'hi_lt).toNat < 194
        · -- 128 ≤ first < 194: width 0
          refine ⟨_, validate_at_w0 v index hi_lt (Or.inl ⟨h_ge_128, h_w0_small⟩), ?_⟩
          show isValidUtf8From v.val index.toNat = false ∧ _
          have h_lw : leadWidth (v.val[index.toNat]'hi_lt) = 0 := by
            unfold leadWidth
            rw [if_neg (by omega), if_pos h_w0_small]
          refine ⟨isValidUtf8From_invalid v.val index.toNat hi_lt h_lw,
                  Nat.le_refl _, Nat.le_of_lt hi_lt,
                  prefix_at_self v.val index.toNat (Nat.le_of_lt hi_lt), ?_, ?_⟩
          · intro n hn
            injection hn with hn_eq
            subst hn_eq
            refine ⟨by decide, by decide, ?_⟩
            show index.toNat + (1 : u8).toNat ≤ v.val.size
            have : (1 : u8).toNat = 1 := by decide
            rw [this]; omega
          · intro hn_none
            exact (by cases hn_none)
        · -- 194 ≤ first
          have h_ge_194 : 194 ≤ (v.val[index.toNat]'hi_lt).toNat := Nat.le_of_not_lt h_w0_small
          by_cases h_w2 : (v.val[index.toNat]'hi_lt).toNat < 224
          · -- 194 ≤ first < 224: width 2
            by_cases h_trunc : v.val.size ≤ index.toNat + 1
            · -- truncation
              refine ⟨_, validate_at_w2_trunc v index hi_lt h_ge_194 h_w2 h_trunc, ?_⟩
              unfold ValidateAtSpec
              have h_lw : leadWidth (v.val[index.toNat]'hi_lt) = 2 := by
                unfold leadWidth
                rw [if_neg (by omega : ¬ (v.val[index.toNat]'hi_lt).toNat < 128)]
                rw [if_neg (by omega : ¬ (v.val[index.toNat]'hi_lt).toNat < 194)]
                rw [if_pos h_w2]
              refine ⟨isValidUtf8From_w2_trunc v.val index.toNat hi_lt h_lw h_trunc,
                      Nat.le_refl _, Nat.le_of_lt hi_lt,
                      prefix_at_self v.val index.toNat (Nat.le_of_lt hi_lt), ?_, ?_⟩
              · intro n hn
                exact (by cases hn)
              · intro _
                refine ⟨hi_lt, ?_, ?_⟩
                · rw [h_lw]; exact Nat.le_refl 2
                · rw [h_lw]
                  show v.val.size - index.toNat < 2
                  omega
            · -- i1 < size
              have hi1 : index.toNat + 1 < v.val.size := by omega
              by_cases h_cont : IsContByte (v.val[index.toNat + 1]'hi1)
              · -- recurse case
                have h_no_ov_i2 : index.toNat + 2 < 2^64 := by omega
                have h_step := validate_at_w2_recurse v index hi_lt h_ge_194 h_w2 hi1 h_cont
                have h_i1_toNat : (index + 1).toNat = index.toNat + 1 :=
                  usize_add_one_toNat _ h_no_ov_i1
                have h_no_ov_i2' : (index + 1).toNat + 1 < 2^64 := by rw [h_i1_toNat]; omega
                have h_i2_toNat : (index + 1 + 1).toNat = index.toNat + 2 := by
                  rw [usize_add_one_toNat (index + 1) h_no_ov_i2', h_i1_toNat]
                have h_meas_i2 : v.val.size - (index + 1 + 1).toNat ≤ m := by
                  rw [h_i2_toNat]; omega
                obtain ⟨r, h_eq, h_spec⟩ := ih (index + 1 + 1) h_meas_i2
                refine ⟨r, by rw [h_step]; exact h_eq, ?_⟩
                unfold ValidateAtSpec at h_spec ⊢
                have h_lw : leadWidth (v.val[index.toNat]'hi_lt) = 2 := by
                  unfold leadWidth
                  rw [if_neg (by omega : ¬ (v.val[index.toNat]'hi_lt).toNat < 128)]
                  rw [if_neg (by omega : ¬ (v.val[index.toNat]'hi_lt).toNat < 194)]
                  rw [if_pos h_w2]
                cases r with
                | Ok _ =>
                  rw [isValidUtf8From_w2_ok v.val index.toNat hi_lt h_lw hi1 h_cont]
                  rw [h_i2_toNat] at h_spec
                  exact h_spec
                | Err err =>
                  obtain ⟨h_false, h_lo, h_hi, h_prefix, h_some, h_none⟩ := h_spec
                  rw [h_i2_toNat] at h_lo h_prefix h_false
                  refine ⟨?_, by omega, h_hi, ?_, h_some, h_none⟩
                  · rw [isValidUtf8From_w2_ok v.val index.toNat hi_lt h_lw hi1 h_cont]
                    exact h_false
                  · exact prefix_valid_back_w2 v index err.valid_up_to.toNat hi_lt
                            h_ge_194 h_w2 hi1 h_cont (by omega) h_hi h_prefix
              · -- bad continuation
                refine ⟨_, validate_at_w2_bad_cont v index hi_lt h_ge_194 h_w2 hi1 h_cont, ?_⟩
                unfold ValidateAtSpec
                have h_lw : leadWidth (v.val[index.toNat]'hi_lt) = 2 := by
                  unfold leadWidth
                  rw [if_neg (by omega : ¬ (v.val[index.toNat]'hi_lt).toNat < 128)]
                  rw [if_neg (by omega : ¬ (v.val[index.toNat]'hi_lt).toNat < 194)]
                  rw [if_pos h_w2]
                refine ⟨isValidUtf8From_w2_bad v.val index.toNat hi_lt h_lw hi1 h_cont,
                        Nat.le_refl _, Nat.le_of_lt hi_lt,
                        prefix_at_self v.val index.toNat (Nat.le_of_lt hi_lt), ?_, ?_⟩
                · intro n hn
                  injection hn with hn_eq
                  subst hn_eq
                  refine ⟨by decide, by decide, ?_⟩
                  show index.toNat + (1 : u8).toNat ≤ v.val.size
                  have : (1 : u8).toNat = 1 := by decide
                  rw [this]; omega
                · intro hn_none
                  exact (by cases hn_none)
          · have h_ge_224 : 224 ≤ (v.val[index.toNat]'hi_lt).toNat := Nat.le_of_not_lt h_w2
            by_cases h_w3 : (v.val[index.toNat]'hi_lt).toNat < 240
            · -- 224 ≤ first < 240: width 3
              have h_lw : leadWidth (v.val[index.toNat]'hi_lt) = 3 := by
                unfold leadWidth
                rw [if_neg (by omega : ¬ (v.val[index.toNat]'hi_lt).toNat < 128)]
                rw [if_neg (by omega : ¬ (v.val[index.toNat]'hi_lt).toNat < 194)]
                rw [if_neg (by omega : ¬ (v.val[index.toNat]'hi_lt).toNat < 224)]
                rw [if_pos h_w3]
              by_cases h_trunc : v.val.size ≤ index.toNat + 1
              · -- trunc1
                refine ⟨_, validate_at_w3_trunc1 v index hi_lt h_ge_224 h_w3 h_trunc, ?_⟩
                unfold ValidateAtSpec
                refine ⟨isValidUtf8From_w3_trunc1 v.val index.toNat hi_lt h_lw h_trunc,
                        Nat.le_refl _, Nat.le_of_lt hi_lt,
                        prefix_at_self v.val index.toNat (Nat.le_of_lt hi_lt), ?_, ?_⟩
                · intro n hn; exact (by cases hn)
                · intro _; refine ⟨hi_lt, ?_, ?_⟩
                  · rw [h_lw]; omega
                  · rw [h_lw]; show v.val.size - index.toNat < 3; omega
              · have hi1 : index.toNat + 1 < v.val.size := by omega
                by_cases h_sbo : SecondByteOk (v.val[index.toNat]'hi_lt)
                                              (v.val[index.toNat + 1]'hi1)
                · -- SecondByteOk holds
                  by_cases h_trunc2 : v.val.size ≤ index.toNat + 2
                  · -- trunc2
                    refine ⟨_, validate_at_w3_trunc2 v index hi_lt h_ge_224 h_w3
                                hi1 h_sbo h_trunc2, ?_⟩
                    unfold ValidateAtSpec
                    refine ⟨isValidUtf8From_w3_trunc2 v.val index.toNat hi_lt h_lw hi1
                              h_sbo h_trunc2,
                            Nat.le_refl _, Nat.le_of_lt hi_lt,
                            prefix_at_self v.val index.toNat (Nat.le_of_lt hi_lt), ?_, ?_⟩
                    · intro n hn; exact (by cases hn)
                    · intro _; refine ⟨hi_lt, ?_, ?_⟩
                      · rw [h_lw]; omega
                      · rw [h_lw]; show v.val.size - index.toNat < 3; omega
                  · have hi2 : index.toNat + 2 < v.val.size := by omega
                    by_cases h_cont : IsContByte (v.val[index.toNat + 2]'hi2)
                    · -- recurse
                      have h_no_ov_i2' : (index + 1).toNat + 1 < 2^64 := by
                        rw [usize_add_one_toNat _ h_no_ov_i1]; omega
                      have h_i2_toNat : (index + 1 + 1).toNat = index.toNat + 2 := by
                        rw [usize_add_one_toNat (index + 1) h_no_ov_i2',
                            usize_add_one_toNat _ h_no_ov_i1]
                      have h_no_ov_i3' : (index + 1 + 1).toNat + 1 < 2^64 := by
                        rw [h_i2_toNat]; omega
                      have h_i3_toNat : (index + 1 + 1 + 1).toNat = index.toNat + 3 := by
                        rw [usize_add_one_toNat (index + 1 + 1) h_no_ov_i3', h_i2_toNat]
                      have h_meas_i3 : v.val.size - (index + 1 + 1 + 1).toNat ≤ m := by
                        rw [h_i3_toNat]; omega
                      have h_step := validate_at_w3_recurse v index hi_lt h_ge_224 h_w3
                                      hi1 h_sbo hi2 h_cont
                      obtain ⟨r, h_eq, h_spec⟩ := ih (index + 1 + 1 + 1) h_meas_i3
                      refine ⟨r, by rw [h_step]; exact h_eq, ?_⟩
                      unfold ValidateAtSpec at h_spec ⊢
                      cases r with
                      | Ok _ =>
                        rw [isValidUtf8From_w3_ok v.val index.toNat hi_lt h_lw hi1 h_sbo
                              hi2 h_cont]
                        rw [h_i3_toNat] at h_spec; exact h_spec
                      | Err err =>
                        obtain ⟨h_false, h_lo, h_hi, h_prefix, h_some, h_none⟩ := h_spec
                        rw [h_i3_toNat] at h_lo h_prefix h_false
                        refine ⟨?_, by omega, h_hi, ?_, h_some, h_none⟩
                        · rw [isValidUtf8From_w3_ok v.val index.toNat hi_lt h_lw hi1 h_sbo
                                hi2 h_cont]
                          exact h_false
                        · exact prefix_valid_back_w3 v index err.valid_up_to.toNat hi_lt
                                  h_ge_224 h_w3 hi1 h_sbo hi2 h_cont (by omega) h_hi h_prefix
                    · -- bad_cont
                      refine ⟨_, validate_at_w3_bad_cont v index hi_lt h_ge_224 h_w3
                                  hi1 h_sbo hi2 h_cont, ?_⟩
                      unfold ValidateAtSpec
                      refine ⟨isValidUtf8From_w3_bad_third v.val index.toNat hi_lt h_lw hi1
                                h_sbo hi2 h_cont,
                              Nat.le_refl _, Nat.le_of_lt hi_lt,
                              prefix_at_self v.val index.toNat (Nat.le_of_lt hi_lt), ?_, ?_⟩
                      · intro n hn
                        injection hn with hn_eq
                        subst hn_eq
                        refine ⟨by decide, by decide, ?_⟩
                        show index.toNat + (2 : u8).toNat ≤ v.val.size
                        have : (2 : u8).toNat = 2 := by decide
                        rw [this]; omega
                      · intro hn_none; exact (by cases hn_none)
                · -- ¬ SecondByteOk: bad_b2
                  refine ⟨_, validate_at_w3_bad_b2 v index hi_lt h_ge_224 h_w3 hi1 h_sbo, ?_⟩
                  unfold ValidateAtSpec
                  refine ⟨isValidUtf8From_w3_bad_second v.val index.toNat hi_lt h_lw hi1 h_sbo,
                          Nat.le_refl _, Nat.le_of_lt hi_lt,
                          prefix_at_self v.val index.toNat (Nat.le_of_lt hi_lt), ?_, ?_⟩
                  · intro n hn
                    injection hn with hn_eq
                    subst hn_eq
                    refine ⟨by decide, by decide, ?_⟩
                    show index.toNat + (1 : u8).toNat ≤ v.val.size
                    have : (1 : u8).toNat = 1 := by decide
                    rw [this]; omega
                  · intro hn_none; exact (by cases hn_none)
            · have h_ge_240 : 240 ≤ (v.val[index.toNat]'hi_lt).toNat := Nat.le_of_not_lt h_w3
              by_cases h_w4 : (v.val[index.toNat]'hi_lt).toNat < 245
              · -- 240 ≤ first < 245: width 4
                have h_lw : leadWidth (v.val[index.toNat]'hi_lt) = 4 := by
                  unfold leadWidth
                  rw [if_neg (by omega : ¬ (v.val[index.toNat]'hi_lt).toNat < 128)]
                  rw [if_neg (by omega : ¬ (v.val[index.toNat]'hi_lt).toNat < 194)]
                  rw [if_neg (by omega : ¬ (v.val[index.toNat]'hi_lt).toNat < 224)]
                  rw [if_neg (by omega : ¬ (v.val[index.toNat]'hi_lt).toNat < 240)]
                  rw [if_pos h_w4]
                by_cases h_trunc : v.val.size ≤ index.toNat + 1
                · -- trunc1
                  refine ⟨_, validate_at_w4_trunc1 v index hi_lt h_ge_240 h_w4 h_trunc, ?_⟩
                  unfold ValidateAtSpec
                  refine ⟨isValidUtf8From_w4_trunc1 v.val index.toNat hi_lt h_lw h_trunc,
                          Nat.le_refl _, Nat.le_of_lt hi_lt,
                          prefix_at_self v.val index.toNat (Nat.le_of_lt hi_lt), ?_, ?_⟩
                  · intro n hn; exact (by cases hn)
                  · intro _; refine ⟨hi_lt, ?_, ?_⟩
                    · rw [h_lw]; omega
                    · rw [h_lw]; show v.val.size - index.toNat < 4; omega
                · have hi1 : index.toNat + 1 < v.val.size := by omega
                  by_cases h_sbo : SecondByteOk (v.val[index.toNat]'hi_lt)
                                                (v.val[index.toNat + 1]'hi1)
                  · -- SecondByteOk holds
                    by_cases h_trunc2 : v.val.size ≤ index.toNat + 2
                    · -- trunc2
                      refine ⟨_, validate_at_w4_trunc2 v index hi_lt h_ge_240 h_w4
                                  hi1 h_sbo h_trunc2, ?_⟩
                      unfold ValidateAtSpec
                      refine ⟨isValidUtf8From_w4_trunc2 v.val index.toNat hi_lt h_lw hi1
                                h_sbo h_trunc2,
                              Nat.le_refl _, Nat.le_of_lt hi_lt,
                              prefix_at_self v.val index.toNat (Nat.le_of_lt hi_lt), ?_, ?_⟩
                      · intro n hn; exact (by cases hn)
                      · intro _; refine ⟨hi_lt, ?_, ?_⟩
                        · rw [h_lw]; omega
                        · rw [h_lw]; show v.val.size - index.toNat < 4; omega
                    · have hi2 : index.toNat + 2 < v.val.size := by omega
                      by_cases h_cont2 : IsContByte (v.val[index.toNat + 2]'hi2)
                      · -- b3 is cont
                        by_cases h_trunc3 : v.val.size ≤ index.toNat + 3
                        · -- trunc3
                          refine ⟨_, validate_at_w4_trunc3 v index hi_lt h_ge_240 h_w4
                                      hi1 h_sbo hi2 h_cont2 h_trunc3, ?_⟩
                          unfold ValidateAtSpec
                          refine ⟨isValidUtf8From_w4_trunc3 v.val index.toNat hi_lt h_lw hi1
                                    h_sbo hi2 h_cont2 h_trunc3,
                                  Nat.le_refl _, Nat.le_of_lt hi_lt,
                                  prefix_at_self v.val index.toNat (Nat.le_of_lt hi_lt), ?_, ?_⟩
                          · intro n hn; exact (by cases hn)
                          · intro _; refine ⟨hi_lt, ?_, ?_⟩
                            · rw [h_lw]; omega
                            · rw [h_lw]; show v.val.size - index.toNat < 4; omega
                        · have hi3 : index.toNat + 3 < v.val.size := by omega
                          by_cases h_cont3 : IsContByte (v.val[index.toNat + 3]'hi3)
                          · -- recurse
                            have h_no_ov_i2' : (index + 1).toNat + 1 < 2^64 := by
                              rw [usize_add_one_toNat _ h_no_ov_i1]; omega
                            have h_i2_toNat : (index + 1 + 1).toNat = index.toNat + 2 := by
                              rw [usize_add_one_toNat (index + 1) h_no_ov_i2',
                                  usize_add_one_toNat _ h_no_ov_i1]
                            have h_no_ov_i3' : (index + 1 + 1).toNat + 1 < 2^64 := by
                              rw [h_i2_toNat]; omega
                            have h_i3_toNat : (index + 1 + 1 + 1).toNat = index.toNat + 3 := by
                              rw [usize_add_one_toNat (index + 1 + 1) h_no_ov_i3', h_i2_toNat]
                            have h_no_ov_i4' : (index + 1 + 1 + 1).toNat + 1 < 2^64 := by
                              rw [h_i3_toNat]; omega
                            have h_i4_toNat : (index + 1 + 1 + 1 + 1).toNat = index.toNat + 4 := by
                              rw [usize_add_one_toNat (index + 1 + 1 + 1) h_no_ov_i4', h_i3_toNat]
                            have h_meas_i4 : v.val.size - (index + 1 + 1 + 1 + 1).toNat ≤ m := by
                              rw [h_i4_toNat]; omega
                            have h_step := validate_at_w4_recurse v index hi_lt h_ge_240 h_w4
                                            hi1 h_sbo hi2 h_cont2 hi3 h_cont3
                            obtain ⟨r, h_eq, h_spec⟩ := ih (index + 1 + 1 + 1 + 1) h_meas_i4
                            refine ⟨r, by rw [h_step]; exact h_eq, ?_⟩
                            unfold ValidateAtSpec at h_spec ⊢
                            cases r with
                            | Ok _ =>
                              rw [isValidUtf8From_w4_ok v.val index.toNat hi_lt h_lw hi1 h_sbo
                                    hi2 h_cont2 hi3 h_cont3]
                              rw [h_i4_toNat] at h_spec; exact h_spec
                            | Err err =>
                              obtain ⟨h_false, h_lo', h_hi', h_prefix, h_some, h_none⟩ := h_spec
                              rw [h_i4_toNat] at h_lo' h_prefix h_false
                              refine ⟨?_, by omega, h_hi', ?_, h_some, h_none⟩
                              · rw [isValidUtf8From_w4_ok v.val index.toNat hi_lt h_lw hi1 h_sbo
                                      hi2 h_cont2 hi3 h_cont3]
                                exact h_false
                              · exact prefix_valid_back_w4 v index err.valid_up_to.toNat hi_lt
                                        h_ge_240 h_w4 hi1 h_sbo hi2 h_cont2 hi3 h_cont3
                                        (by omega) h_hi' h_prefix
                          · -- bad_cont2
                            refine ⟨_, validate_at_w4_bad_cont2 v index hi_lt h_ge_240 h_w4
                                        hi1 h_sbo hi2 h_cont2 hi3 h_cont3, ?_⟩
                            unfold ValidateAtSpec
                            refine ⟨isValidUtf8From_w4_bad_fourth v.val index.toNat hi_lt h_lw hi1
                                      h_sbo hi2 h_cont2 hi3 h_cont3,
                                    Nat.le_refl _, Nat.le_of_lt hi_lt,
                                    prefix_at_self v.val index.toNat (Nat.le_of_lt hi_lt), ?_, ?_⟩
                            · intro n hn
                              injection hn with hn_eq
                              subst hn_eq
                              refine ⟨by decide, by decide, ?_⟩
                              show index.toNat + (3 : u8).toNat ≤ v.val.size
                              have : (3 : u8).toNat = 3 := by decide
                              rw [this]; omega
                            · intro hn_none; exact (by cases hn_none)
                      · -- bad_cont1
                        refine ⟨_, validate_at_w4_bad_cont1 v index hi_lt h_ge_240 h_w4
                                    hi1 h_sbo hi2 h_cont2, ?_⟩
                        unfold ValidateAtSpec
                        refine ⟨isValidUtf8From_w4_bad_third v.val index.toNat hi_lt h_lw hi1
                                  h_sbo hi2 h_cont2,
                                Nat.le_refl _, Nat.le_of_lt hi_lt,
                                prefix_at_self v.val index.toNat (Nat.le_of_lt hi_lt), ?_, ?_⟩
                        · intro n hn
                          injection hn with hn_eq
                          subst hn_eq
                          refine ⟨by decide, by decide, ?_⟩
                          show index.toNat + (2 : u8).toNat ≤ v.val.size
                          have : (2 : u8).toNat = 2 := by decide
                          rw [this]; omega
                        · intro hn_none; exact (by cases hn_none)
                  · -- ¬ SecondByteOk: bad_b2
                    refine ⟨_, validate_at_w4_bad_b2 v index hi_lt h_ge_240 h_w4 hi1 h_sbo, ?_⟩
                    unfold ValidateAtSpec
                    refine ⟨isValidUtf8From_w4_bad_second v.val index.toNat hi_lt h_lw hi1 h_sbo,
                            Nat.le_refl _, Nat.le_of_lt hi_lt,
                            prefix_at_self v.val index.toNat (Nat.le_of_lt hi_lt), ?_, ?_⟩
                    · intro n hn
                      injection hn with hn_eq
                      subst hn_eq
                      refine ⟨by decide, by decide, ?_⟩
                      show index.toNat + (1 : u8).toNat ≤ v.val.size
                      have : (1 : u8).toNat = 1 := by decide
                      rw [this]; omega
                    · intro hn_none; exact (by cases hn_none)
              · -- 245 ≤ first: width 0 (large)
                have h_ge_245 : 245 ≤ (v.val[index.toNat]'hi_lt).toNat := Nat.le_of_not_lt h_w4
                refine ⟨_, validate_at_w0 v index hi_lt (Or.inr h_ge_245), ?_⟩
                show isValidUtf8From v.val index.toNat = false ∧ _
                have h_lw : leadWidth (v.val[index.toNat]'hi_lt) = 0 := by
                  unfold leadWidth
                  rw [if_neg (by omega), if_neg (by omega),
                      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
                refine ⟨isValidUtf8From_invalid v.val index.toNat hi_lt h_lw,
                        Nat.le_refl _, Nat.le_of_lt hi_lt,
                        prefix_at_self v.val index.toNat (Nat.le_of_lt hi_lt), ?_, ?_⟩
                · intro n hn
                  injection hn with hn_eq
                  subst hn_eq
                  refine ⟨by decide, by decide, ?_⟩
                  show index.toNat + (1 : u8).toNat ≤ v.val.size
                  have : (1 : u8).toNat = 1 := by decide
                  rw [this]; omega
                · intro hn_none
                  exact (by cases hn_none)

theorem run_utf8_validation_ok_iff_isValidUtf8 (v : RustSlice u8) :
    run_utf8_validation v =
        RustM.ok (core_models.result.Result.Ok rust_primitives.hax.Tuple0.mk) ↔
      IsValidUtf8 v.val := by
  unfold run_utf8_validation
  obtain ⟨r, hr_eq, hr_spec⟩ :=
    validate_at_correct v v.val.size (0 : usize) (by simp)
  constructor
  · intro h
    rw [hr_eq] at h
    cases r with
    | Ok _ => exact hr_spec
    | Err err =>
        exfalso
        injection h with h1
        cases h1
  · intro h
    show run_utf8_validation_u8.validate_at v (0 : usize) = _
    rw [hr_eq]
    cases r with
    | Ok _ => congr
    | Err err =>
        exfalso
        unfold ValidateAtSpec at hr_spec
        obtain ⟨h_false, _⟩ := hr_spec
        unfold IsValidUtf8 at h
        have h_zero : (0 : usize).toNat = 0 := rfl
        rw [h_zero] at h_false
        rw [h] at h_false
        exact absurd h_false (by simp)

/-- **`prop_valid_up_to_marks_valid_prefix`** — on `Err`, `valid_up_to`
    is in-bounds and the prefix `v[..valid_up_to]` is itself valid
    UTF-8. The validator never gives up "too early". -/
theorem run_utf8_validation_err_prefix_valid
    (v : RustSlice u8) (err : Utf8Error)
    (h : run_utf8_validation v =
        RustM.ok (core_models.result.Result.Err err)) :
    err.valid_up_to.toNat ≤ v.val.size ∧
      IsValidUtf8 (v.val.take err.valid_up_to.toNat) := by
  unfold run_utf8_validation at h
  obtain ⟨r, hr_eq, hr_spec⟩ :=
    validate_at_correct v v.val.size (0 : usize) (by simp)
  rw [hr_eq] at h
  cases r with
  | Ok _ =>
    exfalso
    injection h with h1
    cases h1
  | Err err' =>
    injection h with h1
    injection h1 with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    unfold ValidateAtSpec at hr_spec
    obtain ⟨_, _, h_hi, h_prefix, _⟩ := hr_spec
    refine ⟨h_hi, ?_⟩
    have h_zero : (0 : usize).toNat = 0 := rfl
    rw [h_zero] at h_prefix
    exact h_prefix

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
  unfold run_utf8_validation at h
  obtain ⟨r, hr_eq, hr_spec⟩ :=
    validate_at_correct v v.val.size (0 : usize) (by simp)
  rw [hr_eq] at h
  cases r with
  | Ok _ =>
    exfalso
    injection h with h1
    cases h1
  | Err err' =>
    injection h with h1
    injection h1 with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    unfold ValidateAtSpec at hr_spec
    obtain ⟨_, _, _, _, h_some, _⟩ := hr_spec
    exact h_some n hn

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
  unfold run_utf8_validation at h
  obtain ⟨r, hr_eq, hr_spec⟩ :=
    validate_at_correct v v.val.size (0 : usize) (by simp)
  rw [hr_eq] at h
  cases r with
  | Ok _ =>
    exfalso
    injection h with h1
    cases h1
  | Err err' =>
    injection h with h1
    injection h1 with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    unfold ValidateAtSpec at hr_spec
    obtain ⟨_, _, _, _, _, h_none⟩ := hr_spec
    exact h_none hn

end Run_utf8_validation_u8Obligations
