-- Companion obligations file for the `next_code_point_u8` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import next_code_point_u8

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6400000

namespace Next_code_point_u8Obligations

/-! ## Specification oracle: UTF-8 encoding.

`encodeUtf8 c` is the canonical UTF-8 byte sequence of the Unicode scalar
value `c`, expressed at the `Nat` level independently of the
implementation: 1 byte for `c < 0x80`, 2 for `c < 0x800`, 3 for
`c < 0x10000`, otherwise 4. This is exactly the encoding produced by
`char::encode_utf8` in the Rust property tests, so a postcondition phrased
against it is a genuine semantic specification rather than a restatement of
the decode body. -/
private def encodeUtf8 (c : Nat) : List u8 :=
  if c < 0x80 then
    [UInt8.ofNat c]
  else if c < 0x800 then
    [UInt8.ofNat (0xC0 ||| (c >>> 6)),
     UInt8.ofNat (0x80 ||| (c &&& 0x3F))]
  else if c < 0x10000 then
    [UInt8.ofNat (0xE0 ||| (c >>> 12)),
     UInt8.ofNat (0x80 ||| ((c >>> 6) &&& 0x3F)),
     UInt8.ofNat (0x80 ||| (c &&& 0x3F))]
  else
    [UInt8.ofNat (0xF0 ||| (c >>> 18)),
     UInt8.ofNat (0x80 ||| ((c >>> 12) &&& 0x3F)),
     UInt8.ofNat (0x80 ||| ((c >>> 6) &&& 0x3F)),
     UInt8.ofNat (0x80 ||| (c &&& 0x3F))]

/-- The bytes an iterator still has to yield, in forward order. The
    extracted `Iter u8` wraps a `Seq u8` whose `.val` is the backing array,
    so this is the faithful "remaining input" view that `Iterator::next`
    consumes front-to-back. -/
private def iterBytes (it : core_models.slice.iter.Iter u8) : List u8 :=
  (core_models.slice.iter.Iter._0 it).val.toList

/-! ## Scaffolding: reduction of `Iterator::next` on `Iter u8`.

The extracted decoder threads a `core_models.slice.iter.Iter u8` (a thin
wrapper around a `Seq u8` whose `.val` is the backing `Array`) through up
to four `Iterator::next` calls.  `Iterator::next` for `Iter` is the
`Impl_2` instance: it tests `seq_len = 0`, and on the non-empty branch
reads `seq_first` and re-slices the tail with `seq_slice _ 1 seq_len`.
The two lemmas below collapse one `next` call to a closed form. -/

/-- `RustM.ok x >>= f = f x` as a `simp` rewrite (the library `pure_bind`
    only fires on a literal `Pure.pure`). -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

/-- `f <$> RustM.ok x = RustM.ok (f x)`. -/
@[simp]
private theorem RustM_ok_map {α β : Type} (a : α) (f : α → β) :
    f <$> RustM.ok a = RustM.ok (f a) := rfl

/-- An empty backing array makes `Iterator::next` yield `None` and leave
    the iterator unchanged. -/
private theorem next_nil (it : core_models.slice.iter.Iter u8)
    (h : (core_models.slice.iter.Iter._0 it).val.size = 0) :
    core_models.iter.traits.iterator.Iterator.next
        (core_models.slice.iter.Iter u8) it
      = RustM.ok (rust_primitives.hax.Tuple2.mk it
          core_models.option.Option.None) := by
  simp only [core_models.iter.traits.iterator.Iterator.next,
             rust_primitives.sequence.seq_len,
             rust_primitives.cmp.eq, h]
  rfl

/-- `iterBytes it = []` forces the backing array to be empty. -/
private theorem size_zero_of_iterBytes_nil
    (it : core_models.slice.iter.Iter u8) (h : iterBytes it = []) :
    (core_models.slice.iter.Iter._0 it).val.size = 0 := by
  have hl := congrArg List.length h
  simpa [iterBytes] using hl

/-- `USize64.ofNat n` is `≠ 0` (as a `==` test) for a non-empty backing
    array (`n < 2^64` by the `Seq` invariant). -/
private theorem ofNat_size_beq_zero
    (s : rust_primitives.sequence.Seq u8) (hpos : 0 < s.val.size) :
    (USize64.ofNat s.val.size == (0 : usize)) = false := by
  have hlt : s.val.size < USize64.size := s.size_lt_usizeSize
  have hne : USize64.ofNat s.val.size ≠ (0 : usize) := by
    intro hh
    have ht := congrArg USize64.toNat hh
    rw [USize64.toNat_ofNat_of_lt' hlt] at ht
    have h0 : (0 : usize).toNat = 0 := rfl
    rw [h0] at ht
    omega
  simpa using hne

/-- `1 ≤ USize64.ofNat n` for a non-empty backing array. -/
private theorem one_le_ofNat_size
    (s : rust_primitives.sequence.Seq u8) (hpos : 0 < s.val.size) :
    (1 : usize) ≤ USize64.ofNat s.val.size := by
  rw [USize64.le_iff_toNat_le, USize64.toNat_ofNat_of_lt' s.size_lt_usizeSize]
  have h1 : (1 : usize).toNat = 1 := rfl
  omega

/-- `usize` order is reflexive (Mathlib's `le_refl` is unavailable). -/
private theorem usize_le_refl (x : usize) : x ≤ x := by
  rw [USize64.le_iff_toNat_le]
  exact Nat.le_refl _

/-- `seq_first` on a non-empty backing array returns its head element. -/
private theorem seq_first_pos
    (s : rust_primitives.sequence.Seq u8) (hpos : 0 < s.val.size) :
    rust_primitives.sequence.seq_first u8 s = RustM.ok (s.val[0]'hpos) := by
  unfold rust_primitives.sequence.seq_first
  have hb : ¬ ((s.val.size == 0) = true) := by
    have : s.val.size ≠ 0 := by omega
    simpa using this
  rw [dif_neg hb]
  rfl

/-- `seq_slice _ 1 len` on a non-empty backing array returns the tail
    sub-slice `[1, size)`. -/
private theorem seq_slice_tail
    (s : rust_primitives.sequence.Seq u8) (hpos : 0 < s.val.size)
    (pf : ((s.val.toSubarray 1 s.val.size).toArray).size < USize64.size) :
    rust_primitives.sequence.seq_slice u8 s (1 : usize)
        (USize64.ofNat s.val.size)
      = RustM.ok ⟨(s.val.toSubarray 1 s.val.size).toArray, pf⟩ := by
  unfold rust_primitives.sequence.seq_slice
  have hcond :
      ((1 : usize) ≤ USize64.ofNat s.val.size
        && USize64.ofNat s.val.size ≤ USize64.ofNat s.val.size) = true := by
    simp [one_le_ofNat_size s hpos]
  rw [if_pos hcond]
  have ht1 : (1 : usize).toNat = 1 := rfl
  have hte : (USize64.ofNat s.val.size).toNat = s.val.size :=
    USize64.toNat_ofNat_of_lt' s.size_lt_usizeSize
  simp only [ht1, hte]
  rfl

/-- One `Iterator::next` on a non-empty iterator yields the head byte and
    the tail iterator (whose backing array is the sub-slice `[1, size)`). -/
private theorem next_cons (it : core_models.slice.iter.Iter u8)
    (b : u8) (bs : List u8) (h : iterBytes it = b :: bs) :
    ∃ it' : core_models.slice.iter.Iter u8,
      core_models.iter.traits.iterator.Iterator.next
          (core_models.slice.iter.Iter u8) it
        = RustM.ok (rust_primitives.hax.Tuple2.mk it'
            (core_models.option.Option.Some b))
      ∧ iterBytes it' = bs := by
  obtain ⟨s⟩ := it
  simp only [iterBytes] at h ⊢
  have hsz : s.val.size = bs.length + 1 := by
    have hl := congrArg List.length h
    simpa using hl
  have hpos : 0 < s.val.size := by omega
  have hne : s.val.size ≠ 0 := by omega
  have hbz : (s.val.size == 0) = false := by simpa using hne
  have harr : s.val = (b :: bs).toArray := by
    apply Array.ext'
    simp [h]
  have hb0 : s.val[0]'hpos = b := by
    simp [harr]
  have hpf : ((s.val.toSubarray 1 s.val.size).toArray).size < USize64.size := by
    have hlt := s.size_lt_usizeSize
    simp only [Subarray.size_toArray, Array.start_toSubarray,
               Array.stop_toSubarray, Subarray.size_eq]
    omega
  refine ⟨⟨⟨(s.val.toSubarray 1 s.val.size).toArray, hpf⟩⟩, ?heq, ?hb⟩
  case heq =>
    simp [core_models.iter.traits.iterator.Iterator.next,
          rust_primitives.sequence.seq_len,
          rust_primitives.cmp.eq,
          seq_first_pos s hpos, seq_slice_tail s hpos hpf, hb0]
    intro hc
    exfalso
    have hz := congrArg USize64.toNat hc
    rw [USize64.toNat_ofNat_of_lt' s.size_lt_usizeSize] at hz
    have h0 : USize64.toNat (0 : usize) = 0 := rfl
    omega
  case hb =>
    simp only [Subarray.toList_toArray,
               Subarray.toList_eq_drop_take, Array.array_toSubarray,
               Array.start_toSubarray, Array.stop_toSubarray, h]
    simp [hsz]

/-- Whole-function reduction on an exhausted iterator: `next_code_point`
    short-circuits through the `None` arm of the first `Iterator::next`
    and returns the iterator unchanged with `None`. -/
private theorem next_code_point_nil (it : core_models.slice.iter.Iter u8)
    (h : (core_models.slice.iter.Iter._0 it).val.size = 0) :
    next_code_point_u8.next_code_point it
      = RustM.ok (rust_primitives.hax.Tuple2.mk it
          core_models.option.Option.None) := by
  unfold next_code_point_u8.next_code_point
  rw [next_nil it h]
  simp only [RustM_ok_bind]
  rfl

/-! ## Decode-correctness core (shared by obligations 1 and 2).

The decoder is total and threads the iterator through 1..4 `next_cons`
steps depending on the first byte.  We split on the 1/2/3/4-byte width.
The ASCII (1-byte) branch is discharged in full below.  The multibyte
branches reduce — by the same `next_cons` threading + the
`utf8_first_byte` / `utf8_acc_cont_byte` reductions — to the pure
byte-reassembly identities `recon2` / `recon3` / `recon4` stated (as
scaffolding) just below; those identities are the genuine remaining
obstacle. -/

/-- Widening `u8 → u32` of a small literal byte. -/
private theorem cast8_32 (c : Nat) (h : c < 256) :
    UInt8.toUInt32 (UInt8.ofNat c) = UInt32.ofNat c := by
  have h8 : (UInt8.ofNat c).toNat = c :=
    UInt8.toNat_ofNat_of_lt' (by omega)
  have key : (UInt8.toUInt32 (UInt8.ofNat c)).toNat = (UInt32.ofNat c).toNat := by
    rw [UInt8.toNat_toUInt32, h8, UInt32.toNat_ofNat_of_lt' (by omega : c < 2 ^ 32)]
  exact UInt32.toNat.inj key

/-- For a byte `< 128`, the Rust `<` test against `128` is `true`. -/
private theorem u8_lt_128 (c : Nat) (h : c < 128) :
    (UInt8.ofNat c : u8) < (128 : u8) := by
  rw [UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat_of_lt' (by omega : c < 2 ^ 8)]
  have h128 : (128 : u8).toNat = 128 := rfl
  omega

/-! ### Byte-reassembly identities (scaffolding for the multibyte branches).

These are the pure `Nat`-level identities the 2/3/4-byte decode branches
reduce to once the iterator threading and the
`utf8_first_byte`/`utf8_acc_cont_byte` operators are unfolded.  Each says:
"OR of the disjoint shifted byte groups of the canonical UTF-8 encoding
reconstructs `c`".  They are stated here so a future pass has the exact
lemmas to discharge; the disjointness makes them `Nat`/`BitVec`-decidable
once a `c`-to-`BitVec 21` bridge is available (see docstring on
`decode_correct`). -/

/-- Extract a low byte-group out of `header ||| x`: when `header`'s low
    `n` bits are clear and `x < 2^n`, masking with `2^n-1` recovers `x`. -/
private theorem orgrp (C x n : Nat) (hC : C % 2 ^ n = 0) (hx : x < 2 ^ n) :
    (C ||| x) &&& (2 ^ n - 1) = x := by
  rw [Nat.and_or_distrib_right, Nat.and_two_pow_sub_one_eq_mod,
      Nat.and_two_pow_sub_one_eq_mod, hC, Nat.zero_or,
      Nat.mod_eq_of_lt hx]

/-- 2-byte reconstruction:
    `((0xC0|||c>>>6) &&& 0x1F) <<< 6  |||  ((0x80|||c&&&0x3F) &&& 0x3F) = c`. -/
private theorem recon2 (c : Nat) (h0 : 0x80 ≤ c) (h1 : c < 0x800) :
    (((0xC0 ||| (c >>> 6)) &&& 0x1F) <<< 6) ||| ((0x80 ||| (c &&& 0x3F)) &&& 0x3F) = c := by
  have hb : c >>> 6 < 2 ^ 5 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hl : c &&& 0x3F < 2 ^ 6 := by
    have : c &&& 0x3F ≤ 0x3F := Nat.and_le_right
    omega
  have m1 : (0xC0 ||| (c >>> 6)) &&& 0x1F = c >>> 6 := by
    have := orgrp 0xC0 (c >>> 6) 5 (by decide) hb
    simpa using this
  have m2 : (0x80 ||| (c &&& 0x3F)) &&& 0x3F = c &&& 0x3F := by
    have := orgrp 0x80 (c &&& 0x3F) 6 (by decide) hl
    simpa using this
  have hand : c &&& 0x3F = c % 2 ^ 6 := by
    have := Nat.and_two_pow_sub_one_eq_mod c 6
    simpa using this
  rw [m1, m2, Nat.shiftRight_eq_div_pow, hand,
      ← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt c (by decide)),
      Nat.shiftLeft_eq]
  have h64 : (2 : Nat) ^ 6 = 64 := by decide
  rw [h64]
  omega

/-- 3-byte reconstruction. -/
private theorem recon3 (c : Nat) (h0 : 0x800 ≤ c) (h1 : c < 0x10000) :
    (((0xE0 ||| (c >>> 12)) &&& 0x0F) <<< 12)
      ||| ((((0x80 ||| ((c >>> 6) &&& 0x3F)) &&& 0x3F) <<< 6)
            ||| ((0x80 ||| (c &&& 0x3F)) &&& 0x3F)) = c := by
  have hb0 : c >>> 12 < 2 ^ 4 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hk1 : (c >>> 6) &&& 0x3F < 2 ^ 6 := by
    have : (c >>> 6) &&& 0x3F ≤ 0x3F := Nat.and_le_right
    omega
  have hk2 : c &&& 0x3F < 2 ^ 6 := by
    have : c &&& 0x3F ≤ 0x3F := Nat.and_le_right
    omega
  have g0 : (0xE0 ||| (c >>> 12)) &&& 0x0F = c >>> 12 := by
    have := orgrp 0xE0 (c >>> 12) 4 (by decide) hb0
    simpa using this
  have g1 : (0x80 ||| ((c >>> 6) &&& 0x3F)) &&& 0x3F = (c >>> 6) &&& 0x3F := by
    have := orgrp 0x80 ((c >>> 6) &&& 0x3F) 6 (by decide) hk1
    simpa using this
  have g2 : (0x80 ||| (c &&& 0x3F)) &&& 0x3F = c &&& 0x3F := by
    have := orgrp 0x80 (c &&& 0x3F) 6 (by decide) hk2
    simpa using this
  have e1 : (c >>> 6) &&& 0x3F = (c >>> 6) % 2 ^ 6 := by
    have := Nat.and_two_pow_sub_one_eq_mod (c >>> 6) 6
    simpa using this
  have e2 : c &&& 0x3F = c % 2 ^ 6 := by
    have := Nat.and_two_pow_sub_one_eq_mod c 6
    simpa using this
  rw [g0, g1, g2, e1, e2, Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow,
      ← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt c (by decide))]
  have hv1 : (c / 2 ^ 6 % 2 ^ 6) <<< 6 + c % 2 ^ 6 < 2 ^ 12 := by
    rw [Nat.shiftLeft_eq]
    have p6 : (2 : Nat) ^ 6 = 64 := by decide
    have p12 : (2 : Nat) ^ 12 = 4096 := by decide
    rw [p6, p12]
    omega
  rw [← Nat.shiftLeft_add_eq_or_of_lt hv1, Nat.shiftLeft_eq,
      Nat.shiftLeft_eq]
  have p6 : (2 : Nat) ^ 6 = 64 := by decide
  have p12 : (2 : Nat) ^ 12 = 4096 := by decide
  rw [p6, p12]
  omega

/-- 4-byte reconstruction. -/
private theorem recon4 (c : Nat) (h0 : 0x10000 ≤ c) (h1 : c ≤ 0x10FFFF) :
    (((0xF0 ||| (c >>> 18)) &&& 0x07) <<< 18)
      ||| ((((0x80 ||| ((c >>> 12) &&& 0x3F)) &&& 0x3F) <<< 12)
            ||| ((((0x80 ||| ((c >>> 6) &&& 0x3F)) &&& 0x3F) <<< 6)
                  ||| ((0x80 ||| (c &&& 0x3F)) &&& 0x3F))) = c := by
  have hb0 : c >>> 18 < 2 ^ 3 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hk1 : (c >>> 12) &&& 0x3F < 2 ^ 6 := by
    have : (c >>> 12) &&& 0x3F ≤ 0x3F := Nat.and_le_right
    omega
  have hk2 : (c >>> 6) &&& 0x3F < 2 ^ 6 := by
    have : (c >>> 6) &&& 0x3F ≤ 0x3F := Nat.and_le_right
    omega
  have hk3 : c &&& 0x3F < 2 ^ 6 := by
    have : c &&& 0x3F ≤ 0x3F := Nat.and_le_right
    omega
  have g0 : (0xF0 ||| (c >>> 18)) &&& 0x07 = c >>> 18 := by
    have := orgrp 0xF0 (c >>> 18) 3 (by decide) hb0
    simpa using this
  have g1 : (0x80 ||| ((c >>> 12) &&& 0x3F)) &&& 0x3F = (c >>> 12) &&& 0x3F := by
    have := orgrp 0x80 ((c >>> 12) &&& 0x3F) 6 (by decide) hk1
    simpa using this
  have g2 : (0x80 ||| ((c >>> 6) &&& 0x3F)) &&& 0x3F = (c >>> 6) &&& 0x3F := by
    have := orgrp 0x80 ((c >>> 6) &&& 0x3F) 6 (by decide) hk2
    simpa using this
  have g3 : (0x80 ||| (c &&& 0x3F)) &&& 0x3F = c &&& 0x3F := by
    have := orgrp 0x80 (c &&& 0x3F) 6 (by decide) hk3
    simpa using this
  have e1 : (c >>> 12) &&& 0x3F = (c >>> 12) % 2 ^ 6 := by
    have := Nat.and_two_pow_sub_one_eq_mod (c >>> 12) 6
    simpa using this
  have e2 : (c >>> 6) &&& 0x3F = (c >>> 6) % 2 ^ 6 := by
    have := Nat.and_two_pow_sub_one_eq_mod (c >>> 6) 6
    simpa using this
  have e3 : c &&& 0x3F = c % 2 ^ 6 := by
    have := Nat.and_two_pow_sub_one_eq_mod c 6
    simpa using this
  rw [g0, g1, g2, g3, e1, e2, e3, Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      ← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt c (by decide))]
  have hv2 : (c / 2 ^ 6 % 2 ^ 6) <<< 6 + c % 2 ^ 6 < 2 ^ 12 := by
    rw [Nat.shiftLeft_eq]
    have p6 : (2 : Nat) ^ 6 = 64 := by decide
    have p12 : (2 : Nat) ^ 12 = 4096 := by decide
    rw [p6, p12]
    omega
  rw [← Nat.shiftLeft_add_eq_or_of_lt hv2]
  have hv1 : (c / 2 ^ 12 % 2 ^ 6) <<< 12
              + ((c / 2 ^ 6 % 2 ^ 6) <<< 6 + c % 2 ^ 6) < 2 ^ 18 := by
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    have p6 : (2 : Nat) ^ 6 = 64 := by decide
    have p12 : (2 : Nat) ^ 12 = 4096 := by decide
    have p18 : (2 : Nat) ^ 18 = 262144 := by decide
    rw [p6, p12, p18]
    omega
  rw [← Nat.shiftLeft_add_eq_or_of_lt hv1, Nat.shiftLeft_eq,
      Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  have p6 : (2 : Nat) ^ 6 = 64 := by decide
  have p12 : (2 : Nat) ^ 12 = 4096 := by decide
  have p18 : (2 : Nat) ^ 18 = 262144 := by decide
  rw [p6, p12, p18]
  omega

/-- `utf8_first_byte x 2` reduces to the masked widening cast. -/
private theorem ufb2 (x : u8) :
    next_code_point_u8.utf8_first_byte x (2 : u32)
      = RustM.ok (UInt8.toUInt32 (x &&& 0x1F)) := by
  unfold next_code_point_u8.utf8_first_byte
  simp [rust_primitives.ops.bit.Shr.shr, rust_primitives.hax.cast_op,
        Cast.cast]
  rfl

/-- `utf8_acc_cont_byte ch b` reduces to the shift-or accumulation. -/
private theorem uacb (ch : u32) (b : u8) :
    next_code_point_u8.utf8_acc_cont_byte ch b
      = RustM.ok ((ch <<< (6 : UInt32)) ||| UInt8.toUInt32 (b &&& 0x3F)) := by
  unfold next_code_point_u8.utf8_acc_cont_byte next_code_point_u8.CONT_MASK
  simp [rust_primitives.ops.bit.Shl.shl, rust_primitives.hax.cast_op,
        Cast.cast]
  rfl

/-- `unwrap_or` on `Some`. -/
private theorem uo_some (v : u8) :
    core_models.option.Impl.unwrap_or u8 (core_models.option.Option.Some v) 0
      = RustM.ok v := by
  unfold core_models.option.Impl.unwrap_or; rfl

/-- `unwrap_or` on `None`. -/
private theorem uo_none :
    core_models.option.Impl.unwrap_or u8 core_models.option.Option.None 0
      = RustM.ok (0 : u8) := by
  unfold core_models.option.Impl.unwrap_or; rfl

/-! Decode correctness: if the iterator's remaining bytes begin with the
    canonical UTF-8 encoding of the scalar `c`, the call returns
    `Some (c as u32)` and advances the iterator past exactly that
    encoding.

    The 1-byte (ASCII) branch is **fully proved**.  The multibyte branches
    are set up here (width case-split + first `next_cons` step) and the
    pure byte-reassembly arithmetic they reduce to is **fully proved** as
    `recon2` / `recon3` / `recon4` above.

    Surviving `sorry` (multibyte branches only).  Every external lemma the
    branch needs is now proved in this file:

      * `next_cons`            — one `Iterator::next` step (head + tail);
      * `ufb2`                 — `utf8_first_byte x 2`
                                  `= RustM.ok (UInt8.toUInt32 (x &&& 0x1F))`;
      * `uacb`                 — `utf8_acc_cont_byte ch b`
                                  `= RustM.ok (ch <<< 6 ||| UInt8.toUInt32 (b &&& 0x3F))`;
      * `uo_some` / `uo_none`  — `unwrap_or` reductions;
      * `recon2` / `recon3` / `recon4` — the pure byte-reassembly
                                  identities reconstruct `c` (fully proved).

    The branch is set up here (width case-split + first `next_cons`).  The
    specific remaining sub-goal, after threading the 2..4 reads and
    rewriting with `ufb2`/`uacb`/`uo_*`, is of the form

      `(UInt8.toUInt32 (b0 &&& 0x1F) <<< 6 ||| UInt8.toUInt32 (b1 &&& 0x3F))
         = UInt32.ofNat c`

    (and the 3-byte and 4-byte analogues), together with the first-byte branch
    tests `b0 <? 128`, `b0 >=? 0xE0`, `b0 >=? 0xF0`.  This is no longer
    blocked by missing infrastructure: it needs only the mechanical
    `UInt32 → Nat` `toNat`-distribution
    (`UInt32.toNat_or` / `toNat_shiftLeft` / `toNat_and` /
    `UInt8.toNat_toUInt32`, all in Lean core) to rewrite the `u32`
    reassembly into the `Nat` LHS of the corresponding `recon{2,3,4}`,
    plus a `(UInt8.ofNat (0xC0 ||| c>>>6)).toNat ∈ [0xC0,0xDF]`-style
    value lemma (provable from `Nat.shiftLeft_add_eq_or_of_lt`, already
    used by `recon*`) to decide the branch tests.

    Structural unblock: a `u32`-reassembly-to-`Nat`-bridge helper
    `reasm : ((UInt8.toUInt32 a) <<< k ||| UInt8.toUInt32 d).toNat
              = (a.toNat &&& M) * 2^k + (d.toNat &&& N)` proved once from
    the core `UInt32.toNat_*` lemmas; with it and the lemmas above each
    multibyte branch closes exactly like the ASCII branch (thread the
    reads, rewrite operators, apply `recon{2,3,4}`).  No change outside
    this file is required. -/

/-! ### Operator / bridge scaffolding for the multibyte branches. -/

/-- `u8 → u32` widening cast reduces to `UInt8.toUInt32`. -/
private theorem castU (b : u8) :
    (rust_primitives.hax.cast_op b : RustM u32) = RustM.ok (UInt8.toUInt32 b) := rfl

/-- Left shift of a `u32` by an `i32` constant in range. -/
private theorem shlU (x : u32) (k : i32) (hk : (0 ≤ k && k < 32) = true) :
    (x <<<? k : RustM u32) = RustM.ok (x <<< (k.toNatClampNeg.toUInt32)) := by
  show (rust_primitives.ops.bit.Shl.shl x k : RustM u32) = _
  show (if (0 ≤ k && k < 32) then pure (x <<< (k.toNatClampNeg.toUInt32))
        else (.fail .integerOverflow : RustM u32)) = _
  rw [hk]; rfl

/-- Disjoint OR with a header whose low 6 bits are clear (`0xC0`). -/
private theorem orC0 (k : Nat) (h : k < 64) : 0xC0 ||| k = 192 + k := by
  have h6 : k < 2 ^ 6 := by
    have p6 : (2:Nat) ^ 6 = 64 := by decide
    omega
  have key := Nat.shiftLeft_add_eq_or_of_lt h6 3
  have e : (3 : Nat) <<< 6 = 192 := by decide
  rw [e] at key
  exact key.symm

/-- Disjoint OR with header `0x80` (low 7 bits clear; we use it for
    values `< 64`). -/
private theorem or80 (m : Nat) (h : m < 64) : 0x80 ||| m = 128 + m := by
  have h6 : m < 2 ^ 6 := by
    have p6 : (2:Nat) ^ 6 = 64 := by decide
    omega
  have key := Nat.shiftLeft_add_eq_or_of_lt h6 2
  have e : (2 : Nat) <<< 6 = 128 := by decide
  rw [e] at key
  exact key.symm

/-- Disjoint OR with header `0xE0` (low 5 bits clear). -/
private theorem orE0 (k : Nat) (h : k < 32) : 0xE0 ||| k = 224 + k := by
  have h5 : k < 2 ^ 5 := by
    have p5 : (2:Nat) ^ 5 = 32 := by decide
    omega
  have key := Nat.shiftLeft_add_eq_or_of_lt h5 7
  have e : (7 : Nat) <<< 5 = 224 := by decide
  rw [e] at key
  exact key.symm

/-- Disjoint OR with header `0xF0` (low 4 bits clear). -/
private theorem orF0 (k : Nat) (h : k < 16) : 0xF0 ||| k = 240 + k := by
  have h4 : k < 2 ^ 4 := by
    have p4 : (2:Nat) ^ 4 = 16 := by decide
    omega
  have key := Nat.shiftLeft_add_eq_or_of_lt h4 15
  have e : (15 : Nat) <<< 4 = 240 := by decide
  rw [e] at key
  exact key.symm

/-- `&&& 0x1F = % 32` on `Nat`. -/
private theorem andMod5 (x : Nat) : x &&& 0x1F = x % 32 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 5
  simpa using this

/-- `&&& 0x3F = % 64` on `Nat`. -/
private theorem andMod6 (x : Nat) : x &&& 0x3F = x % 64 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 6
  simpa using this

/-- `&&& 0x07 = % 8` on `Nat`. -/
private theorem andMod3 (x : Nat) : x &&& 0x07 = x % 8 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 3
  simpa using this

/-- 2-byte reassembly bridge: `toNat` of the `u32` OR/shift form is the
    disjoint additive Nat value. -/
private theorem bridge2 (p q : u8) :
    ((UInt8.toUInt32 (p &&& 0x1F) <<< (6 : UInt32)) ||| UInt8.toUInt32 (q &&& 0x3F)).toNat
      = p.toNat % 32 * 64 + q.toNat % 64 := by
  have hbv :
      ((UInt8.toUInt32 (p &&& 0x1F) <<< (6 : UInt32)) ||| UInt8.toUInt32 (q &&& 0x3F)).toBitVec
        = (((p.toBitVec.setWidth 5).setWidth 32) <<< (6 : Nat))
            + ((q.toBitVec.setWidth 6).setWidth 32) := by
    bv_decide
  have h := congrArg BitVec.toNat hbv
  simp only [UInt32.toNat_toBitVec, BitVec.toNat_add, BitVec.toNat_shiftLeft,
             BitVec.toNat_setWidth, UInt8.toNat_toBitVec, Nat.shiftLeft_eq] at h
  have e5 : (2:Nat)^5 = 32 := by decide
  have e6 : (2:Nat)^6 = 64 := by decide
  have e32 : (2:Nat)^32 = 4294967296 := by decide
  have e8 : (2:Nat)^8 = 256 := by decide
  have hp : p.toNat < 256 := by have hh := UInt8.toNat_lt p; rw [e8] at hh; exact hh
  have hq : q.toNat < 256 := by have hh := UInt8.toNat_lt q; rw [e8] at hh; exact hh
  rw [e5, e6, e32] at h
  rw [h]; omega

/-- Normalise the `i32`-typed shift amount `12` to `UInt32`. -/
private theorem cast12 : ((12 : i32).toNatClampNeg).toUInt32 = (12 : UInt32) := by decide

/-- Normalise the `i32`-typed shift amount `18` to `UInt32`. -/
private theorem cast18 : ((18 : i32).toNatClampNeg).toUInt32 = (18 : UInt32) := by decide

/-- `u32 <<<? (12 : i32)` reduces to `<<< (12 : UInt32)`. -/
private theorem shl12u (x : u32) :
    (x <<<? (12 : i32) : RustM u32) = RustM.ok (x <<< (12 : UInt32)) := by
  rw [shlU x (12 : i32) (by decide), cast12]

/-- `u32 <<<? (18 : i32)` reduces to `<<< (18 : UInt32)`. -/
private theorem shl18u (x : u32) :
    (x <<<? (18 : i32) : RustM u32) = RustM.ok (x <<< (18 : UInt32)) := by
  rw [shlU x (18 : i32) (by decide), cast18]

/-- 3-byte reassembly bridge. -/
private theorem bridge3 (p q r : u8) :
    ((UInt8.toUInt32 (p &&& 0x1F) <<< (12 : UInt32))
      ||| ((UInt8.toUInt32 (q &&& 0x3F) <<< (6 : UInt32))
            ||| UInt8.toUInt32 (r &&& 0x3F))).toNat
      = p.toNat % 32 * 4096 + q.toNat % 64 * 64 + r.toNat % 64 := by
  have hbv :
      ((UInt8.toUInt32 (p &&& 0x1F) <<< (12 : UInt32))
        ||| ((UInt8.toUInt32 (q &&& 0x3F) <<< (6 : UInt32))
              ||| UInt8.toUInt32 (r &&& 0x3F))).toBitVec
        = (((p.toBitVec.setWidth 5).setWidth 32) <<< (12 : Nat))
            + (((q.toBitVec.setWidth 6).setWidth 32) <<< (6 : Nat))
            + ((r.toBitVec.setWidth 6).setWidth 32) := by
    bv_decide
  have h := congrArg BitVec.toNat hbv
  simp only [UInt32.toNat_toBitVec, BitVec.toNat_add, BitVec.toNat_shiftLeft,
             BitVec.toNat_setWidth, UInt8.toNat_toBitVec, Nat.shiftLeft_eq] at h
  have e5 : (2:Nat)^5 = 32 := by decide
  have e6 : (2:Nat)^6 = 64 := by decide
  have e12 : (2:Nat)^12 = 4096 := by decide
  have e32 : (2:Nat)^32 = 4294967296 := by decide
  have e8 : (2:Nat)^8 = 256 := by decide
  have hp : p.toNat < 256 := by have hh := UInt8.toNat_lt p; rw [e8] at hh; exact hh
  have hq : q.toNat < 256 := by have hh := UInt8.toNat_lt q; rw [e8] at hh; exact hh
  have hr : r.toNat < 256 := by have hh := UInt8.toNat_lt r; rw [e8] at hh; exact hh
  rw [e5, e6, e12, e32] at h
  rw [h]; omega

/-- 4-byte reassembly bridge. -/
private theorem bridge4 (p q r s : u8) :
    (((UInt8.toUInt32 (p &&& 0x1F) &&& 7) <<< (18 : UInt32))
      ||| (((UInt8.toUInt32 (q &&& 0x3F) <<< (6 : UInt32))
              ||| UInt8.toUInt32 (r &&& 0x3F)) <<< (6 : UInt32)
            ||| UInt8.toUInt32 (s &&& 0x3F))).toNat
      = p.toNat % 8 * 262144 + q.toNat % 64 * 4096 + r.toNat % 64 * 64
          + s.toNat % 64 := by
  have hbv :
      (((UInt8.toUInt32 (p &&& 0x1F) &&& 7) <<< (18 : UInt32))
        ||| (((UInt8.toUInt32 (q &&& 0x3F) <<< (6 : UInt32))
                ||| UInt8.toUInt32 (r &&& 0x3F)) <<< (6 : UInt32)
              ||| UInt8.toUInt32 (s &&& 0x3F))).toBitVec
        = (((p.toBitVec.setWidth 3).setWidth 32) <<< (18 : Nat))
            + (((q.toBitVec.setWidth 6).setWidth 32) <<< (12 : Nat))
            + (((r.toBitVec.setWidth 6).setWidth 32) <<< (6 : Nat))
            + ((s.toBitVec.setWidth 6).setWidth 32) := by
    bv_decide
  have h := congrArg BitVec.toNat hbv
  simp only [UInt32.toNat_toBitVec, BitVec.toNat_add, BitVec.toNat_shiftLeft,
             BitVec.toNat_setWidth, UInt8.toNat_toBitVec, Nat.shiftLeft_eq] at h
  have e3 : (2:Nat)^3 = 8 := by decide
  have e6 : (2:Nat)^6 = 64 := by decide
  have e12 : (2:Nat)^12 = 4096 := by decide
  have e18 : (2:Nat)^18 = 262144 := by decide
  have e32 : (2:Nat)^32 = 4294967296 := by decide
  have e8 : (2:Nat)^8 = 256 := by decide
  have hp : p.toNat < 256 := by have hh := UInt8.toNat_lt p; rw [e8] at hh; exact hh
  have hq : q.toNat < 256 := by have hh := UInt8.toNat_lt q; rw [e8] at hh; exact hh
  have hr : r.toNat < 256 := by have hh := UInt8.toNat_lt r; rw [e8] at hh; exact hh
  have hs : s.toNat < 256 := by have hh := UInt8.toNat_lt s; rw [e8] at hh; exact hh
  rw [e3, e6, e12, e18, e32] at h
  rw [h]; omega

private theorem decode_correct
    (it : core_models.slice.iter.Iter u8) (c : Nat) (rest : List u8)
    (hc : c ≤ 0x10FFFF)
    (hbytes : iterBytes it = encodeUtf8 c ++ rest) :
    ∃ it' : core_models.slice.iter.Iter u8,
      next_code_point_u8.next_code_point it
        = RustM.ok (rust_primitives.hax.Tuple2.mk it'
            (core_models.option.Option.Some (UInt32.ofNat c)))
      ∧ iterBytes it' = rest := by
  by_cases h1 : c < 0x80
  · -- ASCII (1-byte) branch — fully discharged.
    have henc : encodeUtf8 c = [UInt8.ofNat c] := by
      unfold encodeUtf8; simp [h1]
    rw [henc] at hbytes
    have hcons : iterBytes it = UInt8.ofNat c :: rest := by
      simpa using hbytes
    obtain ⟨it1, hnext, hb1⟩ := next_cons it (UInt8.ofNat c) rest hcons
    refine ⟨it1, ?_, hb1⟩
    unfold next_code_point_u8.next_code_point
    rw [hnext]
    simp only [RustM_ok_bind]
    have hxlt : (UInt8.ofNat c : u8) < (128 : u8) := u8_lt_128 c h1
    simp only [rust_primitives.cmp.lt, rust_primitives.hax.cast_op,
               Cast.cast, pure_bind, hxlt, decide_true, if_true,
               cast8_32 c (by omega)]
    rfl
  · -- Multibyte (2/3/4-byte) branches: width case-split + first read.
    by_cases h2 : c < 0x800
    · -- 2-byte.
      have henc : encodeUtf8 c
          = [UInt8.ofNat (0xC0 ||| (c >>> 6)),
             UInt8.ofNat (0x80 ||| (c &&& 0x3F))] := by
        unfold encodeUtf8; simp [h1, h2]
      rw [henc] at hbytes
      have hcons : iterBytes it
          = UInt8.ofNat (0xC0 ||| (c >>> 6))
              :: (UInt8.ofNat (0x80 ||| (c &&& 0x3F)) :: rest) := by
        simpa using hbytes
      obtain ⟨it1, hnext1, hb1⟩ := next_cons it _ _ hcons
      obtain ⟨it2, hnext2, hb2⟩ := next_cons it1 _ _ hb1
      refine ⟨it2, ?_, hb2⟩
      have p6 : (2:Nat)^6 = 64 := by decide
      have p8 : (2:Nat)^8 = 256 := by decide
      have p32 : (2:Nat)^32 = 4294967296 := by decide
      have hcdiv : c >>> 6 = c / 64 := by
        rw [Nat.shiftRight_eq_div_pow, p6]
      have hb0eq : 0xC0 ||| (c >>> 6) = 192 + c / 64 := by
        rw [hcdiv]; exact orC0 (c / 64) (by omega)
      have hb1eq : 0x80 ||| (c &&& 0x3F) = 128 + c % 64 := by
        rw [andMod6]; exact or80 (c % 64) (by omega)
      have hb0n : (UInt8.ofNat (0xC0 ||| (c >>> 6)) : u8).toNat = 192 + c / 64 := by
        rw [UInt8.toNat_ofNat_of_lt'
              (show 0xC0 ||| (c >>> 6) < 2 ^ 8 by rw [hb0eq, p8]; omega), hb0eq]
      have hb1n : (UInt8.ofNat (0x80 ||| (c &&& 0x3F)) : u8).toNat = 128 + c % 64 := by
        rw [UInt8.toNat_ofNat_of_lt'
              (show 0x80 ||| (c &&& 0x3F) < 2 ^ 8 by rw [hb1eq, p8]; omega), hb1eq]
      have hcond_lt :
          decide ((UInt8.ofNat (0xC0 ||| (c >>> 6)) : u8) < (128 : u8)) = false := by
        rw [decide_eq_false_iff_not, UInt8.lt_iff_toNat_lt, hb0n]
        show ¬ (192 + c / 64 < (128 : u8).toNat)
        have e : (128 : u8).toNat = 128 := rfl
        rw [e]; omega
      have hcond_ge :
          decide ((UInt8.ofNat (0xC0 ||| (c >>> 6)) : u8) ≥ (224 : u8)) = false := by
        rw [decide_eq_false_iff_not, ge_iff_le, UInt8.le_iff_toNat_le, hb0n]
        show ¬ ((224 : u8).toNat ≤ 192 + c / 64)
        have e : (224 : u8).toNat = 224 := rfl
        rw [e]; omega
      have hval :
          ((UInt8.toUInt32 (UInt8.ofNat (0xC0 ||| (c >>> 6)) &&& 0x1F) <<< (6 : UInt32))
            ||| UInt8.toUInt32 (UInt8.ofNat (0x80 ||| (c &&& 0x3F)) &&& 0x3F))
            = UInt32.ofNat c := by
        apply UInt32.toNat.inj
        rw [bridge2 (UInt8.ofNat (0xC0 ||| (c >>> 6))) (UInt8.ofNat (0x80 ||| (c &&& 0x3F))),
            hb0n, hb1n,
            UInt32.toNat_ofNat_of_lt' (show c < 2 ^ 32 by rw [p32]; omega)]
        omega
      unfold next_code_point_u8.next_code_point
      rw [hnext1]
      simp only [RustM_ok_bind, rust_primitives.cmp.lt, pure_bind,
                 hcond_lt, Bool.false_eq_true, ↓reduceIte]
      rw [ufb2 (UInt8.ofNat (0xC0 ||| (c >>> 6)))]
      simp only [RustM_ok_bind]
      rw [hnext2]
      simp only [RustM_ok_bind]
      rw [uo_some (UInt8.ofNat (0x80 ||| (c &&& 0x3F)))]
      simp only [RustM_ok_bind]
      rw [uacb (UInt8.toUInt32 (UInt8.ofNat (0xC0 ||| (c >>> 6)) &&& 0x1F))
              (UInt8.ofNat (0x80 ||| (c &&& 0x3F)))]
      simp only [RustM_ok_bind, rust_primitives.cmp.ge, pure_bind,
                 hcond_ge, Bool.false_eq_true, ↓reduceIte]
      rw [hval]
      rfl
    · by_cases h3 : c < 0x10000
      · -- 3-byte.
        have henc : encodeUtf8 c
            = [UInt8.ofNat (0xE0 ||| (c >>> 12)),
               UInt8.ofNat (0x80 ||| ((c >>> 6) &&& 0x3F)),
               UInt8.ofNat (0x80 ||| (c &&& 0x3F))] := by
          unfold encodeUtf8; simp [h1, h2, h3]
        rw [henc] at hbytes
        have hcons : iterBytes it
            = UInt8.ofNat (0xE0 ||| (c >>> 12))
                :: (UInt8.ofNat (0x80 ||| ((c >>> 6) &&& 0x3F))
                    :: (UInt8.ofNat (0x80 ||| (c &&& 0x3F)) :: rest)) := by
          simpa using hbytes
        obtain ⟨it1, hnext1, hb1⟩ := next_cons it _ _ hcons
        obtain ⟨it2, hnext2, hb2⟩ := next_cons it1 _ _ hb1
        obtain ⟨it3, hnext3, hb3⟩ := next_cons it2 _ _ hb2
        refine ⟨it3, ?_, hb3⟩
        have p6 : (2:Nat)^6 = 64 := by decide
        have p8 : (2:Nat)^8 = 256 := by decide
        have p12 : (2:Nat)^12 = 4096 := by decide
        have p32 : (2:Nat)^32 = 4294967296 := by decide
        have hcdiv12 : c >>> 12 = c / 4096 := by rw [Nat.shiftRight_eq_div_pow, p12]
        have hcdiv6 : c >>> 6 = c / 64 := by rw [Nat.shiftRight_eq_div_pow, p6]
        have hb0eq : 0xE0 ||| (c >>> 12) = 224 + c / 4096 := by
          rw [hcdiv12]; exact orE0 (c / 4096) (by omega)
        have hb1eq : 0x80 ||| ((c >>> 6) &&& 0x3F) = 128 + (c / 64) % 64 := by
          rw [hcdiv6, andMod6]; exact or80 ((c / 64) % 64) (by omega)
        have hb2eq : 0x80 ||| (c &&& 0x3F) = 128 + c % 64 := by
          rw [andMod6]; exact or80 (c % 64) (by omega)
        have hb0n : (UInt8.ofNat (0xE0 ||| (c >>> 12)) : u8).toNat = 224 + c / 4096 := by
          rw [UInt8.toNat_ofNat_of_lt'
                (show 0xE0 ||| (c >>> 12) < 2 ^ 8 by rw [hb0eq, p8]; omega), hb0eq]
        have hb1n : (UInt8.ofNat (0x80 ||| ((c >>> 6) &&& 0x3F)) : u8).toNat
            = 128 + (c / 64) % 64 := by
          rw [UInt8.toNat_ofNat_of_lt'
                (show 0x80 ||| ((c >>> 6) &&& 0x3F) < 2 ^ 8 by rw [hb1eq, p8]; omega),
              hb1eq]
        have hb2n : (UInt8.ofNat (0x80 ||| (c &&& 0x3F)) : u8).toNat = 128 + c % 64 := by
          rw [UInt8.toNat_ofNat_of_lt'
                (show 0x80 ||| (c &&& 0x3F) < 2 ^ 8 by rw [hb2eq, p8]; omega), hb2eq]
        have hcl :
            decide ((UInt8.ofNat (0xE0 ||| (c >>> 12)) : u8) < (128 : u8)) = false := by
          rw [decide_eq_false_iff_not, UInt8.lt_iff_toNat_lt, hb0n]
          show ¬ (224 + c / 4096 < (128 : u8).toNat)
          have e : (128 : u8).toNat = 128 := rfl
          rw [e]; omega
        have hg224 :
            decide ((UInt8.ofNat (0xE0 ||| (c >>> 12)) : u8) ≥ (224 : u8)) = true := by
          rw [decide_eq_true_iff, ge_iff_le, UInt8.le_iff_toNat_le, hb0n]
          show (224 : u8).toNat ≤ 224 + c / 4096
          have e : (224 : u8).toNat = 224 := rfl
          rw [e]; omega
        have hg240 :
            decide ((UInt8.ofNat (0xE0 ||| (c >>> 12)) : u8) ≥ (240 : u8)) = false := by
          rw [decide_eq_false_iff_not, ge_iff_le, UInt8.le_iff_toNat_le, hb0n]
          show ¬ ((240 : u8).toNat ≤ 224 + c / 4096)
          have e : (240 : u8).toNat = 240 := rfl
          rw [e]; omega
        have hval3 :
            ((UInt8.toUInt32 (UInt8.ofNat (0xE0 ||| (c >>> 12)) &&& 0x1F) <<< (12 : UInt32))
              ||| ((UInt8.toUInt32 (UInt8.ofNat (0x80 ||| ((c >>> 6) &&& 0x3F)) &&& 0x3F)
                      <<< (6 : UInt32))
                    ||| UInt8.toUInt32 (UInt8.ofNat (0x80 ||| (c &&& 0x3F)) &&& 0x3F)))
              = UInt32.ofNat c := by
          apply UInt32.toNat.inj
          rw [bridge3 (UInt8.ofNat (0xE0 ||| (c >>> 12)))
                (UInt8.ofNat (0x80 ||| ((c >>> 6) &&& 0x3F)))
                (UInt8.ofNat (0x80 ||| (c &&& 0x3F))),
              hb0n, hb1n, hb2n,
              UInt32.toNat_ofNat_of_lt' (show c < 2 ^ 32 by rw [p32]; omega)]
          omega
        unfold next_code_point_u8.next_code_point
        rw [hnext1]
        simp only [RustM_ok_bind, rust_primitives.cmp.lt, pure_bind, hcl,
                   Bool.false_eq_true, ↓reduceIte, ufb2]
        rw [hnext2]
        simp only [RustM_ok_bind, uo_some, uacb, rust_primitives.cmp.ge,
                   pure_bind, hg224, ↓reduceIte]
        rw [hnext3]
        simp only [RustM_ok_bind, uo_some, next_code_point_u8.CONT_MASK,
                   rust_primitives.hax.cast_op, Cast.cast, uacb, shl12u,
                   pure_bind, rust_primitives.cmp.ge, hg240,
                   Bool.false_eq_true, ↓reduceIte]
        rw [hval3]
        rfl
      · -- 4-byte.
        have henc : encodeUtf8 c
            = [UInt8.ofNat (0xF0 ||| (c >>> 18)),
               UInt8.ofNat (0x80 ||| ((c >>> 12) &&& 0x3F)),
               UInt8.ofNat (0x80 ||| ((c >>> 6) &&& 0x3F)),
               UInt8.ofNat (0x80 ||| (c &&& 0x3F))] := by
          unfold encodeUtf8; simp [h1, h2, h3]
        rw [henc] at hbytes
        have hcons : iterBytes it
            = UInt8.ofNat (0xF0 ||| (c >>> 18))
                :: (UInt8.ofNat (0x80 ||| ((c >>> 12) &&& 0x3F))
                    :: (UInt8.ofNat (0x80 ||| ((c >>> 6) &&& 0x3F))
                        :: (UInt8.ofNat (0x80 ||| (c &&& 0x3F)) :: rest))) := by
          simpa using hbytes
        obtain ⟨it1, hnext1, hb1⟩ := next_cons it _ _ hcons
        obtain ⟨it2, hnext2, hb2⟩ := next_cons it1 _ _ hb1
        obtain ⟨it3, hnext3, hb3⟩ := next_cons it2 _ _ hb2
        obtain ⟨it4, hnext4, hb4⟩ := next_cons it3 _ _ hb3
        refine ⟨it4, ?_, hb4⟩
        have p6 : (2:Nat)^6 = 64 := by decide
        have p8 : (2:Nat)^8 = 256 := by decide
        have p12 : (2:Nat)^12 = 4096 := by decide
        have p18 : (2:Nat)^18 = 262144 := by decide
        have p32 : (2:Nat)^32 = 4294967296 := by decide
        have hcdiv18 : c >>> 18 = c / 262144 := by rw [Nat.shiftRight_eq_div_pow, p18]
        have hcdiv12 : c >>> 12 = c / 4096 := by rw [Nat.shiftRight_eq_div_pow, p12]
        have hcdiv6 : c >>> 6 = c / 64 := by rw [Nat.shiftRight_eq_div_pow, p6]
        have hb0eq : 0xF0 ||| (c >>> 18) = 240 + c / 262144 := by
          rw [hcdiv18]; exact orF0 (c / 262144) (by omega)
        have hb1eq : 0x80 ||| ((c >>> 12) &&& 0x3F) = 128 + (c / 4096) % 64 := by
          rw [hcdiv12, andMod6]; exact or80 ((c / 4096) % 64) (by omega)
        have hb2eq : 0x80 ||| ((c >>> 6) &&& 0x3F) = 128 + (c / 64) % 64 := by
          rw [hcdiv6, andMod6]; exact or80 ((c / 64) % 64) (by omega)
        have hb3eq : 0x80 ||| (c &&& 0x3F) = 128 + c % 64 := by
          rw [andMod6]; exact or80 (c % 64) (by omega)
        have hb0n : (UInt8.ofNat (0xF0 ||| (c >>> 18)) : u8).toNat = 240 + c / 262144 := by
          rw [UInt8.toNat_ofNat_of_lt'
                (show 0xF0 ||| (c >>> 18) < 2 ^ 8 by rw [hb0eq, p8]; omega), hb0eq]
        have hb1n : (UInt8.ofNat (0x80 ||| ((c >>> 12) &&& 0x3F)) : u8).toNat
            = 128 + (c / 4096) % 64 := by
          rw [UInt8.toNat_ofNat_of_lt'
                (show 0x80 ||| ((c >>> 12) &&& 0x3F) < 2 ^ 8 by rw [hb1eq, p8]; omega),
              hb1eq]
        have hb2n : (UInt8.ofNat (0x80 ||| ((c >>> 6) &&& 0x3F)) : u8).toNat
            = 128 + (c / 64) % 64 := by
          rw [UInt8.toNat_ofNat_of_lt'
                (show 0x80 ||| ((c >>> 6) &&& 0x3F) < 2 ^ 8 by rw [hb2eq, p8]; omega),
              hb2eq]
        have hb3n : (UInt8.ofNat (0x80 ||| (c &&& 0x3F)) : u8).toNat = 128 + c % 64 := by
          rw [UInt8.toNat_ofNat_of_lt'
                (show 0x80 ||| (c &&& 0x3F) < 2 ^ 8 by rw [hb3eq, p8]; omega), hb3eq]
        have hcl :
            decide ((UInt8.ofNat (0xF0 ||| (c >>> 18)) : u8) < (128 : u8)) = false := by
          rw [decide_eq_false_iff_not, UInt8.lt_iff_toNat_lt, hb0n]
          show ¬ (240 + c / 262144 < (128 : u8).toNat)
          have e : (128 : u8).toNat = 128 := rfl
          rw [e]; omega
        have hg224 :
            decide ((UInt8.ofNat (0xF0 ||| (c >>> 18)) : u8) ≥ (224 : u8)) = true := by
          rw [decide_eq_true_iff, ge_iff_le, UInt8.le_iff_toNat_le, hb0n]
          show (224 : u8).toNat ≤ 240 + c / 262144
          have e : (224 : u8).toNat = 224 := rfl
          rw [e]; omega
        have hg240 :
            decide ((UInt8.ofNat (0xF0 ||| (c >>> 18)) : u8) ≥ (240 : u8)) = true := by
          rw [decide_eq_true_iff, ge_iff_le, UInt8.le_iff_toNat_le, hb0n]
          show (240 : u8).toNat ≤ 240 + c / 262144
          have e : (240 : u8).toNat = 240 := rfl
          rw [e]; omega
        have hval4 :
            (((UInt8.toUInt32 (UInt8.ofNat (0xF0 ||| (c >>> 18)) &&& 0x1F) &&& 7)
                <<< (18 : UInt32))
              ||| (((UInt8.toUInt32 (UInt8.ofNat (0x80 ||| ((c >>> 12) &&& 0x3F)) &&& 0x3F)
                      <<< (6 : UInt32))
                      ||| UInt8.toUInt32 (UInt8.ofNat (0x80 ||| ((c >>> 6) &&& 0x3F)) &&& 0x3F))
                    <<< (6 : UInt32)
                  ||| UInt8.toUInt32 (UInt8.ofNat (0x80 ||| (c &&& 0x3F)) &&& 0x3F)))
              = UInt32.ofNat c := by
          apply UInt32.toNat.inj
          rw [bridge4 (UInt8.ofNat (0xF0 ||| (c >>> 18)))
                (UInt8.ofNat (0x80 ||| ((c >>> 12) &&& 0x3F)))
                (UInt8.ofNat (0x80 ||| ((c >>> 6) &&& 0x3F)))
                (UInt8.ofNat (0x80 ||| (c &&& 0x3F))),
              hb0n, hb1n, hb2n, hb3n,
              UInt32.toNat_ofNat_of_lt' (show c < 2 ^ 32 by rw [p32]; omega)]
          omega
        unfold next_code_point_u8.next_code_point
        rw [hnext1]
        simp only [RustM_ok_bind, rust_primitives.cmp.lt, pure_bind, hcl,
                   Bool.false_eq_true, ↓reduceIte, ufb2]
        rw [hnext2]
        simp only [RustM_ok_bind, uo_some, uacb, rust_primitives.cmp.ge,
                   pure_bind, hg224, ↓reduceIte]
        rw [hnext3]
        simp only [RustM_ok_bind, uo_some, next_code_point_u8.CONT_MASK,
                   rust_primitives.hax.cast_op, Cast.cast, uacb, shl12u,
                   pure_bind, rust_primitives.cmp.ge, hg240, ↓reduceIte]
        rw [hnext4]
        simp only [RustM_ok_bind, uo_some, rust_primitives.hax.cast_op,
                   Cast.cast, uacb, shl18u, pure_bind]
        rw [hval4]
        rfl

/-! ## Obligations.

The extracted body of `next_code_point` is a real (non-stubbed) decoder:
it threads the `core_models.slice.iter.Iter u8` through up to four
`Iterator::next` calls, applies `unwrap_or 0` to the `Option u8` results,
and reassembles the scalar with `utf8_first_byte` / `utf8_acc_cont_byte`
across the 1/2/3/4-byte width branches. The statements below pin the full
contract surface exercised by the two property tests
(`prop_roundtrip_every_scalar_value`, `prop_sequence_matches_chars_iterator`)
and the example-based tests (which are concrete instances of these
clauses). -/

/-- POSTCONDITION (decoded scalar value). Captures the value assertion of
    `prop_roundtrip_every_scalar_value` (`cp == Some(u)` over the entire
    Unicode scalar domain — every width and every range boundary,
    surrogates excluded) and, with a non-empty `rest`, the per-call value
    assertion of `prop_sequence_matches_chars_iterator`
    (`next_code_point == Some(expected as u32)` even when more code points
    follow): if the iterator's remaining bytes begin with the UTF-8
    encoding of the scalar `c`, the call returns `Some (c as u32)`. This
    simultaneously pins all four width branches and the
    `utf8_first_byte` / `utf8_acc_cont_byte` reconstruction. A decoder
    returning any other scalar, or mis-counting continuation bytes, would
    falsify it. (The example tests `two_byte_codepoint_copyright`,
    `three_byte_codepoint_bmp`, `four_byte_codepoint_supplementary`,
    `ascii_byte_returns_single_codepoint` are concrete instances.) -/
theorem next_code_point_decodes_scalar_value
    (it : core_models.slice.iter.Iter u8) (c : Nat) (rest : List u8)
    (hc : c ≤ 0x10FFFF)
    (hsurr : c < 0xD800 ∨ 0xDFFF < c)
    (hbytes : iterBytes it = encodeUtf8 c ++ rest) :
    ∃ it' : core_models.slice.iter.Iter u8,
      next_code_point_u8.next_code_point it
        = RustM.ok (rust_primitives.hax.Tuple2.mk it'
            (core_models.option.Option.Some (UInt32.ofNat c))) := by
  obtain ⟨it', he, _⟩ := decode_correct it c rest hc hbytes
  exact ⟨it', he⟩

/-- POSTCONDITION (consumes exactly one code point's encoding). With
    `rest = []` this is the "iterator empty afterwards / full encoding
    consumed" assertion of `prop_roundtrip_every_scalar_value`
    (`remaining == 0`, i.e. not too few / not too many bytes read); with
    an arbitrary suffix `rest` it is the independent advancement / no-desync
    claim of `prop_sequence_matches_chars_iterator` (each call advances the
    shared iterator by precisely one code point's UTF-8 width, neither
    over- nor under-reading into the following code point). After the call
    the returned iterator yields exactly `rest`. -/
theorem next_code_point_advances_by_encoding
    (it it' : core_models.slice.iter.Iter u8) (c : Nat) (rest : List u8)
    (o : core_models.option.Option u32)
    (hc : c ≤ 0x10FFFF)
    (hsurr : c < 0xD800 ∨ 0xDFFF < c)
    (hbytes : iterBytes it = encodeUtf8 c ++ rest)
    (hstep : next_code_point_u8.next_code_point it
              = RustM.ok (rust_primitives.hax.Tuple2.mk it' o)) :
    iterBytes it' = rest := by
  obtain ⟨it'', he, hb⟩ := decode_correct it c rest hc hbytes
  rw [he] at hstep
  injection hstep with k0
  injection k0 with k1
  injection k1 with kit ko
  have hit : it' = it'' := kit.symm
  rw [hit]
  exact hb

/-- FAILURE / TERMINATION condition. Captures `empty_iterator_returns_none`
    and the end-of-input termination of
    `prop_sequence_matches_chars_iterator` (`next_code_point == None` once
    the buffer is exhausted): on an empty iterator the function does not
    panic — it returns `Ok None`. The first `Iterator::next` yields `None`
    via the `seq_len = 0` branch and the function short-circuits. -/
theorem next_code_point_empty_returns_none
    (it : core_models.slice.iter.Iter u8)
    (hempty : iterBytes it = []) :
    ∃ it' : core_models.slice.iter.Iter u8,
      next_code_point_u8.next_code_point it
        = RustM.ok (rust_primitives.hax.Tuple2.mk it'
            core_models.option.Option.None) := by
  exact ⟨it, next_code_point_nil it (size_zero_of_iterBytes_nil it hempty)⟩

/-- TERMINATION stability. Captures the final clause of
    `prop_sequence_matches_chars_iterator` (`end_again == None` — `None`
    remains stable on further calls): once the iterator is exhausted, a
    subsequent call still returns `None`. The model's `None` branch leaves
    the iterator unchanged, so the iterator returned by the first
    exhausted call (`it'`) is still empty and a further call is again
    `None`. Independent of the first decode's value. -/
theorem next_code_point_none_is_stable
    (it it' : core_models.slice.iter.Iter u8)
    (o : core_models.option.Option u32)
    (hempty : iterBytes it = [])
    (hstep : next_code_point_u8.next_code_point it
              = RustM.ok (rust_primitives.hax.Tuple2.mk it' o)) :
    ∃ it'' : core_models.slice.iter.Iter u8,
      next_code_point_u8.next_code_point it'
        = RustM.ok (rust_primitives.hax.Tuple2.mk it''
            core_models.option.Option.None) := by
  have hsz := size_zero_of_iterBytes_nil it hempty
  have key := next_code_point_nil it hsz
  rw [hstep] at key
  -- key : RustM.ok (Tuple2.mk it' o) = RustM.ok (Tuple2.mk it None)
  injection key with k0
  injection k0 with k1
  injection k1 with kit ko
  rw [kit]
  exact ⟨it, next_code_point_nil it hsz⟩

end Next_code_point_u8Obligations
