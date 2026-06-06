-- Companion obligations file for the `big_endian_write_u64_into` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import big_endian_write_u64_into

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6400000

namespace Big_endian_write_u64_intoObligations

/-! ## Specification oracle: big-endian byte extraction.

`beByte n j` is the `j`-th byte (counting from the most-significant end,
`j = 0` is the top byte) of the 64-bit value `n`, written big-endian.
Expressed at the `Nat` level — `(n / 2^(8*(7-j))) % 256` — independent of
the implementation's `(n >> k) as u8` shift/narrowing-cast form, so the
postcondition is a genuine semantic specification rather than a restatement
of the code. This is exactly the `((value >> (8*(7-j))) & 0xff) as u8`
expression spelled out independently in the Rust property test
`prop_writes_big_endian_bytes`; a little-endian (or otherwise
byte-permuted) implementation fails against this oracle. (`byteorder` doc:
`BigEndian::write_u64_into` writes each `u64` of `src` in big-endian order
into the corresponding 8-byte chunk of `dst`.) -/
private def beByte (n : u64) (j : Nat) : Nat :=
  (n.toNat / 2 ^ (8 * (7 - j))) % 256

/-! ## Generic scaffolding (pattern reused from `big_endian_read_u64_into`,
`big_endian_write_u64`, `big_endian_from_slice_u64`, `clever_009_rolling_max`). -/

/-- `RustM.ok x >>= f = f x`. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl
private theorem ulit8 : (8 : usize).toNat = 8 := by decide
private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide
private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide
private theorem eight_lt_usize_size : (8 : Nat) < USize64.size := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

/-- `usize` multiplication without overflow (mirror of `read_u64_into`'s
    `mul_ok`). -/
private theorem mul_ok (base k : usize) (h : base.toNat * k.toNat < 2^64) :
    (base *? k : RustM usize) = RustM.ok (base * k) := by
  show (rust_primitives.ops.arith.Mul.mul base k : RustM usize) = RustM.ok (base * k)
  show (if BitVec.umulOverflow base.toBitVec k.toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure (base * k)) = _
  have hbv : BitVec.umulOverflow base.toBitVec k.toBitVec = false := by
    generalize hbo : BitVec.umulOverflow base.toBitVec k.toBitVec = bo
    cases bo with
    | false => rfl
    | true => exact absurd ((USize64.umulOverflow_iff base k).mp hbo) (by omega)
  rw [hbv]; rfl

/-- Right-shift by a valid constant amount (mirror of `big_endian_write_u64`'s
    `shr_ok`). -/
private theorem shr_ok (x : u64) (k : i32) (hk : (0 ≤ k && k < 64) = true) :
    (x >>>? k : RustM u64) = RustM.ok (x >>> (k.toNatClampNeg.toUInt64)) := by
  show (rust_primitives.ops.bit.Shr.shr x k : RustM u64) = _
  show (if (0 ≤ k && k < 64)
        then pure (x >>> (k.toNatClampNeg.toUInt64))
        else (.fail .integerOverflow : RustM u64)) = _
  rw [hk]; rfl

/-- The narrowing `u64 → u8` cast. -/
private theorem cast_ok (m : u64) :
    (rust_primitives.hax.cast_op m : RustM u8) = RustM.ok (UInt64.toUInt8 m) := rfl

/-- Indexing a `u64` slice in-bounds. -/
private theorem idx_ok (src : RustSlice u64) (v : usize)
    (h : v.toNat < src.val.size) :
    (src[v]_? : RustM u64) = RustM.ok (src.val[v.toNat]'h) := by
  show (if h : v.toNat < src.val.size then pure (src.val[v])
          else .fail .arrayOutOfBounds) = RustM.ok (src.val[v.toNat]'h)
  rw [dif_pos h]; rfl

/-! ## Big-endian byte array (pattern from `big_endian_write_u64`).

The inline `chunk` in `build_output` is built from eight `(n >>> k) as u8`
narrowing casts.  After reducing the modeled shift (`>>>?`) and narrowing
cast (`cast_op`), the array is exactly `beArr n`. -/
private def beArr (n : u64) : RustArray u8 8 :=
  RustArray.ofVec #v[
    UInt64.toUInt8 (n >>> (56 : UInt64)),
    UInt64.toUInt8 (n >>> (48 : UInt64)),
    UInt64.toUInt8 (n >>> (40 : UInt64)),
    UInt64.toUInt8 (n >>> (32 : UInt64)),
    UInt64.toUInt8 (n >>> (24 : UInt64)),
    UInt64.toUInt8 (n >>> (16 : UInt64)),
    UInt64.toUInt8 (n >>> (8 : UInt64)),
    UInt64.toUInt8 n]

private theorem beArr_toArray_size (n : u64) :
    ((beArr n).toVec.toArray).size = 8 := by simp [beArr]

/-- The `Seq` wrapper produced by `unsize (beArr n)`. -/
private def beSeq (n : u64) : rust_primitives.sequence.Seq u8 :=
  ⟨(beArr n).toVec.toArray, by rw [beArr_toArray_size]; exact eight_lt_usize_size⟩

/-- The narrowing cast of a right-shift, at the `Nat` level: a single byte
    extraction.  Bridged from the `BitVec` form (`setWidth 8` of a
    `ushiftRight`) discharged by `bv_decide`. -/
private theorem byte_toNat_of_bv (n : u64) (b : u8) (E : Nat)
    (hbv : b.toBitVec = (n.toBitVec >>> E).setWidth 8) :
    b.toNat = (n.toNat / 2 ^ E) % 256 := by
  have h := congrArg BitVec.toNat hbv
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
             Nat.shiftRight_eq_div_pow] at h
  simpa using h

private theorem be0 (n : u64) :
    (UInt64.toUInt8 (n >>> (56 : UInt64))).toNat = beByte n 0 := by
  have h := byte_toNat_of_bv n (UInt64.toUInt8 (n >>> (56 : UInt64))) 56 (by bv_decide)
  simpa [beByte] using h

private theorem be1 (n : u64) :
    (UInt64.toUInt8 (n >>> (48 : UInt64))).toNat = beByte n 1 := by
  have h := byte_toNat_of_bv n (UInt64.toUInt8 (n >>> (48 : UInt64))) 48 (by bv_decide)
  simpa [beByte] using h

private theorem be2 (n : u64) :
    (UInt64.toUInt8 (n >>> (40 : UInt64))).toNat = beByte n 2 := by
  have h := byte_toNat_of_bv n (UInt64.toUInt8 (n >>> (40 : UInt64))) 40 (by bv_decide)
  simpa [beByte] using h

private theorem be3 (n : u64) :
    (UInt64.toUInt8 (n >>> (32 : UInt64))).toNat = beByte n 3 := by
  have h := byte_toNat_of_bv n (UInt64.toUInt8 (n >>> (32 : UInt64))) 32 (by bv_decide)
  simpa [beByte] using h

private theorem be4 (n : u64) :
    (UInt64.toUInt8 (n >>> (24 : UInt64))).toNat = beByte n 4 := by
  have h := byte_toNat_of_bv n (UInt64.toUInt8 (n >>> (24 : UInt64))) 24 (by bv_decide)
  simpa [beByte] using h

private theorem be5 (n : u64) :
    (UInt64.toUInt8 (n >>> (16 : UInt64))).toNat = beByte n 5 := by
  have h := byte_toNat_of_bv n (UInt64.toUInt8 (n >>> (16 : UInt64))) 16 (by bv_decide)
  simpa [beByte] using h

private theorem be6 (n : u64) :
    (UInt64.toUInt8 (n >>> (8 : UInt64))).toNat = beByte n 6 := by
  have h := byte_toNat_of_bv n (UInt64.toUInt8 (n >>> (8 : UInt64))) 8 (by bv_decide)
  simpa [beByte] using h

private theorem be7 (n : u64) :
    (UInt64.toUInt8 n).toNat = beByte n 7 := by
  have h := byte_toNat_of_bv n (UInt64.toUInt8 n) 0 (by bv_decide)
  simpa [beByte] using h

/-- The `j`-th element of `(beArr n).toVec.toArray` decodes to the
    big-endian oracle. -/
private theorem beArr_get_toNat (n : u64) (j : Nat) (hj : j < 8)
    (h : j < ((beArr n).toVec.toArray).size) :
    (((beArr n).toVec.toArray)[j]'h).toNat = beByte n j := by
  have hcases :
      j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases hcases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · simpa [beArr] using be0 n
  · simpa [beArr] using be1 n
  · simpa [beArr] using be2 n
  · simpa [beArr] using be3 n
  · simpa [beArr] using be4 n
  · simpa [beArr] using be5 n
  · simpa [beArr] using be6 n
  · simpa [beArr] using be7 n

/-- Append the 8 big-endian bytes of `n` (one `extend_from_slice` step). -/
private def push8 (acc : alloc.vec.Vec u8 alloc.alloc.Global) (n : u64)
    (h : acc.val.size + 8 < USize64.size) :
    alloc.vec.Vec u8 alloc.alloc.Global :=
  ⟨acc.val ++ (beArr n).toVec.toArray, by
    rw [Array.size_append, beArr_toArray_size]; exact h⟩

/-! ## `build_output` step lemmas. -/

private theorem build_output_oob
    (src : RustSlice u64) (i : usize)
    (acc : alloc.vec.Vec u8 alloc.alloc.Global)
    (hi : src.val.size ≤ i.toNat) :
    big_endian_write_u64_into.build_output src i acc = RustM.ok acc := by
  conv => lhs; unfold big_endian_write_u64_into.build_output
  have h_ofNat : (USize64.ofNat src.val.size).toNat = src.val.size :=
    USize64.toNat_ofNat_of_lt' src.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat src.val.size ≤ i) = true := by
    rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, h_cond, ↓reduceIte]
  rfl

private theorem build_output_step
    (src : RustSlice u64) (i : usize)
    (acc : alloc.vec.Vec u8 alloc.alloc.Global)
    (hi : i.toNat < src.val.size)
    (h_acc : acc.val.size + 8 < USize64.size) :
    big_endian_write_u64_into.build_output src i acc =
      big_endian_write_u64_into.build_output src (i + 1)
        (push8 acc (src.val[i.toNat]'hi) h_acc) := by
  conv => lhs; unfold big_endian_write_u64_into.build_output
  have h_size_lt : src.val.size < USize64.size := src.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat src.val.size).toNat = src.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat src.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx :
      (src[i]_? : RustM u64) = RustM.ok (src.val[i.toNat]'hi) := idx_ok src i hi
  have h_no_ov_i : i.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_size_lt; omega
  have h_no_bv_i :
      BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hii := (USize64.uaddOverflow_iff i 1).mp hbo
      rw [usize_one_toNat] at hii
      omega
  have h_add_eq : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
    show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
    show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
          then (.fail .integerOverflow : RustM usize)
          else pure (i + 1)) = _
    rw [h_no_bv_i]; rfl
  have hs56 : (0 ≤ (56 : i32) && (56 : i32) < 64) = true := by decide
  have hs48 : (0 ≤ (48 : i32) && (48 : i32) < 64) = true := by decide
  have hs40 : (0 ≤ (40 : i32) && (40 : i32) < 64) = true := by decide
  have hs32 : (0 ≤ (32 : i32) && (32 : i32) < 64) = true := by decide
  have hs24 : (0 ≤ (24 : i32) && (24 : i32) < 64) = true := by decide
  have hs16 : (0 ≤ (16 : i32) && (16 : i32) < 64) = true := by decide
  have hs8  : (0 ≤ (8 : i32) && (8 : i32) < 64) = true := by decide
  have e56 : ((56 : i32).toNatClampNeg).toUInt64 = (56 : UInt64) := by decide
  have e48 : ((48 : i32).toNatClampNeg).toUInt64 = (48 : UInt64) := by decide
  have e40 : ((40 : i32).toNatClampNeg).toUInt64 = (40 : UInt64) := by decide
  have e32 : ((32 : i32).toNatClampNeg).toUInt64 = (32 : UInt64) := by decide
  have e24 : ((24 : i32).toNatClampNeg).toUInt64 = (24 : UInt64) := by decide
  have e16 : ((16 : i32).toNatClampNeg).toUInt64 = (16 : UInt64) := by decide
  have e8  : ((8 : i32).toNatClampNeg).toUInt64 = (8 : UInt64) := by decide
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte, h_idx,
             shr_ok _ (56 : i32) hs56, shr_ok _ (48 : i32) hs48,
             shr_ok _ (40 : i32) hs40, shr_ok _ (32 : i32) hs32,
             shr_ok _ (24 : i32) hs24, shr_ok _ (16 : i32) hs16,
             shr_ok _ (8 : i32) hs8,
             e56, e48, e40, e32, e24, e16, e8, cast_ok]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[
                  UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (56 : UInt64)),
                  UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (48 : UInt64)),
                  UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (40 : UInt64)),
                  UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (32 : UInt64)),
                  UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (24 : UInt64)),
                  UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (16 : UInt64)),
                  UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (8 : UInt64)),
                  UInt64.toUInt8 (src.val[i.toNat]'hi)] : RustArray u8 8)
              : RustM (rust_primitives.sequence.Seq u8))
            = RustM.ok (beSeq (src.val[i.toNat]'hi)) from rfl]
  simp only [RustM_ok_bind]
  rw [show (alloc.vec.Impl_2.extend_from_slice u8 alloc.alloc.Global acc
              (beSeq (src.val[i.toNat]'hi))
            : RustM (alloc.vec.Vec u8 alloc.alloc.Global))
        = RustM.ok (push8 acc (src.val[i.toNat]'hi) h_acc) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos (show acc.val.size + (beSeq (src.val[i.toNat]'hi)).val.size
                      < USize64.size from by
      have hv : (beSeq (src.val[i.toNat]'hi)).val.size = 8 := by
        show ((beArr (src.val[i.toNat]'hi)).toVec.toArray).size = 8
        exact beArr_toArray_size _
      rw [hv]; exact h_acc)]
    rfl]
  simp only [RustM_ok_bind]
  rw [h_add_eq]
  rfl

/-! ## Strong induction for `build_output` (mirrors `build_values_correct`
from `big_endian_read_u64_into`, generalised to 8-byte chunks).

Invariant: `acc.val.size = i.toNat * 8`, and for every word index `c` and
byte position `j < 8` already emitted, `acc[c*8+j]` is the `j`-th
big-endian byte of `src[c]`. -/

private theorem build_output_correct (src : RustSlice u64)
    (hsrc8 : src.val.size * 8 < USize64.size) :
    ∀ (k : Nat) (i : usize) (acc : alloc.vec.Vec u8 alloc.alloc.Global),
      src.val.size - i.toNat ≤ k →
      i.toNat ≤ src.val.size →
      acc.val.size = i.toNat * 8 →
      (∀ (c j : Nat) (hpos : c * 8 + j < acc.val.size)
          (hc : c < src.val.size) (hj : j < 8),
          ((acc.val[c * 8 + j]'hpos).toNat = beByte (src.val[c]'hc) j)) →
      ∃ v : alloc.vec.Vec u8 alloc.alloc.Global,
        big_endian_write_u64_into.build_output src i acc = RustM.ok v ∧
        v.val.size = src.val.size * 8 ∧
        (∀ (c j : Nat) (hpos : c * 8 + j < v.val.size)
            (hc : c < src.val.size) (hj : j < 8),
            ((v.val[c * 8 + j]'hpos).toNat = beByte (src.val[c]'hc) j)) := by
  have h_size_lt : src.val.size < USize64.size := src.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  intro k
  induction k with
  | zero =>
    intro i acc hk hi_le h_acc_size h_acc_chunk
    have hi_eq : i.toNat = src.val.size := by omega
    have hi_ge : src.val.size ≤ i.toNat := by omega
    refine ⟨acc, build_output_oob src i acc hi_ge, ?_, ?_⟩
    · rw [h_acc_size, hi_eq]
    · intro c j hpos hc hj; exact h_acc_chunk c j hpos hc hj
  | succ k ih =>
    intro i acc hk hi_le h_acc_size h_acc_chunk
    by_cases hi_ge : src.val.size ≤ i.toNat
    · have hi_eq : i.toNat = src.val.size := by omega
      refine ⟨acc, build_output_oob src i acc hi_ge, ?_, ?_⟩
      · rw [h_acc_size, hi_eq]
      · intro c j hpos hc hj; exact h_acc_chunk c j hpos hc hj
    · have hi_lt : i.toNat < src.val.size := Nat.lt_of_not_le hi_ge
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_acc_succ : acc.val.size + 8 < USize64.size := by
        rw [h_acc_size]; omega
      have h_step := build_output_step src i acc hi_lt h_acc_succ
      rw [h_step]
      have h_push8_size :
          (push8 acc (src.val[i.toNat]'hi_lt) h_acc_succ).val.size
            = acc.val.size + 8 := by
        show (acc.val ++ (beArr (src.val[i.toNat]'hi_lt)).toVec.toArray).size
              = acc.val.size + 8
        rw [Array.size_append, beArr_toArray_size]
      have h_acc'_size :
          (push8 acc (src.val[i.toNat]'hi_lt) h_acc_succ).val.size
            = (i + 1).toNat * 8 := by
        rw [h_push8_size, h_acc_size, h_i1]; omega
      have h_acc'_chunk :
          ∀ (c j : Nat)
            (hpos : c * 8 + j
                < (push8 acc (src.val[i.toNat]'hi_lt) h_acc_succ).val.size)
            (hc : c < src.val.size) (hj : j < 8),
            (((push8 acc (src.val[i.toNat]'hi_lt) h_acc_succ).val[c * 8 + j]'hpos).toNat
              = beByte (src.val[c]'hc) j) := by
        intro c j hpos hc hj
        have hpos' : c * 8 + j < acc.val.size + 8 := by
          rw [h_push8_size] at hpos; exact hpos
        show ((acc.val ++ (beArr (src.val[i.toNat]'hi_lt)).toVec.toArray)[c * 8 + j]'hpos).toNat
              = beByte (src.val[c]'hc) j
        by_cases hclt : c < i.toNat
        · have hlt : c * 8 + j < acc.val.size := by
            rw [h_acc_size]; omega
          rw [Array.getElem_append_left hlt]
          exact h_acc_chunk c j hlt hc hj
        · have hc_eq : c = i.toNat := by
            rw [h_acc_size] at hpos'; omega
          have hsrc_eq : src.val[c]'hc = src.val[i.toNat]'hi_lt :=
            getElem_congr_idx hc_eq
          rw [hsrc_eq]
          have hge : acc.val.size ≤ c * 8 + j := by
            rw [h_acc_size]; omega
          rw [Array.getElem_append_right hge]
          have hsub : c * 8 + j - acc.val.size = j := by
            rw [h_acc_size]; omega
          have hidx :
              ((beArr (src.val[i.toNat]'hi_lt)).toVec.toArray)[c * 8 + j - acc.val.size]'(by
                  rw [hsub, beArr_toArray_size]; exact hj)
                = ((beArr (src.val[i.toNat]'hi_lt)).toVec.toArray)[j]'(by
                  rw [beArr_toArray_size]; exact hj) :=
            getElem_congr_idx hsub
          rw [hidx]
          exact beArr_get_toNat (src.val[i.toNat]'hi_lt) j hj
                  (by rw [beArr_toArray_size]; exact hj)
      have h_i1_le : (i + 1).toNat ≤ src.val.size := by rw [h_i1]; omega
      have h_k_le : src.val.size - (i + 1).toNat ≤ k := by rw [h_i1]; omega
      exact ih (i + 1) (push8 acc (src.val[i.toNat]'hi_lt) h_acc_succ)
              h_k_le h_i1_le h_acc'_size h_acc'_chunk

/-! ## Top-level reduction.

`write_u64_into` asserts `src.len()*8 == dst.len()`, then builds the
big-endian image from the empty `Vec` and writes it back with
`copy_from_slice` (which returns its `src` argument via `mem.replace`). -/

private theorem write_u64_into_eq_build (src : RustSlice u64) (dst : RustSlice u8)
    (hpre : dst.val.size = src.val.size * 8) :
    big_endian_write_u64_into.write_u64_into src dst
      = big_endian_write_u64_into.build_output src (0 : usize)
          ⟨(List.nil).toArray, by grind⟩ := by
  have hsz : src.val.size < USize64.size := src.size_lt_usizeSize
  have hszN : src.val.size < 2 ^ 64 := by rw [← usize_size_eq]; exact hsz
  have hdsz : dst.val.size < USize64.size := dst.size_lt_usizeSize
  have hsrc8N : src.val.size * 8 < 2 ^ 64 := by
    rw [← usize_size_eq, ← hpre]; exact hdsz
  have h_len_src :
      (core_models.slice.Impl.len u64 src : RustM usize)
        = RustM.ok (USize64.ofNat src.val.size) := rfl
  have h_len_dst :
      (core_models.slice.Impl.len u8 dst : RustM usize)
        = RustM.ok (USize64.ofNat dst.val.size) := rfl
  have h_mul :
      ((USize64.ofNat src.val.size) *? (8 : usize) : RustM usize)
        = RustM.ok (USize64.ofNat src.val.size * 8) := by
    apply mul_ok
    rw [USize64.toNat_ofNat_of_lt' hsz, ulit8]; exact hsrc8N
  have h_eq_bool :
      ((USize64.ofNat src.val.size * 8) == (USize64.ofNat dst.val.size)) = true := by
    rw [beq_iff_eq]
    apply USize64.toNat_inj.mp
    rw [USize64.toNat_mul_of_lt (by rw [USize64.toNat_ofNat_of_lt' hsz, ulit8]; exact hsrc8N),
        USize64.toNat_ofNat_of_lt' hsz, ulit8, USize64.toNat_ofNat_of_lt' hdsz]
    omega
  have h_new :
      (alloc.vec.Impl.new u8 rust_primitives.hax.Tuple0.mk
        : RustM (alloc.vec.Vec u8 alloc.alloc.Global))
        = RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  unfold big_endian_write_u64_into.write_u64_into
  simp only [h_len_src, h_len_dst, RustM_ok_bind, h_mul,
             rust_primitives.cmp.eq, h_eq_bool, hax_lib.assert, ↓reduceIte,
             pure_bind, h_new, core_models.ops.deref.Deref.deref,
             core_models.slice.Impl.copy_from_slice, rust_primitives.mem.replace,
             bind_pure]

private theorem write_u64_into_fail_aux (src : RustSlice u64) (dst : RustSlice u8)
    (hno : src.val.size * 8 < USize64.size)
    (hmis : src.val.size * 8 ≠ dst.val.size) :
    big_endian_write_u64_into.write_u64_into src dst
      = RustM.fail Error.assertionFailure := by
  have hsz : src.val.size < USize64.size := src.size_lt_usizeSize
  have hdsz : dst.val.size < USize64.size := dst.size_lt_usizeSize
  have hnoN : src.val.size * 8 < 2 ^ 64 := by rw [← usize_size_eq]; exact hno
  have h_len_src :
      (core_models.slice.Impl.len u64 src : RustM usize)
        = RustM.ok (USize64.ofNat src.val.size) := rfl
  have h_len_dst :
      (core_models.slice.Impl.len u8 dst : RustM usize)
        = RustM.ok (USize64.ofNat dst.val.size) := rfl
  have h_mul :
      ((USize64.ofNat src.val.size) *? (8 : usize) : RustM usize)
        = RustM.ok (USize64.ofNat src.val.size * 8) := by
    apply mul_ok
    rw [USize64.toNat_ofNat_of_lt' hsz, ulit8]; exact hnoN
  have h_eq_bool :
      ((USize64.ofNat src.val.size * 8) == (USize64.ofNat dst.val.size)) = false := by
    rw [← Bool.not_eq_true, beq_iff_eq]
    intro hC
    apply hmis
    have := congrArg USize64.toNat hC
    rw [USize64.toNat_mul_of_lt (by rw [USize64.toNat_ofNat_of_lt' hsz, ulit8]; exact hnoN),
        USize64.toNat_ofNat_of_lt' hsz, ulit8, USize64.toNat_ofNat_of_lt' hdsz] at this
    exact this
  unfold big_endian_write_u64_into.write_u64_into
  simp only [h_len_src, h_len_dst, RustM_ok_bind, h_mul,
             rust_primitives.cmp.eq, h_eq_bool, hax_lib.assert,
             Bool.false_eq_true, ↓reduceIte, pure_bind]
  rfl

private theorem write_u64_into_aux (src : RustSlice u64) (dst : RustSlice u8)
    (hpre : dst.val.size = src.val.size * 8) :
    ∃ v : RustSlice u8,
      big_endian_write_u64_into.write_u64_into src dst = RustM.ok v ∧
      v.val.size = src.val.size * 8 ∧
      (∀ (c j : Nat) (hpos : c * 8 + j < v.val.size)
          (hc : c < src.val.size) (hj : j < 8),
          ((v.val[c * 8 + j]'hpos).toNat = beByte (src.val[c]'hc) j)) := by
  have hdsz : dst.val.size < USize64.size := dst.size_lt_usizeSize
  have hsrc8 : src.val.size * 8 < USize64.size := by rw [← hpre]; exact hdsz
  rw [write_u64_into_eq_build src dst hpre]
  have h_acc0_size :
      (⟨(List.nil).toArray, by grind⟩
        : alloc.vec.Vec u8 alloc.alloc.Global).val.size = (0 : usize).toNat := rfl
  have h_acc0_chunk :
      ∀ (c j : Nat)
        (hpos : c * 8 + j < (⟨(List.nil).toArray, by grind⟩
                    : alloc.vec.Vec u8 alloc.alloc.Global).val.size)
        (hc : c < src.val.size) (hj : j < 8),
        (((⟨(List.nil).toArray, by grind⟩
            : alloc.vec.Vec u8 alloc.alloc.Global).val[c * 8 + j]'hpos).toNat
          = beByte (src.val[c]'hc) j) := by
    intro c j hpos hc hj; exact absurd hpos (by simp)
  have h_m_le : src.val.size - (0 : usize).toNat ≤ src.val.size := by
    show src.val.size - 0 ≤ src.val.size; omega
  have h_i_le : (0 : usize).toNat ≤ src.val.size := by
    show 0 ≤ src.val.size; omega
  obtain ⟨v, hv, hv_size, hv_chunk⟩ :=
    build_output_correct src hsrc8 src.val.size (0 : usize)
      ⟨(List.nil).toArray, by grind⟩ h_m_le h_i_le h_acc0_size h_acc0_chunk
  exact ⟨v, hv, hv_size, hv_chunk⟩

/-! ## Obligations. -/

/-- Failure condition (precondition violation). Captures the property test
    `prop_panics_on_length_mismatch` and the two `#[should_panic]` tests
    `slice_len_too_small_u64_write_big_endian` (15 bytes vs 2 longs) and
    `slice_len_too_big_u64_write_big_endian` (17 bytes vs 2 longs):
    whenever the exact relation `src.len() * 8 == dst.len()` does **not**
    hold, the modeled `hax_lib::assert!` fires and the function fails with
    an assertion failure (the original `assert_eq!` panic). The `hno`
    hypothesis pins the failure mode to the assertion path (the contract
    regime the tests exercise); without it an over-large `src` would
    instead trip the `usize` overflow of `src.len() * 8` computed before
    the comparison. -/
theorem write_u64_into_length_mismatch_fails
    (src : RustSlice u64) (dst : RustSlice u8)
    (hno : src.val.size * 8 < USize64.size)
    (hmis : src.val.size * 8 ≠ dst.val.size) :
    big_endian_write_u64_into.write_u64_into src dst
      = RustM.fail Error.assertionFailure :=
  write_u64_into_fail_aux src dst hno hmis

/-- Totality / no-panic on valid input. Captures the "completes without
    panicking" assertion implicit in `prop_writes_big_endian_bytes`: when
    the precondition `dst.len() == src.len() * 8` holds, the assert passes,
    `build_output`'s decreasing recursion terminates, every
    `extend_from_slice` stays within `usize` (the final buffer length is
    `src.len() * 8 == dst.len()`), and `copy_from_slice`'s equal-length
    requirement holds by construction, so the function returns
    successfully. -/
theorem write_u64_into_valid_succeeds
    (src : RustSlice u64) (dst : RustSlice u8)
    (hpre : dst.val.size = src.val.size * 8) :
    ∃ v : RustSlice u8,
      big_endian_write_u64_into.write_u64_into src dst = RustM.ok v := by
  obtain ⟨v, hv, _, _⟩ := write_u64_into_aux src dst hpre
  exact ⟨v, hv⟩

/-- Length-preservation postcondition. Captures the
    `prop_assert_eq!(dst.len(), src.len() * 8)` clause of
    `prop_writes_big_endian_bytes`: `build_output` emits exactly 8 bytes
    per input word, so the built image has length `src.len() * 8`, and the
    whole-slice `copy_from_slice` preserves `dst`'s length; hence the
    rewritten slice has the same length as the input `dst`. -/
theorem write_u64_into_preserves_length
    (src : RustSlice u64) (dst : RustSlice u8)
    (hpre : dst.val.size = src.val.size * 8)
    (v : RustSlice u8)
    (hres : big_endian_write_u64_into.write_u64_into src dst = RustM.ok v) :
    v.val.size = dst.val.size := by
  obtain ⟨v', hv', hsz, _⟩ := write_u64_into_aux src dst hpre
  rw [hv'] at hres
  injection hres with h_eq
  injection h_eq with h_eq'
  subst h_eq'
  rw [hsz, hpre]

/-- Core functional postcondition (value + endianness). Captures the
    double `for` loop of `prop_writes_big_endian_bytes`: for input word
    index `i` and byte position `j < 8`, output byte `dst[i*8 + j]` is the
    `j`-th big-endian byte of `src[i]`, i.e. `((src[i] >> (8*(7-j))) &
    0xff) as u8`, taken at its own position. The oracle `beByte` weights
    `j = 0` by the top byte, so this falsifies any implementation using the
    wrong endianness, a byte permutation, the wrong word per chunk,
    reversed chunk order, or a shifted write position. -/
theorem write_u64_into_big_endian_bytes
    (src : RustSlice u64) (dst : RustSlice u8)
    (hpre : dst.val.size = src.val.size * 8)
    (v : RustSlice u8)
    (hres : big_endian_write_u64_into.write_u64_into src dst = RustM.ok v)
    (i : Nat) (hi : i < src.val.size)
    (j : Nat) (hj : j < 8)
    (hk : i * 8 + j < v.val.size) :
    (v.val[i * 8 + j]'hk).toNat = beByte (src.val[i]'hi) j := by
  obtain ⟨v', hv', _, hchunk⟩ := write_u64_into_aux src dst hpre
  rw [hv'] at hres
  injection hres with h_eq
  injection h_eq with h_eq'
  subst h_eq'
  exact hchunk i j hk hi hj

/-- Empty-slice edge case. Captures the empty-slice boundary explicitly
    called out by `prop_writes_big_endian_bytes` (its `0..32` length range
    includes the empty `src`, "0 == 8 * 0, must not panic, must write
    nothing"): on empty `src`/`dst` the precondition `0 == src.len() * 8`
    holds, so the call is a valid no-op — the function completes
    successfully and yields an empty slice (`build_output`'s base case
    fires immediately and the whole-slice `copy_from_slice` write-back is a
    no-op). -/
theorem write_u64_into_empty_noop
    (src : RustSlice u64) (dst : RustSlice u8)
    (hsrc : src.val.size = 0) (hdst : dst.val.size = 0) :
    ∃ v : RustSlice u8,
      big_endian_write_u64_into.write_u64_into src dst = RustM.ok v ∧
      v.val.size = 0 := by
  have hpre : dst.val.size = src.val.size * 8 := by rw [hsrc, hdst]
  obtain ⟨v, hv, hsz, _⟩ := write_u64_into_aux src dst hpre
  exact ⟨v, hv, by rw [hsz, hsrc]⟩

end Big_endian_write_u64_intoObligations
