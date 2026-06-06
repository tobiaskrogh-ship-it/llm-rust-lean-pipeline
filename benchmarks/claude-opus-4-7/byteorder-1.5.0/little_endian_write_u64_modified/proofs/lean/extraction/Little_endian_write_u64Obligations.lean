-- Companion obligations file for the `little_endian_write_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import little_endian_write_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6400000

namespace Little_endian_write_u64Obligations

/-! ## Specification oracle: little-endian byte extraction.

`leByte n i` is the `i`-th byte (counting from the *least*-significant end,
`i = 0` is the bottom byte) of the 64-bit value `n`, written little-endian.
Expressed at the `Nat` level — `(n / 2^(8*i)) % 256` — independent of the
implementation's `(n >> k) as u8` shift/narrowing-cast form, so the
postcondition is a genuine semantic specification rather than a restatement
of the code. A big-endian (or otherwise byte-permuted) implementation fails
against this oracle. (`byteorder` doc: `LittleEndian::write_u64` writes an
unsigned 64-bit integer in little-endian order into `buf`; the Rust test
`prop_little_endian_byte_order` pins `buf[i] == (n >> (8*i)) & 0xff`.) -/
private def leByte (n : u64) (i : Nat) : Nat :=
  (n.toNat / 2 ^ (8 * i)) % 256

/-! ## Generic scaffolding (pattern reused from the verified
`big_endian_write_u64` reference — the canonical little-endian-mirror
template flagged by the selection stage). -/

/-- `RustM.ok x >>= f = f x`. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl
private theorem ulit8 : (8 : usize).toNat = 8 := by decide
private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide
private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

/-- Push a single element (1-chunk `extend_from_slice`). -/
private def push_one (acc : alloc.vec.Vec u8 alloc.alloc.Global) (x : u8)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec u8 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

/-! ## Little-endian byte array.

`le` in the extracted code is built from `n as u8` (byte 0, no shift) plus
seven `(n >>> k) as u8` narrowing casts (bytes 1..7).  After reducing the
modeled shift (`>>>?`) and narrowing cast (`cast_op`), the array is exactly
`leArr n`. -/
private def leArr (n : u64) : RustArray u8 8 :=
  RustArray.ofVec #v[
    UInt64.toUInt8 n,
    UInt64.toUInt8 (n >>> (8 : UInt64)),
    UInt64.toUInt8 (n >>> (16 : UInt64)),
    UInt64.toUInt8 (n >>> (24 : UInt64)),
    UInt64.toUInt8 (n >>> (32 : UInt64)),
    UInt64.toUInt8 (n >>> (40 : UInt64)),
    UInt64.toUInt8 (n >>> (48 : UInt64)),
    UInt64.toUInt8 (n >>> (56 : UInt64))]

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

private theorem le0 (n : u64) :
    (UInt64.toUInt8 n).toNat = leByte n 0 := by
  have h := byte_toNat_of_bv n (UInt64.toUInt8 n) 0 (by bv_decide)
  simpa [leByte] using h

private theorem le1 (n : u64) :
    (UInt64.toUInt8 (n >>> (8 : UInt64))).toNat = leByte n 1 := by
  have h := byte_toNat_of_bv n (UInt64.toUInt8 (n >>> (8 : UInt64))) 8 (by bv_decide)
  simpa [leByte] using h

private theorem le2 (n : u64) :
    (UInt64.toUInt8 (n >>> (16 : UInt64))).toNat = leByte n 2 := by
  have h := byte_toNat_of_bv n (UInt64.toUInt8 (n >>> (16 : UInt64))) 16 (by bv_decide)
  simpa [leByte] using h

private theorem le3 (n : u64) :
    (UInt64.toUInt8 (n >>> (24 : UInt64))).toNat = leByte n 3 := by
  have h := byte_toNat_of_bv n (UInt64.toUInt8 (n >>> (24 : UInt64))) 24 (by bv_decide)
  simpa [leByte] using h

private theorem le4 (n : u64) :
    (UInt64.toUInt8 (n >>> (32 : UInt64))).toNat = leByte n 4 := by
  have h := byte_toNat_of_bv n (UInt64.toUInt8 (n >>> (32 : UInt64))) 32 (by bv_decide)
  simpa [leByte] using h

private theorem le5 (n : u64) :
    (UInt64.toUInt8 (n >>> (40 : UInt64))).toNat = leByte n 5 := by
  have h := byte_toNat_of_bv n (UInt64.toUInt8 (n >>> (40 : UInt64))) 40 (by bv_decide)
  simpa [leByte] using h

private theorem le6 (n : u64) :
    (UInt64.toUInt8 (n >>> (48 : UInt64))).toNat = leByte n 6 := by
  have h := byte_toNat_of_bv n (UInt64.toUInt8 (n >>> (48 : UInt64))) 48 (by bv_decide)
  simpa [leByte] using h

private theorem le7 (n : u64) :
    (UInt64.toUInt8 (n >>> (56 : UInt64))).toNat = leByte n 7 := by
  have h := byte_toNat_of_bv n (UInt64.toUInt8 (n >>> (56 : UInt64))) 56 (by bv_decide)
  simpa [leByte] using h

/-- The `i`-th element of `leArr n` decodes to the little-endian oracle. -/
private theorem leArr_toNat (n : u64) (k : Nat) (hk8 : k < ((8 : usize)).toNat) :
    ((leArr n).toVec[k]'hk8).toNat = leByte n k := by
  have hu : ((8 : usize)).toNat = 8 := ulit8
  have hk : k < 8 := by omega
  have hcases :
      k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases hcases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact le0 n
  · exact le1 n
  · exact le2 n
  · exact le3 n
  · exact le4 n
  · exact le5 n
  · exact le6 n
  · exact le7 n

/-! ## Primitive-operator reduction lemmas. -/

/-- Right-shift by a valid constant amount. -/
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

/-! ## `build_output` step lemmas. -/

private theorem build_output_oob
    (buf : RustSlice u8) (le : RustArray u8 8) (i : usize)
    (acc : alloc.vec.Vec u8 alloc.alloc.Global)
    (hi : buf.val.size ≤ i.toNat) :
    little_endian_write_u64.build_output buf le i acc = RustM.ok acc := by
  conv => lhs; unfold little_endian_write_u64.build_output
  have h_ofNat : (USize64.ofNat buf.val.size).toNat = buf.val.size :=
    USize64.toNat_ofNat_of_lt' buf.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat buf.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

private theorem build_output_step_le
    (buf : RustSlice u8) (le : RustArray u8 8) (i : usize)
    (acc : alloc.vec.Vec u8 alloc.alloc.Global)
    (hi : i.toNat < buf.val.size)
    (h8 : i.toNat < ((8 : usize)).toNat)
    (h_acc : acc.val.size + 1 < USize64.size) :
    little_endian_write_u64.build_output buf le i acc =
      little_endian_write_u64.build_output buf le (i + 1)
        (push_one acc (le.toVec[i.toNat]'h8) h_acc) := by
  conv => lhs; unfold little_endian_write_u64.build_output
  have h_size_lt : buf.val.size < USize64.size := buf.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat buf.val.size).toNat = buf.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat buf.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_cond_inner : decide (i < (8 : usize)) = true := by
    rw [decide_eq_true_iff, USize64.lt_iff_toNat_lt]
    exact h8
  have h_idx :
      (le[i]_? : RustM u8) = RustM.ok (le.toVec[i.toNat]'h8) := by
    show (if h : i.toNat < ((8 : usize)).toNat then pure (le.toVec[i.toNat])
            else .fail .arrayOutOfBounds)
        = RustM.ok (le.toVec[i.toNat]'h8)
    rw [dif_pos h8]; rfl
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
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, rust_primitives.cmp.lt, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_cond_inner, h_idx]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[le.toVec[i.toNat]'h8] : RustArray u8 1)
              : RustM (rust_primitives.sequence.Seq u8))
            = RustM.ok ⟨#[le.toVec[i.toNat]'h8], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size :
      acc.val.size + (#[le.toVec[i.toNat]'h8] : Array u8).size < USize64.size := by
    show acc.val.size + 1 < USize64.size
    exact h_acc
  rw [show (alloc.vec.Impl_2.extend_from_slice u8 alloc.alloc.Global acc
              ⟨#[le.toVec[i.toNat]'h8], one_lt_usize_size⟩
            : RustM (alloc.vec.Vec u8 alloc.alloc.Global))
        = RustM.ok (push_one acc (le.toVec[i.toNat]'h8) h_acc) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  simp only [RustM_ok_bind]
  rw [h_add_eq]
  rfl

private theorem build_output_step_buf
    (buf : RustSlice u8) (le : RustArray u8 8) (i : usize)
    (acc : alloc.vec.Vec u8 alloc.alloc.Global)
    (hi : i.toNat < buf.val.size)
    (hge : 8 ≤ i.toNat)
    (h_acc : acc.val.size + 1 < USize64.size) :
    little_endian_write_u64.build_output buf le i acc =
      little_endian_write_u64.build_output buf le (i + 1)
        (push_one acc (buf.val[i.toNat]'hi) h_acc) := by
  conv => lhs; unfold little_endian_write_u64.build_output
  have h_size_lt : buf.val.size < USize64.size := buf.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat buf.val.size).toNat = buf.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat buf.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_cond_inner : decide (i < (8 : usize)) = false := by
    rw [decide_eq_false_iff_not, USize64.lt_iff_toNat_lt]
    have hu : ((8 : usize)).toNat = 8 := ulit8
    omega
  have h_idx :
      (buf[i]_? : RustM u8) = RustM.ok (buf.val[i.toNat]'hi) := by
    show (if h : i.toNat < buf.val.size then pure (buf.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (buf.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
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
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, rust_primitives.cmp.lt, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_cond_inner, h_idx]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[buf.val[i.toNat]'hi] : RustArray u8 1)
              : RustM (rust_primitives.sequence.Seq u8))
            = RustM.ok ⟨#[buf.val[i.toNat]'hi], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size :
      acc.val.size + (#[buf.val[i.toNat]'hi] : Array u8).size < USize64.size := by
    show acc.val.size + 1 < USize64.size
    exact h_acc
  rw [show (alloc.vec.Impl_2.extend_from_slice u8 alloc.alloc.Global acc
              ⟨#[buf.val[i.toNat]'hi], one_lt_usize_size⟩
            : RustM (alloc.vec.Vec u8 alloc.alloc.Global))
        = RustM.ok (push_one acc (buf.val[i.toNat]'hi) h_acc) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  simp only [RustM_ok_bind]
  rw [h_add_eq]
  rfl

/-! ## Strong induction for `build_output`.

Invariant: `acc.val.size = i.toNat`; the first ≤ 8 entries are the
little-endian bytes (`le.toVec`), the rest are copied unchanged from
`buf`. -/

private theorem build_output_correct (buf : RustSlice u8) (le : RustArray u8 8) :
    ∀ (m : Nat) (i : usize) (acc : alloc.vec.Vec u8 alloc.alloc.Global),
      buf.val.size - i.toNat ≤ m →
      i.toNat ≤ buf.val.size →
      acc.val.size = i.toNat →
      (∀ (j : Nat) (hj : j < acc.val.size) (hj8 : j < ((8 : usize)).toNat),
          (acc.val[j]'hj) = le.toVec[j]'hj8) →
      (∀ (j : Nat) (hj : j < acc.val.size) (hjb : j < buf.val.size),
          8 ≤ j → (acc.val[j]'hj) = buf.val[j]'hjb) →
      ∃ v : alloc.vec.Vec u8 alloc.alloc.Global,
        little_endian_write_u64.build_output buf le i acc = RustM.ok v ∧
        v.val.size = buf.val.size ∧
        (∀ (j : Nat) (hj : j < v.val.size) (hj8 : j < ((8 : usize)).toNat),
            (v.val[j]'hj) = le.toVec[j]'hj8) ∧
        (∀ (j : Nat) (hj : j < v.val.size) (hjb : j < buf.val.size),
            8 ≤ j → (v.val[j]'hj) = buf.val[j]'hjb) := by
  intro m
  induction m with
  | zero =>
    intro i acc hm hi_le h_acc_size h_acc_le h_acc_buf
    have hi_eq : i.toNat = buf.val.size := by omega
    have hi_ge : buf.val.size ≤ i.toNat := by omega
    refine ⟨acc, build_output_oob buf le i acc hi_ge, ?_, ?_, ?_⟩
    · rw [h_acc_size, hi_eq]
    · intro j hj hj8; exact h_acc_le j hj hj8
    · intro j hj hjb hge; exact h_acc_buf j hj hjb hge
  | succ m ih =>
    intro i acc hm hi_le h_acc_size h_acc_le h_acc_buf
    by_cases hi_ge : buf.val.size ≤ i.toNat
    · have hi_eq : i.toNat = buf.val.size := by omega
      refine ⟨acc, build_output_oob buf le i acc hi_ge, ?_, ?_, ?_⟩
      · rw [h_acc_size, hi_eq]
      · intro j hj hj8; exact h_acc_le j hj hj8
      · intro j hj hjb hge; exact h_acc_buf j hj hjb hge
    · have hi_lt : i.toNat < buf.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : buf.val.size < USize64.size := buf.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_acc_succ : acc.val.size + 1 < USize64.size := by
        rw [h_acc_size, h_usize_size]; omega
      have h_i1_le : (i + 1).toNat ≤ buf.val.size := by rw [h_i1]; omega
      have h_m_le : buf.val.size - (i + 1).toNat ≤ m := by rw [h_i1]; omega
      have hu : ((8 : usize)).toNat = 8 := ulit8
      by_cases h8 : i.toNat < ((8 : usize)).toNat
      · -- little-endian byte branch
        have h_step := build_output_step_le buf le i acc hi_lt h8 h_acc_succ
        rw [h_step]
        have h_acc'_size :
            (push_one acc (le.toVec[i.toNat]'h8) h_acc_succ).val.size
              = (i + 1).toNat := by
          show (acc.val ++ #[le.toVec[i.toNat]'h8]).size = (i + 1).toNat
          rw [Array.size_append, h_i1, h_acc_size]; rfl
        have h_acc'_le :
            ∀ (j : Nat)
              (hj : j < (push_one acc (le.toVec[i.toNat]'h8) h_acc_succ).val.size)
              (hj8 : j < ((8 : usize)).toNat),
              ((push_one acc (le.toVec[i.toNat]'h8) h_acc_succ).val[j]'hj)
                = le.toVec[j]'hj8 := by
          intro j hj hj8
          show ((acc.val ++ #[le.toVec[i.toNat]'h8])[j]'hj) = _
          by_cases hjlt : j < acc.val.size
          · rw [Array.getElem_append_left hjlt]
            exact h_acc_le j hjlt hj8
          · have h_size_raw :
                (acc.val ++ #[le.toVec[i.toNat]'h8]).size = acc.val.size + 1 := by
              rw [Array.size_append]; rfl
            have hj_eq : j = acc.val.size := by
              have : j < acc.val.size + 1 := by rw [← h_size_raw]; exact hj
              omega
            subst hj_eq
            rw [Array.getElem_append_right (Nat.le_refl _)]
            simp only [Nat.sub_self]
            show (le.toVec[i.toNat]'h8) = le.toVec[acc.val.size]'hj8
            exact getElem_congr_idx h_acc_size.symm
        have h_acc'_buf :
            ∀ (j : Nat)
              (hj : j < (push_one acc (le.toVec[i.toNat]'h8) h_acc_succ).val.size)
              (hjb : j < buf.val.size),
              8 ≤ j →
              ((push_one acc (le.toVec[i.toNat]'h8) h_acc_succ).val[j]'hj)
                = buf.val[j]'hjb := by
          intro j hj hjb hge
          show ((acc.val ++ #[le.toVec[i.toNat]'h8])[j]'hj) = _
          by_cases hjlt : j < acc.val.size
          · rw [Array.getElem_append_left hjlt]
            exact h_acc_buf j hjlt hjb hge
          · have h_size_raw :
                (acc.val ++ #[le.toVec[i.toNat]'h8]).size = acc.val.size + 1 := by
              rw [Array.size_append]; rfl
            have hj_eq : j = acc.val.size := by
              have : j < acc.val.size + 1 := by rw [← h_size_raw]; exact hj
              omega
            exfalso; omega
        exact ih (i + 1) _ h_m_le h_i1_le h_acc'_size h_acc'_le h_acc'_buf
      · -- copied-unchanged branch
        have hge8 : 8 ≤ i.toNat := by omega
        have h_step := build_output_step_buf buf le i acc hi_lt hge8 h_acc_succ
        rw [h_step]
        have h_acc'_size :
            (push_one acc (buf.val[i.toNat]'hi_lt) h_acc_succ).val.size
              = (i + 1).toNat := by
          show (acc.val ++ #[buf.val[i.toNat]'hi_lt]).size = (i + 1).toNat
          rw [Array.size_append, h_i1, h_acc_size]; rfl
        have h_acc'_le :
            ∀ (j : Nat)
              (hj : j < (push_one acc (buf.val[i.toNat]'hi_lt) h_acc_succ).val.size)
              (hj8 : j < ((8 : usize)).toNat),
              ((push_one acc (buf.val[i.toNat]'hi_lt) h_acc_succ).val[j]'hj)
                = le.toVec[j]'hj8 := by
          intro j hj hj8
          show ((acc.val ++ #[buf.val[i.toNat]'hi_lt])[j]'hj) = _
          by_cases hjlt : j < acc.val.size
          · rw [Array.getElem_append_left hjlt]
            exact h_acc_le j hjlt hj8
          · have h_size_raw :
                (acc.val ++ #[buf.val[i.toNat]'hi_lt]).size = acc.val.size + 1 := by
              rw [Array.size_append]; rfl
            have hj_eq : j = acc.val.size := by
              have : j < acc.val.size + 1 := by rw [← h_size_raw]; exact hj
              omega
            exfalso
            rw [hj_eq, h_acc_size] at hj8
            omega
        have h_acc'_buf :
            ∀ (j : Nat)
              (hj : j < (push_one acc (buf.val[i.toNat]'hi_lt) h_acc_succ).val.size)
              (hjb : j < buf.val.size),
              8 ≤ j →
              ((push_one acc (buf.val[i.toNat]'hi_lt) h_acc_succ).val[j]'hj)
                = buf.val[j]'hjb := by
          intro j hj hjb hge
          show ((acc.val ++ #[buf.val[i.toNat]'hi_lt])[j]'hj) = _
          by_cases hjlt : j < acc.val.size
          · rw [Array.getElem_append_left hjlt]
            exact h_acc_buf j hjlt hjb hge
          · have h_size_raw :
                (acc.val ++ #[buf.val[i.toNat]'hi_lt]).size = acc.val.size + 1 := by
              rw [Array.size_append]; rfl
            have hj_eq : j = acc.val.size := by
              have : j < acc.val.size + 1 := by rw [← h_size_raw]; exact hj
              omega
            subst hj_eq
            rw [Array.getElem_append_right (Nat.le_refl _)]
            simp only [Nat.sub_self]
            show (buf.val[i.toNat]'hi_lt) = buf.val[acc.val.size]'hjb
            exact getElem_congr_idx h_acc_size.symm
        exact ih (i + 1) _ h_m_le h_i1_le h_acc'_size h_acc'_le h_acc'_buf

/-! ## `write_u64` reduces to `build_output` from the empty buffer. -/

private theorem write_u64_eq_build (buf : RustSlice u8) (n : u64)
    (h : 8 ≤ buf.val.size) :
    little_endian_write_u64.write_u64 buf n
      = little_endian_write_u64.build_output buf (leArr n) (0 : usize)
          ⟨(List.nil).toArray, by grind⟩ := by
  have h_size_lt : buf.val.size < USize64.size := buf.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat buf.val.size).toNat = buf.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_assert : decide ((8 : usize) ≤ USize64.ofNat buf.val.size) = true := by
    rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat]
    have hu : ((8 : usize)).toNat = 8 := ulit8
    omega
  have hs8  : (0 ≤ (8 : i32) && (8 : i32) < 64) = true := by decide
  have hs16 : (0 ≤ (16 : i32) && (16 : i32) < 64) = true := by decide
  have hs24 : (0 ≤ (24 : i32) && (24 : i32) < 64) = true := by decide
  have hs32 : (0 ≤ (32 : i32) && (32 : i32) < 64) = true := by decide
  have hs40 : (0 ≤ (40 : i32) && (40 : i32) < 64) = true := by decide
  have hs48 : (0 ≤ (48 : i32) && (48 : i32) < 64) = true := by decide
  have hs56 : (0 ≤ (56 : i32) && (56 : i32) < 64) = true := by decide
  have e8  : ((8 : i32).toNatClampNeg).toUInt64 = (8 : UInt64) := by decide
  have e16 : ((16 : i32).toNatClampNeg).toUInt64 = (16 : UInt64) := by decide
  have e24 : ((24 : i32).toNatClampNeg).toUInt64 = (24 : UInt64) := by decide
  have e32 : ((32 : i32).toNatClampNeg).toUInt64 = (32 : UInt64) := by decide
  have e40 : ((40 : i32).toNatClampNeg).toUInt64 = (40 : UInt64) := by decide
  have e48 : ((48 : i32).toNatClampNeg).toUInt64 = (48 : UInt64) := by decide
  have e56 : ((56 : i32).toNatClampNeg).toUInt64 = (56 : UInt64) := by decide
  have h_new : (alloc.vec.Impl.new u8 rust_primitives.hax.Tuple0.mk
                  : RustM (alloc.vec.Vec u8 alloc.alloc.Global))
                = RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  unfold little_endian_write_u64.write_u64
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, RustM_ok_bind, pure_bind,
             h_assert, hax_lib.assert, ↓reduceIte,
             shr_ok _ (8 : i32) hs8, shr_ok _ (16 : i32) hs16,
             shr_ok _ (24 : i32) hs24, shr_ok _ (32 : i32) hs32,
             shr_ok _ (40 : i32) hs40, shr_ok _ (48 : i32) hs48,
             shr_ok _ (56 : i32) hs56,
             e8, e16, e24, e32, e40, e48, e56,
             cast_ok, h_new,
             core_models.ops.deref.Deref.deref,
             core_models.slice.Impl.copy_from_slice, rust_primitives.mem.replace,
             bind_pure, leArr]

private theorem write_u64_aux (buf : RustSlice u8) (n : u64)
    (h : 8 ≤ buf.val.size) :
    ∃ v : alloc.vec.Vec u8 alloc.alloc.Global,
      little_endian_write_u64.write_u64 buf n = RustM.ok v ∧
      v.val.size = buf.val.size ∧
      (∀ (j : Nat) (hj : j < v.val.size) (hj8 : j < ((8 : usize)).toNat),
          (v.val[j]'hj) = (leArr n).toVec[j]'hj8) ∧
      (∀ (j : Nat) (hj : j < v.val.size) (hjb : j < buf.val.size),
          8 ≤ j → (v.val[j]'hj) = buf.val[j]'hjb) := by
  rw [write_u64_eq_build buf n h]
  have h_acc0_size :
      (⟨(List.nil).toArray, by grind⟩
        : alloc.vec.Vec u8 alloc.alloc.Global).val.size = (0 : usize).toNat := by
    show (List.nil : List u8).toArray.size = 0
    rfl
  have h_acc0_le :
      ∀ (j : Nat)
        (hj : j < (⟨(List.nil).toArray, by grind⟩
                    : alloc.vec.Vec u8 alloc.alloc.Global).val.size)
        (hj8 : j < ((8 : usize)).toNat),
        ((⟨(List.nil).toArray, by grind⟩
            : alloc.vec.Vec u8 alloc.alloc.Global).val[j]'hj)
          = (leArr n).toVec[j]'hj8 := by
    intro j hj _; exact absurd hj (by simp)
  have h_acc0_buf :
      ∀ (j : Nat)
        (hj : j < (⟨(List.nil).toArray, by grind⟩
                    : alloc.vec.Vec u8 alloc.alloc.Global).val.size)
        (hjb : j < buf.val.size),
        8 ≤ j →
        ((⟨(List.nil).toArray, by grind⟩
            : alloc.vec.Vec u8 alloc.alloc.Global).val[j]'hj)
          = buf.val[j]'hjb := by
    intro j hj _ _; exact absurd hj (by simp)
  have h_m_le : buf.val.size - (0 : usize).toNat ≤ buf.val.size := by
    show buf.val.size - 0 ≤ buf.val.size; omega
  have h_i_le : (0 : usize).toNat ≤ buf.val.size := by
    show 0 ≤ buf.val.size; omega
  exact build_output_correct buf (leArr n) buf.val.size (0 : usize)
          ⟨(List.nil).toArray, by grind⟩ h_m_le h_i_le h_acc0_size
          h_acc0_le h_acc0_buf

/-! ## Obligations. -/

/-- Failure condition (precondition violation). Captures the
    `#[should_panic]` test `write_little_endian_too_small` (buffer length
    7) and its generalization `prop_panics_when_buffer_too_small` (every
    buffer shorter than 8 bytes, for any `n`): the modeled
    `hax_lib::assert!(buf.len() >= 8)` fires and the function fails with an
    assertion failure (the original `buf[..8]` out-of-bounds panic). -/
theorem write_u64_too_small_fails
    (buf : RustSlice u8) (n : u64)
    (h : buf.val.size < 8) :
    little_endian_write_u64.write_u64 buf n = RustM.fail Error.assertionFailure := by
  have h_size_lt : buf.val.size < USize64.size := buf.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat buf.val.size).toNat = buf.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_assert : decide ((8 : usize) ≤ USize64.ofNat buf.val.size) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]
    have hu : ((8 : usize)).toNat = 8 := ulit8
    omega
  unfold little_endian_write_u64.write_u64
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_assert, hax_lib.assert, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- Totality / no-panic on valid input. Captures the "completes without
    panicking" assertion implicit in `prop_little_endian_byte_order` and
    `prop_only_first_eight_bytes_written`: when the precondition
    `buf.len() >= 8` holds, the assert passes, `build_output`'s decreasing
    recursion terminates, every `extend_from_slice` stays within `usize`
    (final length equals `buf.len()`), and `copy_from_slice`'s equal-length
    requirement holds by construction, so the function returns
    successfully. -/
theorem write_u64_valid_succeeds
    (buf : RustSlice u8) (n : u64)
    (h : 8 ≤ buf.val.size) :
    ∃ v : RustSlice u8,
      little_endian_write_u64.write_u64 buf n = RustM.ok v := by
  obtain ⟨v, hv, _, _, _⟩ := write_u64_aux buf n h
  exact ⟨v, hv⟩

/-- Length-preservation postcondition. Captures the structural invariant
    underlying both `prop_little_endian_byte_order` (writes within the
    buffer) and `prop_only_first_eight_bytes_written` (`buf.len()`
    unchanged): `build_output` emits exactly one byte per index
    `0 ≤ i < buf.len()`, and the whole-slice `copy_from_slice` preserves
    `buf`'s length, so the rewritten slice has the same length as the
    input. -/
theorem write_u64_preserves_length
    (buf : RustSlice u8) (n : u64)
    (h : 8 ≤ buf.val.size)
    (v : RustSlice u8)
    (hres : little_endian_write_u64.write_u64 buf n = RustM.ok v) :
    v.val.size = buf.val.size := by
  obtain ⟨v', hv', hsz, _, _⟩ := write_u64_aux buf n h
  rw [hv'] at hres
  injection hres with h_eq
  injection h_eq with h_eq'
  subst h_eq'
  exact hsz

/-- Core functional postcondition (value + endianness). Captures
    `prop_little_endian_byte_order` (and its derived round-trip consequence
    `doc_example_round_trip`): for any `n` and any buffer of length `>= 8`,
    output byte `i` (for `i < 8`) is the `i`-th little-endian byte of `n`,
    i.e. `(n >> (8*i)) & 0xff`, taken at its own index. The oracle `leByte`
    weights index `0` by the bottom byte, so this falsifies any
    implementation using the wrong endianness, a byte permutation, or a
    shifted write position. -/
theorem write_u64_little_endian_bytes
    (buf : RustSlice u8) (n : u64)
    (h : 8 ≤ buf.val.size)
    (v : RustSlice u8)
    (hres : little_endian_write_u64.write_u64 buf n = RustM.ok v)
    (i : Nat) (hi : i < 8) (hiv : i < v.val.size) :
    (v.val[i]'hiv).toNat = leByte n i := by
  obtain ⟨v', hv', _, hle, _⟩ := write_u64_aux buf n h
  rw [hv'] at hres
  injection hres with h_eq
  injection h_eq with h_eq'
  subst h_eq'
  have hj8 : i < ((8 : usize)).toNat := by
    have hu : ((8 : usize)).toNat = 8 := ulit8
    omega
  rw [hle i hiv hj8]
  exact leArr_toNat n i hj8

/-- Writes-exactly-8-bytes postcondition (tail unchanged). Captures
    `prop_only_first_eight_bytes_written`: every byte at index `>= 8` is
    left exactly as it was in the input buffer, so a write that spills past
    index 8 (or clears the whole buffer) is caught. `build_output` copies
    `buf[i]` unchanged for `i >= 8`, and `copy_from_slice` writes that image
    back. -/
theorem write_u64_tail_unchanged
    (buf : RustSlice u8) (n : u64)
    (h : 8 ≤ buf.val.size)
    (v : RustSlice u8)
    (hres : little_endian_write_u64.write_u64 buf n = RustM.ok v)
    (i : Nat) (hi : 8 ≤ i) (hiv : i < v.val.size) (hib : i < buf.val.size) :
    (v.val[i]'hiv) = buf.val[i]'hib := by
  obtain ⟨v', hv', _, _, hbuf⟩ := write_u64_aux buf n h
  rw [hv'] at hres
  injection hres with h_eq
  injection h_eq with h_eq'
  subst h_eq'
  exact hbuf i hiv hib hi

end Little_endian_write_u64Obligations
