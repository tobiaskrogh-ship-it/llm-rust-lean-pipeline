-- Companion obligations file for the `little_endian_write_u64_into` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import little_endian_write_u64_into

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 6400000

namespace Little_endian_write_u64_intoObligations

/-! ## Specification oracle: little-endian byte extraction.

`leByte n j` is the `j`-th byte (counting from the least-significant end —
`j = 0` is the low byte) of the 64-bit value `n`, written little-endian.
Expressed at the `Nat` level — `(n / 2^(8*j)) % 256` — independent of the
implementation's `(n >> (8*j)) as u8` shift/narrowing-cast form, so the
postcondition is a genuine semantic specification rather than a restatement
of the code. -/
private def leByte (n : u64) (j : Nat) : Nat :=
  (n.toNat / 2 ^ (8 * j)) % 256

/-! ## Generic scaffolding (pattern reused from `big_endian_read_u64_into`,
`big_endian_write_u64`, `big_endian_from_slice_u64`, `clever_009_rolling_max`). -/

/-- `RustM.ok x >>= f = f x`. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem uzero : (0 : usize).toNat = 0 := by decide
private theorem usize_one_toNat : (1 : usize).toNat = 1 := by decide
private theorem ulit8 : (8 : usize).toNat = 8 := by decide
private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide
private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide
private theorem eight_lt_usize_size : (8 : Nat) < USize64.size := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

/-- `usize` multiplication without overflow. -/
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

/-- The narrowing `u64 → u8` cast. -/
private theorem cast_ok (m : u64) :
    (rust_primitives.hax.cast_op m : RustM u8) = RustM.ok (UInt64.toUInt8 m) := rfl

/-- Right-shift by a valid constant amount. -/
private theorem shr_ok (x : u64) (k : i32) (hk : (0 ≤ k && k < 64) = true) :
    (x >>>? k : RustM u64) = RustM.ok (x >>> (k.toNatClampNeg.toUInt64)) := by
  show (rust_primitives.ops.bit.Shr.shr x k : RustM u64) = _
  show (if (0 ≤ k && k < 64)
        then pure (x >>> (k.toNatClampNeg.toUInt64))
        else (.fail .integerOverflow : RustM u64)) = _
  rw [hk]; rfl

/-! ## Per-byte little-endian decode lemmas. -/

/-- The narrowing cast of a right-shift, at the `Nat` level: a single byte
    extraction. Bridged from the `BitVec` form discharged by `bv_decide`. -/
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

/-! ## Push an 8-byte little-endian chunk (8-element `extend_from_slice`). -/

private def push_eight (acc : alloc.vec.Vec u8 alloc.alloc.Global)
    (b0 b1 b2 b3 b4 b5 b6 b7 : u8)
    (h : acc.val.size + 8 < USize64.size) :
    alloc.vec.Vec u8 alloc.alloc.Global :=
  ⟨acc.val ++ #[b0, b1, b2, b3, b4, b5, b6, b7], by
    have h_size : (acc.val ++ #[b0, b1, b2, b3, b4, b5, b6, b7]).size
        = acc.val.size + 8 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

private theorem push_eight_size (acc : alloc.vec.Vec u8 alloc.alloc.Global)
    (b0 b1 b2 b3 b4 b5 b6 b7 : u8)
    (h : acc.val.size + 8 < USize64.size) :
    (push_eight acc b0 b1 b2 b3 b4 b5 b6 b7 h).val.size = acc.val.size + 8 := by
  show (acc.val ++ #[b0, b1, b2, b3, b4, b5, b6, b7]).size = acc.val.size + 8
  rw [Array.size_append]; rfl

/-! ## `build_output` step lemmas. -/

private theorem build_output_oob
    (src : RustSlice u64) (i : usize)
    (acc : alloc.vec.Vec u8 alloc.alloc.Global)
    (hi : src.val.size ≤ i.toNat) :
    little_endian_write_u64_into.build_output src i acc = RustM.ok acc := by
  conv => lhs; unfold little_endian_write_u64_into.build_output
  have h_ofNat : (USize64.ofNat src.val.size).toNat = src.val.size :=
    USize64.toNat_ofNat_of_lt' src.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat src.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

private theorem build_output_step
    (src : RustSlice u64) (i : usize)
    (acc : alloc.vec.Vec u8 alloc.alloc.Global)
    (hi : i.toNat < src.val.size)
    (h_acc : acc.val.size + 8 < USize64.size) :
    little_endian_write_u64_into.build_output src i acc =
      little_endian_write_u64_into.build_output src (i + 1)
        (push_eight acc
          (UInt64.toUInt8 (src.val[i.toNat]'hi))
          (UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (8 : UInt64)))
          (UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (16 : UInt64)))
          (UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (24 : UInt64)))
          (UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (32 : UInt64)))
          (UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (40 : UInt64)))
          (UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (48 : UInt64)))
          (UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (56 : UInt64)))
          h_acc) := by
  conv => lhs; unfold little_endian_write_u64_into.build_output
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
      (src[i]_? : RustM u64) = RustM.ok (src.val[i.toNat]'hi) := by
    show (if h : i.toNat < src.val.size then pure (src.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (src.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
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
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte, h_idx,
             shr_ok _ (8 : i32) hs8, shr_ok _ (16 : i32) hs16,
             shr_ok _ (24 : i32) hs24, shr_ok _ (32 : i32) hs32,
             shr_ok _ (40 : i32) hs40, shr_ok _ (48 : i32) hs48,
             shr_ok _ (56 : i32) hs56,
             e8, e16, e24, e32, e40, e48, e56, cast_ok]
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[
                UInt64.toUInt8 (src.val[i.toNat]'hi),
                UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (8 : UInt64)),
                UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (16 : UInt64)),
                UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (24 : UInt64)),
                UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (32 : UInt64)),
                UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (40 : UInt64)),
                UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (48 : UInt64)),
                UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (56 : UInt64))]
                : RustArray u8 8)
              : RustM (rust_primitives.sequence.Seq u8))
            = RustM.ok ⟨#[
                UInt64.toUInt8 (src.val[i.toNat]'hi),
                UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (8 : UInt64)),
                UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (16 : UInt64)),
                UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (24 : UInt64)),
                UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (32 : UInt64)),
                UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (40 : UInt64)),
                UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (48 : UInt64)),
                UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (56 : UInt64))],
                eight_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size :
      acc.val.size + (#[
        UInt64.toUInt8 (src.val[i.toNat]'hi),
        UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (8 : UInt64)),
        UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (16 : UInt64)),
        UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (24 : UInt64)),
        UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (32 : UInt64)),
        UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (40 : UInt64)),
        UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (48 : UInt64)),
        UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (56 : UInt64))]
        : Array u8).size < USize64.size := by
    show acc.val.size + 8 < USize64.size
    exact h_acc
  rw [show (alloc.vec.Impl_2.extend_from_slice u8 alloc.alloc.Global acc
              ⟨#[
                UInt64.toUInt8 (src.val[i.toNat]'hi),
                UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (8 : UInt64)),
                UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (16 : UInt64)),
                UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (24 : UInt64)),
                UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (32 : UInt64)),
                UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (40 : UInt64)),
                UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (48 : UInt64)),
                UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (56 : UInt64))],
                eight_lt_usize_size⟩
            : RustM (alloc.vec.Vec u8 alloc.alloc.Global))
        = RustM.ok (push_eight acc
            (UInt64.toUInt8 (src.val[i.toNat]'hi))
            (UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (8 : UInt64)))
            (UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (16 : UInt64)))
            (UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (24 : UInt64)))
            (UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (32 : UInt64)))
            (UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (40 : UInt64)))
            (UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (48 : UInt64)))
            (UInt64.toUInt8 ((src.val[i.toNat]'hi) >>> (56 : UInt64)))
            h_acc) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  simp only [RustM_ok_bind]
  rw [h_add_eq]
  rfl

/-! ## Strong induction for `build_output`.

Invariant: `acc.val.size = 8 * i.toNat`, and at flat output index `m`,
`acc[m]` is the `(m % 8)`-th little-endian byte of `src[m / 8]`. The
precondition `8 * src.val.size < USize64.size` keeps every chunk append
within `usize`. -/

private theorem build_output_correct (src : RustSlice u64)
    (hbound : 8 * src.val.size < USize64.size) :
    ∀ (k : Nat) (i : usize) (acc : alloc.vec.Vec u8 alloc.alloc.Global),
      src.val.size - i.toNat ≤ k →
      i.toNat ≤ src.val.size →
      acc.val.size = 8 * i.toNat →
      (∀ (m : Nat) (hm : m < acc.val.size) (hms : m / 8 < src.val.size),
          (acc.val[m]'hm).toNat = leByte (src.val[m / 8]'hms) (m % 8)) →
      ∃ v : alloc.vec.Vec u8 alloc.alloc.Global,
        little_endian_write_u64_into.build_output src i acc = RustM.ok v ∧
        v.val.size = 8 * src.val.size ∧
        (∀ (m : Nat) (hm : m < v.val.size) (hms : m / 8 < src.val.size),
            (v.val[m]'hm).toNat = leByte (src.val[m / 8]'hms) (m % 8)) := by
  intro k
  induction k with
  | zero =>
    intro i acc hk hi_le h_acc_size h_acc_inv
    have hi_eq : i.toNat = src.val.size := by omega
    have hi_ge : src.val.size ≤ i.toNat := by omega
    refine ⟨acc, build_output_oob src i acc hi_ge, ?_, ?_⟩
    · rw [h_acc_size, hi_eq]
    · intro m hm hms; exact h_acc_inv m hm hms
  | succ k ih =>
    intro i acc hk hi_le h_acc_size h_acc_inv
    by_cases hi_ge : src.val.size ≤ i.toNat
    · have hi_eq : i.toNat = src.val.size := by omega
      refine ⟨acc, build_output_oob src i acc hi_ge, ?_, ?_⟩
      · rw [h_acc_size, hi_eq]
      · intro m hm hms; exact h_acc_inv m hm hms
    · have hi_lt : i.toNat < src.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : src.val.size < USize64.size := src.size_lt_usizeSize
      have h_size_ltN : src.val.size < 2 ^ 64 := by
        rw [usize_size_eq] at h_size_lt; exact h_size_lt
      have h_no_ov_i : i.toNat + 1 < 2 ^ 64 := by omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_acc_succ : acc.val.size + 8 < USize64.size := by
        rw [h_acc_size]
        have h1 : 8 * i.toNat + 8 ≤ 8 * src.val.size := by omega
        omega
      have h_step := build_output_step src i acc hi_lt h_acc_succ
      rw [h_step]
      have h_acc'_size :
          (push_eight acc
            (UInt64.toUInt8 (src.val[i.toNat]'hi_lt))
            (UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (8 : UInt64)))
            (UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (16 : UInt64)))
            (UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (24 : UInt64)))
            (UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (32 : UInt64)))
            (UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (40 : UInt64)))
            (UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (48 : UInt64)))
            (UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (56 : UInt64)))
            h_acc_succ).val.size = 8 * (i + 1).toNat := by
        rw [push_eight_size, h_acc_size, h_i1]; omega
      have h_acc'_inv :
          ∀ (m : Nat)
            (hm : m < (push_eight acc
              (UInt64.toUInt8 (src.val[i.toNat]'hi_lt))
              (UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (8 : UInt64)))
              (UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (16 : UInt64)))
              (UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (24 : UInt64)))
              (UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (32 : UInt64)))
              (UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (40 : UInt64)))
              (UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (48 : UInt64)))
              (UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (56 : UInt64)))
              h_acc_succ).val.size)
            (hms : m / 8 < src.val.size),
            ((push_eight acc
              (UInt64.toUInt8 (src.val[i.toNat]'hi_lt))
              (UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (8 : UInt64)))
              (UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (16 : UInt64)))
              (UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (24 : UInt64)))
              (UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (32 : UInt64)))
              (UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (40 : UInt64)))
              (UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (48 : UInt64)))
              (UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (56 : UInt64)))
              h_acc_succ).val[m]'hm).toNat
              = leByte (src.val[m / 8]'hms) (m % 8) := by
        intro m hm hms
        show ((acc.val ++ #[
            UInt64.toUInt8 (src.val[i.toNat]'hi_lt),
            UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (8 : UInt64)),
            UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (16 : UInt64)),
            UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (24 : UInt64)),
            UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (32 : UInt64)),
            UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (40 : UInt64)),
            UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (48 : UInt64)),
            UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (56 : UInt64))])[m]'hm).toNat = _
        by_cases hmlt : m < acc.val.size
        · rw [Array.getElem_append_left hmlt]
          exact h_acc_inv m hmlt hms
        · have hge : acc.val.size ≤ m := Nat.le_of_not_lt hmlt
          have h_size_raw : (acc.val ++ #[
              UInt64.toUInt8 (src.val[i.toNat]'hi_lt),
              UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (8 : UInt64)),
              UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (16 : UInt64)),
              UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (24 : UInt64)),
              UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (32 : UInt64)),
              UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (40 : UInt64)),
              UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (48 : UInt64)),
              UInt64.toUInt8 ((src.val[i.toNat]'hi_lt) >>> (56 : UInt64))]).size
              = acc.val.size + 8 := by
            rw [Array.size_append]; rfl
          have hm8 : m < acc.val.size + 8 := by rw [← h_size_raw]; exact hm
          have hmdiv : m / 8 = i.toNat := by omega
          have hmmod : m % 8 = m - acc.val.size := by omega
          have h_src_eq : src.val[m / 8]'hms = src.val[i.toNat]'hi_lt :=
            getElem_congr_idx hmdiv
          rw [h_src_eq, hmmod, Array.getElem_append_right hge]
          have hr8 : m - acc.val.size < 8 := by omega
          have hcases : m - acc.val.size = 0 ∨ m - acc.val.size = 1 ∨
              m - acc.val.size = 2 ∨ m - acc.val.size = 3 ∨ m - acc.val.size = 4 ∨
              m - acc.val.size = 5 ∨ m - acc.val.size = 6 ∨ m - acc.val.size = 7 := by
            omega
          rcases hcases with h|h|h|h|h|h|h|h
          · simp only [h]; simpa [leByte] using le0 (src.val[i.toNat]'hi_lt)
          · simp only [h]; simpa [leByte] using le1 (src.val[i.toNat]'hi_lt)
          · simp only [h]; simpa [leByte] using le2 (src.val[i.toNat]'hi_lt)
          · simp only [h]; simpa [leByte] using le3 (src.val[i.toNat]'hi_lt)
          · simp only [h]; simpa [leByte] using le4 (src.val[i.toNat]'hi_lt)
          · simp only [h]; simpa [leByte] using le5 (src.val[i.toNat]'hi_lt)
          · simp only [h]; simpa [leByte] using le6 (src.val[i.toNat]'hi_lt)
          · simp only [h]; simpa [leByte] using le7 (src.val[i.toNat]'hi_lt)
      have h_i1_le : (i + 1).toNat ≤ src.val.size := by rw [h_i1]; omega
      have h_k_le : src.val.size - (i + 1).toNat ≤ k := by rw [h_i1]; omega
      exact ih (i + 1) _ h_k_le h_i1_le h_acc'_size h_acc'_inv

/-! ## Top-level reduction. -/

private theorem write_u64_into_eq_build (src : RustSlice u64) (dst : RustSlice u8)
    (hpre : src.val.size * 8 = dst.val.size) :
    little_endian_write_u64_into.write_u64_into src dst
      = little_endian_write_u64_into.build_output src (0 : usize)
          ⟨(List.nil).toArray, by grind⟩ := by
  have hsz : src.val.size < USize64.size := src.size_lt_usizeSize
  have hszN : src.val.size < 2 ^ 64 := by rw [← usize_size_eq]; exact hsz
  have hdsz : dst.val.size < USize64.size := dst.size_lt_usizeSize
  have hdszN : dst.val.size < 2 ^ 64 := by rw [← usize_size_eq]; exact hdsz
  have hmulN : src.val.size * 8 < 2 ^ 64 := by rw [hpre]; exact hdszN
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
    rw [USize64.toNat_ofNat_of_lt' hsz, ulit8]; exact hmulN
  have h_eq_bool :
      ((USize64.ofNat src.val.size * 8) == (USize64.ofNat dst.val.size)) = true := by
    rw [beq_iff_eq]
    apply USize64.toNat_inj.mp
    rw [USize64.toNat_mul_of_lt (by rw [USize64.toNat_ofNat_of_lt' hsz, ulit8]; exact hmulN),
        USize64.toNat_ofNat_of_lt' hsz, ulit8, USize64.toNat_ofNat_of_lt' hdsz]
    exact hpre
  have h_new :
      (alloc.vec.Impl.new u8 rust_primitives.hax.Tuple0.mk
        : RustM (alloc.vec.Vec u8 alloc.alloc.Global))
        = RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  unfold little_endian_write_u64_into.write_u64_into
  simp only [h_len_src, h_len_dst, RustM_ok_bind, h_mul,
             rust_primitives.cmp.eq, h_eq_bool, hax_lib.assert, ↓reduceIte,
             pure_bind, h_new, core_models.ops.deref.Deref.deref,
             core_models.slice.Impl.copy_from_slice, rust_primitives.mem.replace,
             bind_pure]

private theorem write_u64_into_aux (src : RustSlice u64) (dst : RustSlice u8)
    (hpre : src.val.size * 8 = dst.val.size) :
    ∃ v : RustSlice u8,
      little_endian_write_u64_into.write_u64_into src dst = RustM.ok v ∧
      v.val.size = dst.val.size ∧
      (∀ (m : Nat) (hm : m < v.val.size) (hms : m / 8 < src.val.size),
          (v.val[m]'hm).toNat = leByte (src.val[m / 8]'hms) (m % 8)) := by
  have hdsz : dst.val.size < USize64.size := dst.size_lt_usizeSize
  have hbound : 8 * src.val.size < USize64.size := by
    have h8 : 8 * src.val.size = src.val.size * 8 := by omega
    rw [h8, hpre]; exact hdsz
  rw [write_u64_into_eq_build src dst hpre]
  obtain ⟨v, hv, hv_size, hv_inv⟩ :=
    build_output_correct src hbound src.val.size (0 : usize)
      ⟨(List.nil).toArray, by grind⟩
      (by rw [uzero]; omega)
      (by rw [uzero]; omega)
      (by rw [uzero]; rfl)
      (by intro m hm hms; exact absurd hm (by simp))
  refine ⟨v, hv, ?_, ?_⟩
  · rw [hv_size]; omega
  · intro m hm hms; exact hv_inv m hm hms

private theorem write_u64_into_fail_aux (src : RustSlice u64) (dst : RustSlice u8)
    (hno : src.val.size * 8 < USize64.size)
    (hmis : src.val.size * 8 ≠ dst.val.size) :
    little_endian_write_u64_into.write_u64_into src dst
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
    have hh := congrArg USize64.toNat hC
    rw [USize64.toNat_mul_of_lt (by rw [USize64.toNat_ofNat_of_lt' hsz, ulit8]; exact hnoN),
        USize64.toNat_ofNat_of_lt' hsz, ulit8, USize64.toNat_ofNat_of_lt' hdsz] at hh
    exact hh
  unfold little_endian_write_u64_into.write_u64_into
  simp only [h_len_src, h_len_dst, RustM_ok_bind, h_mul,
             rust_primitives.cmp.eq, h_eq_bool, hax_lib.assert,
             Bool.false_eq_true, ↓reduceIte, pure_bind]
  rfl

/-! ## Obligations. -/

/-- Failure condition (precondition violation). Captures
    `panics_exactly_when_length_relation_violated` on the mismatch side:
    whenever `src.len() * 8 ≠ dst.len()`, the modeled
    `hax_lib::assert!(src.len() * 8 == dst.len())` fires and the function
    fails with an assertion failure (the original `assert_eq!` panic).
    The `hno` hypothesis pins the failure mode to the assertion path (the
    regime the test exercises, with small `src.len()`); without it an
    over-long `src` would instead trip the `usize` overflow of
    `src.len() * 8`, which is evaluated before the comparison. -/
theorem write_u64_into_length_mismatch_fails
    (src : RustSlice u64) (dst : RustSlice u8)
    (hno : src.val.size * 8 < USize64.size)
    (hmis : src.val.size * 8 ≠ dst.val.size) :
    little_endian_write_u64_into.write_u64_into src dst
      = RustM.fail Error.assertionFailure :=
  write_u64_into_fail_aux src dst hno hmis

/-- Totality / no-panic on valid input. Captures
    `panics_exactly_when_length_relation_violated` on the match side and
    the "completes without panicking" assertion implicit in
    `postcondition_little_endian_layout_covers_all_bytes`: when the
    precondition `src.len() * 8 == dst.len()` holds, the assert passes,
    `build_output`'s decreasing recursion terminates, every
    `extend_from_slice` stays within `usize` (final length equals
    `dst.len()`), and `copy_from_slice`'s equal-length requirement holds
    by construction, so the function returns successfully. -/
theorem write_u64_into_valid_succeeds
    (src : RustSlice u64) (dst : RustSlice u8)
    (hpre : src.val.size * 8 = dst.val.size) :
    ∃ v : RustSlice u8,
      little_endian_write_u64_into.write_u64_into src dst = RustM.ok v := by
  obtain ⟨v, hv, _, _⟩ := write_u64_into_aux src dst hpre
  exact ⟨v, hv⟩

/-- Length-preservation postcondition. Captures the
    `assert_eq!(dst.len(), src.len() * 8)` check of
    `postcondition_little_endian_layout_covers_all_bytes`: `build_output`
    emits exactly 8 bytes per source element, and the whole-slice
    `copy_from_slice` preserves `dst`'s length, so the rewritten slice
    has the same length as the input `dst`. -/
theorem write_u64_into_preserves_length
    (src : RustSlice u64) (dst : RustSlice u8)
    (hpre : src.val.size * 8 = dst.val.size)
    (v : RustSlice u8)
    (hres : little_endian_write_u64_into.write_u64_into src dst = RustM.ok v) :
    v.val.size = dst.val.size := by
  obtain ⟨v', hv', hsz, _⟩ := write_u64_into_aux src dst hpre
  rw [hv'] at hres
  injection hres with h_eq
  injection h_eq with h_eq'
  subst h_eq'
  exact hsz

/-- Core functional postcondition (value + endianness). Captures
    `postcondition_little_endian_layout_covers_all_bytes`: for every
    source element `i` and byte offset `j < 8`, output byte
    `dst[8*i + j]` is the `j`-th **little-endian** byte of `src[i]`,
    i.e. `(src[i] >> (8*j)) as u8`, taken at its own index. The oracle
    `leByte` weights offset `0` by the least-significant byte, so this
    falsifies any implementation using the wrong endianness, a byte
    permutation, a shifted write position, or a wrong element mapping.
    The index set `{ 8*i + j : i < src.len(), j < 8 }` is exactly
    `0 .. dst.len()`, so together with length preservation this also
    pins that every byte of `dst` is overwritten. -/
theorem write_u64_into_little_endian_layout
    (src : RustSlice u64) (dst : RustSlice u8)
    (hpre : src.val.size * 8 = dst.val.size)
    (v : RustSlice u8)
    (hres : little_endian_write_u64_into.write_u64_into src dst = RustM.ok v)
    (i j : Nat) (hi : i < src.val.size) (hj : j < 8)
    (hidx : i * 8 + j < v.val.size) :
    (v.val[i * 8 + j]'hidx).toNat = leByte (src.val[i]'hi) j := by
  obtain ⟨v', hv', _, hinv⟩ := write_u64_into_aux src dst hpre
  rw [hv'] at hres
  injection hres with h_eq
  injection h_eq with h_eq'
  subst h_eq'
  have hdiv : (i * 8 + j) / 8 = i := by omega
  have hmod : (i * 8 + j) % 8 = j := by omega
  have hms : (i * 8 + j) / 8 < src.val.size := by rw [hdiv]; exact hi
  have hkey := hinv (i * 8 + j) hidx hms
  rw [hmod] at hkey
  rw [show src.val[(i * 8 + j) / 8]'hms = src.val[i]'hi from getElem_congr_idx hdiv] at hkey
  exact hkey

/-- Empty-slice edge case. Captures the `len == 0` iteration of
    `postcondition_little_endian_layout_covers_all_bytes` (and the
    `(0, 0)` pair of `panics_exactly_when_length_relation_violated`): on
    empty `src`/`dst` the precondition `0 * 8 == 0` holds, so the call is
    a valid no-op — the function completes successfully and yields an
    empty slice (`build_output`'s base case fires immediately and the
    whole-slice `copy_from_slice` write-back is a no-op). -/
theorem write_u64_into_empty_noop
    (src : RustSlice u64) (dst : RustSlice u8)
    (hsrc : src.val.size = 0) (hdst : dst.val.size = 0) :
    ∃ v : RustSlice u8,
      little_endian_write_u64_into.write_u64_into src dst = RustM.ok v ∧
      v.val.size = 0 := by
  have hpre : src.val.size * 8 = dst.val.size := by rw [hsrc, hdst]
  obtain ⟨v, hv, hszv, _⟩ := write_u64_into_aux src dst hpre
  exact ⟨v, hv, by rw [hszv, hdst]⟩

end Little_endian_write_u64_intoObligations
