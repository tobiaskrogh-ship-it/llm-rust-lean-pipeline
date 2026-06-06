-- Companion obligations file for the `clever_121_add_elements` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_121_add_elements

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_121_add_elementsObligations

/-! ## Integer-valued specification oracle -/

/-- Conditional prefix sum (see file header). -/
private def cond_sum_int (arr : RustSlice i64) (k : Nat) : Nat → Int
  | 0     => 0
  | j + 1 =>
      cond_sum_int arr k j +
        (if h : j < arr.val.size then
           (if j < k ∧ (arr.val[j]'h).toInt.natAbs ≤ 99
            then (arr.val[j]'h).toInt
            else 0)
         else 0)

/-! ## Helpers -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide
private theorem i64_one_toInt : (1 : i64).toInt = 1 := by decide
private theorem i64_99_toInt : (99 : i64).toInt = 99 := by decide

private theorem i64_toInt_lt (x : i64) : x.toInt < 2 ^ 63 := by
  have h := Int64.toInt_lt x; simpa using h

private theorem i64_toInt_ge (x : i64) : -(2 ^ 63 : Int) ≤ x.toInt := by
  have h := Int64.le_toInt x; simpa using h

private theorem h63_eq : (2 : Int) ^ (64 - 1) = 2 ^ 63 := by decide

/-- `(i +? 1 : RustM i64) = RustM.ok (i + 1)` when `i.toInt + 1 < 2^63`. -/
private theorem i64_add_one_eq (i : i64) (h : i.toInt + 1 < 2^63) :
    (i +? (1 : i64) : RustM i64) = RustM.ok (i + 1) := by
  have h_lo := i64_toInt_ge i
  have h_no_add : ¬ Int64.addOverflow i (1 : i64) := by
    intro hov
    rw [Int64.addOverflow_iff, i64_one_toInt, h63_eq] at hov
    rcases hov with hp | hn
    · omega
    · omega
  have h_bv : BitVec.saddOverflow i.toBitVec (1 : i64).toBitVec = false := by
    cases hb : BitVec.saddOverflow i.toBitVec (1 : i64).toBitVec with
    | false => rfl
    | true => exact absurd hb h_no_add
  show (rust_primitives.ops.arith.Add.add i 1 : RustM i64) = RustM.ok (i + 1)
  show (if BitVec.saddOverflow i.toBitVec (1 : i64).toBitVec then
          (.fail .integerOverflow : RustM i64)
        else pure (i + 1)) = _
  rw [h_bv]; rfl

private theorem i64_add_one_toInt (i : i64) (h : i.toInt + 1 < 2^63) :
    (i + (1 : i64)).toInt = i.toInt + 1 := by
  have h_lo := i64_toInt_ge i
  have h_no_add : ¬ Int64.addOverflow i (1 : i64) := by
    intro hov
    rw [Int64.addOverflow_iff, i64_one_toInt, h63_eq] at hov
    rcases hov with hp | hn
    · omega
    · omega
  rw [Int64.toInt_add_of_not_addOverflow h_no_add, i64_one_toInt]

private theorem i64_toUSize64_toNat (i : i64) (h_lo : 0 ≤ i.toInt) :
    (Int64.toUSize64 i).toNat = i.toInt.toNat := by
  have h_hi := i64_toInt_lt i
  show (USize64.ofInt i.toInt).toNat = i.toInt.toNat
  unfold USize64.ofInt
  have h_mod : i.toInt % (2^64 : Int) = i.toInt := by
    apply Int.emod_eq_of_lt h_lo
    have : (2^63 : Int) < 2^64 := by decide
    omega
  rw [h_mod]
  have h_to_nat_lt : i.toInt.toNat < 2^64 := by
    have h_toNat : (i.toInt.toNat : Int) = i.toInt := Int.toNat_of_nonneg h_lo
    have h_lt : (i.toInt.toNat : Int) < (2^64 : Int) := by
      have h2 : i.toInt < (2^64 : Int) := by
        have : (2^63 : Int) < 2^64 := by decide
        omega
      rw [h_toNat]; exact h2
    exact_mod_cast h_lt
  rw [USize64.toNat_ofNat_of_lt' (by
    have : USize64.size = 2^64 := by decide
    rw [this]; exact h_to_nat_lt)]

/-- Slice index when the natural-number index is in range. -/
private theorem slice_index_eq (arr : RustSlice i64) (i : usize)
    (hi : i.toNat < arr.val.size) :
    (arr[i]_? : RustM i64) = RustM.ok (arr.val[i.toNat]'hi) := by
  show (if h : i.toNat < arr.val.size then pure (arr.val[i])
          else .fail .arrayOutOfBounds)
      = RustM.ok (arr.val[i.toNat]'hi)
  rw [dif_pos hi]; rfl

/-- Index equality under a Nat equality. -/
private theorem arr_val_eq (arr : RustSlice i64) {a b : Nat}
    (h_eq : a = b) (h_b : b < arr.val.size) :
    arr.val[a]'(h_eq ▸ h_b) = arr.val[b]'h_b := by
  subst h_eq
  rfl

/-- Slice index when the i64 cast equals a known Nat index. -/
private theorem slice_index_eq_cast (arr : RustSlice i64) (i : i64)
    (h_lo : 0 ≤ i.toInt) (h_lt : i.toInt.toNat < arr.val.size) :
    (arr[Int64.toUSize64 i]_? : RustM i64) = RustM.ok (arr.val[i.toInt.toNat]'h_lt) := by
  have h_cast_toNat : (Int64.toUSize64 i).toNat = i.toInt.toNat :=
    i64_toUSize64_toNat i h_lo
  have h_idx_at : (Int64.toUSize64 i).toNat < arr.val.size := by
    rw [h_cast_toNat]; exact h_lt
  have h1 := slice_index_eq arr (Int64.toUSize64 i) h_idx_at
  rw [h1]
  have h2 : arr.val[(Int64.toUSize64 i).toNat]'h_idx_at =
             arr.val[i.toInt.toNat]'h_lt :=
    arr_val_eq arr h_cast_toNat h_lt
  rw [h2]

/-- Step of `cond_sum_int`: when `j < arr.val.size`, the outer `dite` reduces. -/
private theorem cond_sum_int_succ
    (arr : RustSlice i64) (k : Nat) (j : Nat) (hj : j < arr.val.size) :
    cond_sum_int arr k (j + 1) =
      cond_sum_int arr k j +
        (if j < k ∧ (arr.val[j]'hj).toInt.natAbs ≤ 99
         then (arr.val[j]'hj).toInt
         else 0) := by
  show cond_sum_int arr k j
        + (if h : j < arr.val.size then
             (if j < k ∧ (arr.val[j]'h).toInt.natAbs ≤ 99
              then (arr.val[j]'h).toInt
              else 0)
           else 0)
       = cond_sum_int arr k j +
         (if j < k ∧ (arr.val[j]'hj).toInt.natAbs ≤ 99
          then (arr.val[j]'hj).toInt
          else 0)
  rw [dif_pos hj]

private theorem cond_sum_int_succ_oob
    (arr : RustSlice i64) (k : Nat) (j : Nat) (hj : arr.val.size ≤ j) :
    cond_sum_int arr k (j + 1) = cond_sum_int arr k j := by
  show cond_sum_int arr k j
        + (if h : j < arr.val.size then
             (if j < k ∧ (arr.val[j]'h).toInt.natAbs ≤ 99
              then (arr.val[j]'h).toInt
              else 0)
           else 0)
       = cond_sum_int arr k j
  rw [dif_neg (Nat.not_lt_of_le hj)]; omega

private theorem cond_sum_int_succ_above_k
    (arr : RustSlice i64) (k : Nat) (j : Nat) (hj : k ≤ j) :
    cond_sum_int arr k (j + 1) = cond_sum_int arr k j := by
  show cond_sum_int arr k j
        + (if h : j < arr.val.size then
             (if j < k ∧ (arr.val[j]'h).toInt.natAbs ≤ 99
              then (arr.val[j]'h).toInt
              else 0)
           else 0)
       = cond_sum_int arr k j
  by_cases hin : j < arr.val.size
  · rw [dif_pos hin]
    have h_not : ¬ (j < k ∧ (arr.val[j]'hin).toInt.natAbs ≤ 99) := by
      intro ⟨h_lt, _⟩; omega
    rw [if_neg h_not]; omega
  · rw [dif_neg hin]; omega

private theorem cond_sum_int_stable
    (arr : RustSlice i64) (k : Nat) (j : Nat)
    (h : arr.val.size ≤ j ∨ k ≤ j) :
    ∀ n, cond_sum_int arr k (j + n) = cond_sum_int arr k j := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases h with h1 | h2
    · have h_succ : arr.val.size ≤ j + n := by omega
      have := cond_sum_int_succ_oob arr k (j + n) h_succ
      show cond_sum_int arr k (j + n + 1) = cond_sum_int arr k j
      rw [this, ih]
    · have h_succ : k ≤ j + n := by omega
      have := cond_sum_int_succ_above_k arr k (j + n) h_succ
      show cond_sum_int arr k (j + n + 1) = cond_sum_int arr k j
      rw [this, ih]

private theorem cond_sum_int_eq_of_ge
    (arr : RustSlice i64) (k : Nat) (j m : Nat)
    (h_cross : arr.val.size ≤ j ∨ k ≤ j)
    (h_ge : j ≤ m) :
    cond_sum_int arr k m = cond_sum_int arr k j := by
  obtain ⟨n, hn⟩ : ∃ n, m = j + n := ⟨m - j, by omega⟩
  rw [hn]; exact cond_sum_int_stable arr k j h_cross n

/-- When `v.toInt.natAbs < 2^63`, v ≠ Int64.minValue. -/
private theorem v_ne_minValue_of_natAbs (v : i64)
    (h : v.toInt.natAbs < 2^63) : v ≠ Int64.minValue := by
  intro h_eq
  have h_min : v.toInt = -(2^63 : Int) := by
    rw [h_eq]; decide
  rw [h_min] at h
  exact absurd h (by decide)

/-! ## Step lemmas for `sum_at`. -/

/-- OOB step: when `i.toInt ≥ k.toInt` or `i.toInt.toNat ≥ arr.val.size`
    (and `0 ≤ i.toInt`), the function returns `pure acc`. -/
private theorem sum_at_oob (arr : RustSlice i64) (k i acc : i64)
    (h_lo : 0 ≤ i.toInt)
    (h_oob : k.toInt ≤ i.toInt ∨ arr.val.size ≤ i.toInt.toNat) :
    clever_121_add_elements.sum_at arr k i acc = RustM.ok acc := by
  conv => lhs; unfold clever_121_add_elements.sum_at
  have h_size_lt : arr.val.size < USize64.size := arr.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat arr.val.size).toNat = arr.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cast_toNat : (Int64.toUSize64 i).toNat = i.toInt.toNat :=
    i64_toUSize64_toNat i h_lo
  have h_cast : (rust_primitives.hax.cast_op i : RustM usize) = pure (Int64.toUSize64 i) := rfl
  have h_cond_bool : (decide (i ≥ k) || decide (Int64.toUSize64 i ≥ USize64.ofNat arr.val.size)) = true := by
    rcases h_oob with h1 | h2
    · have h_ge : i ≥ k := by
        apply Int64.le_iff_toInt_le.mpr; exact h1
      rw [decide_eq_true h_ge]; rfl
    · have h_ge : Int64.toUSize64 i ≥ USize64.ofNat arr.val.size := by
        apply USize64.le_iff_toNat_le.mpr
        rw [h_ofNat, h_cast_toNat]; exact h2
      rw [decide_eq_true h_ge]; exact Bool.or_true _
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, h_cast,
             rust_primitives.hax.logical_op.or,
             h_cond_bool, ↓reduceIte]
  rfl

/-- In-range head: the boolean condition guarding the OOB branch is `false`. -/
private theorem sum_at_in_range_cond_false (arr : RustSlice i64) (k i : i64)
    (h_lo : 0 ≤ i.toInt)
    (h_lt_k : i.toInt < k.toInt)
    (h_lt_arr : i.toInt.toNat < arr.val.size) :
    (decide (i ≥ k) || decide (Int64.toUSize64 i ≥ USize64.ofNat arr.val.size)) = false := by
  have h_size_lt : arr.val.size < USize64.size := arr.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat arr.val.size).toNat = arr.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cast_toNat : (Int64.toUSize64 i).toNat = i.toInt.toNat :=
    i64_toUSize64_toNat i h_lo
  have h_not_ge_k : ¬ (i ≥ k) := by
    intro h
    have := Int64.le_iff_toInt_le.mp h
    omega
  have h_not_ge_arr : ¬ (Int64.toUSize64 i ≥ USize64.ofNat arr.val.size) := by
    intro h
    have := USize64.le_iff_toNat_le.mp h
    rw [h_ofNat, h_cast_toNat] at this
    omega
  rw [decide_eq_false h_not_ge_k, decide_eq_false h_not_ge_arr]
  rfl

/-- The unary negation `-? v` on i64 reduces to `pure (-v)` when v ≠ minValue. -/
private theorem i64_neg_eq (v : i64) (h_not_min : v ≠ Int64.minValue) :
    (-? v : RustM i64) = RustM.ok (-v) := by
  show (rust_primitives.ops.arith.Neg.neg v : RustM i64) = _
  show (if v = Int64.minValue
        then (.fail .integerOverflow : RustM i64)
        else pure (-v)) = _
  rw [if_neg h_not_min]; rfl

/-- `acc +? v = pure (acc + v)` when the i64 addition doesn't overflow. -/
private theorem i64_add_eq (acc v : i64) (h_no : ¬ Int64.addOverflow acc v) :
    (acc +? v : RustM i64) = RustM.ok (acc + v) := by
  have h_no_bv : BitVec.saddOverflow acc.toBitVec v.toBitVec = false := by
    cases hb : BitVec.saddOverflow acc.toBitVec v.toBitVec with
    | false => rfl
    | true => exact absurd hb h_no
  show (rust_primitives.ops.arith.Add.add acc v : RustM i64) = _
  show (if BitVec.saddOverflow acc.toBitVec v.toBitVec
        then (.fail .integerOverflow : RustM i64)
        else pure (acc + v)) = _
  rw [h_no_bv]; rfl

/-! ### Take/skip step lemmas, factored by sign of `v`. -/

/-- Take step, v ≥ 0 branch. -/
private theorem sum_at_take_pos
    (arr : RustSlice i64) (k i acc : i64)
    (h_lo : 0 ≤ i.toInt)
    (h_lt_k : i.toInt < k.toInt)
    (h_lt_arr : i.toInt.toNat < arr.val.size)
    (h_i_succ : i.toInt + 1 < 2^63)
    (h_v_nneg : 0 ≤ (arr.val[i.toInt.toNat]'h_lt_arr).toInt)
    (h_le_99 : (arr.val[i.toInt.toNat]'h_lt_arr).toInt ≤ 99)
    (h_no_add : ¬ Int64.addOverflow acc (arr.val[i.toInt.toNat]'h_lt_arr)) :
    clever_121_add_elements.sum_at arr k i acc =
      clever_121_add_elements.sum_at arr k (i + 1)
        (acc + (arr.val[i.toInt.toNat]'h_lt_arr)) := by
  conv => lhs; unfold clever_121_add_elements.sum_at
  have h_idx := slice_index_eq_cast arr i h_lo h_lt_arr
  have h_cast : (rust_primitives.hax.cast_op i : RustM usize) = pure (Int64.toUSize64 i) := rfl
  have h_cond_false := sum_at_in_range_cond_false arr k i h_lo h_lt_k h_lt_arr
  have h_v_not_lt0 : ¬ (arr.val[i.toInt.toNat]'h_lt_arr) < (0 : i64) := by
    intro h
    have := Int64.lt_iff_toInt_lt.mp h
    rw [i64_zero_toInt] at this; omega
  have h_dec_neg : decide ((arr.val[i.toInt.toNat]'h_lt_arr) < (0 : i64)) = false :=
    decide_eq_false h_v_not_lt0
  have h_v_le_99_i64 : (arr.val[i.toInt.toNat]'h_lt_arr) ≤ (99 : i64) := by
    apply Int64.le_iff_toInt_le.mpr
    rw [i64_99_toInt]; exact h_le_99
  have h_dec_le_99 : decide ((arr.val[i.toInt.toNat]'h_lt_arr) ≤ (99 : i64)) = true :=
    decide_eq_true h_v_le_99_i64
  have h_iplus : (i +? (1 : i64) : RustM i64) = RustM.ok (i + 1) :=
    i64_add_one_eq i h_i_succ
  have h_accv : (acc +? (arr.val[i.toInt.toNat]'h_lt_arr) : RustM i64) =
      RustM.ok (acc + (arr.val[i.toInt.toNat]'h_lt_arr)) :=
    i64_add_eq acc _ h_no_add
  unfold rust_primitives.cmp.ge rust_primitives.cmp.lt rust_primitives.cmp.le
    core_models.slice.Impl.len rust_primitives.slice.slice_length
    rust_primitives.hax.logical_op.or rust_primitives.hax.cast_op
  rw [show (Cast.cast i : RustM usize) = pure (Int64.toUSize64 i) from rfl]
  simp only [pure_bind, RustM_ok_bind, h_idx, h_iplus, h_accv,
             h_dec_neg, h_dec_le_99,
             h_cond_false, Bool.false_eq_true, ↓reduceIte]

/-- Take step, v < 0 branch. -/
private theorem sum_at_take_neg
    (arr : RustSlice i64) (k i acc : i64)
    (h_lo : 0 ≤ i.toInt)
    (h_lt_k : i.toInt < k.toInt)
    (h_lt_arr : i.toInt.toNat < arr.val.size)
    (h_i_succ : i.toInt + 1 < 2^63)
    (h_v_neg : (arr.val[i.toInt.toNat]'h_lt_arr).toInt < 0)
    (h_v_natAbs_le_99 : (arr.val[i.toInt.toNat]'h_lt_arr).toInt.natAbs ≤ 99)
    (h_v_not_min : (arr.val[i.toInt.toNat]'h_lt_arr) ≠ Int64.minValue)
    (h_no_add : ¬ Int64.addOverflow acc (arr.val[i.toInt.toNat]'h_lt_arr)) :
    clever_121_add_elements.sum_at arr k i acc =
      clever_121_add_elements.sum_at arr k (i + 1)
        (acc + (arr.val[i.toInt.toNat]'h_lt_arr)) := by
  conv => lhs; unfold clever_121_add_elements.sum_at
  have h_idx := slice_index_eq_cast arr i h_lo h_lt_arr
  have h_cond_false := sum_at_in_range_cond_false arr k i h_lo h_lt_k h_lt_arr
  have h_v_lt0 : (arr.val[i.toInt.toNat]'h_lt_arr) < (0 : i64) := by
    apply Int64.lt_iff_toInt_lt.mpr
    rw [i64_zero_toInt]; exact h_v_neg
  have h_dec_neg : decide ((arr.val[i.toInt.toNat]'h_lt_arr) < (0 : i64)) = true :=
    decide_eq_true h_v_lt0
  have h_negv_toInt : (-(arr.val[i.toInt.toNat]'h_lt_arr)).toInt =
      -(arr.val[i.toInt.toNat]'h_lt_arr).toInt :=
    Int64.toInt_neg_of_ne_intMin h_v_not_min
  have h_negv_le_99 : (-(arr.val[i.toInt.toNat]'h_lt_arr)).toInt ≤ 99 := by
    rw [h_negv_toInt]
    have h_eq : (arr.val[i.toInt.toNat]'h_lt_arr).toInt =
        -((arr.val[i.toInt.toNat]'h_lt_arr).toInt.natAbs : Int) := by
      have h_le : (arr.val[i.toInt.toNat]'h_lt_arr).toInt ≤ 0 := by omega
      exact Int.eq_neg_natAbs_of_nonpos h_le
    rw [h_eq]
    have : ((arr.val[i.toInt.toNat]'h_lt_arr).toInt.natAbs : Int) ≤ 99 := by
      exact_mod_cast h_v_natAbs_le_99
    omega
  have h_negv_le_99_i64 : (-(arr.val[i.toInt.toNat]'h_lt_arr)) ≤ (99 : i64) := by
    apply Int64.le_iff_toInt_le.mpr
    rw [i64_99_toInt]; exact h_negv_le_99
  have h_dec_le_99 : decide ((-(arr.val[i.toInt.toNat]'h_lt_arr)) ≤ (99 : i64)) = true :=
    decide_eq_true h_negv_le_99_i64
  have h_neg_eq : (-? (arr.val[i.toInt.toNat]'h_lt_arr) : RustM i64) =
      RustM.ok (-(arr.val[i.toInt.toNat]'h_lt_arr)) :=
    i64_neg_eq _ h_v_not_min
  have h_iplus : (i +? (1 : i64) : RustM i64) = RustM.ok (i + 1) :=
    i64_add_one_eq i h_i_succ
  have h_accv : (acc +? (arr.val[i.toInt.toNat]'h_lt_arr) : RustM i64) =
      RustM.ok (acc + (arr.val[i.toInt.toNat]'h_lt_arr)) :=
    i64_add_eq acc _ h_no_add
  unfold rust_primitives.cmp.ge rust_primitives.cmp.lt rust_primitives.cmp.le
    core_models.slice.Impl.len rust_primitives.slice.slice_length
    rust_primitives.hax.logical_op.or rust_primitives.hax.cast_op
  rw [show (Cast.cast i : RustM usize) = pure (Int64.toUSize64 i) from rfl]
  simp only [pure_bind, RustM_ok_bind, h_idx, h_iplus, h_accv,
             h_dec_neg, h_neg_eq, h_dec_le_99,
             h_cond_false, Bool.false_eq_true, ↓reduceIte]

/-- Skip step, v ≥ 0 branch. -/
private theorem sum_at_skip_pos
    (arr : RustSlice i64) (k i acc : i64)
    (h_lo : 0 ≤ i.toInt)
    (h_lt_k : i.toInt < k.toInt)
    (h_lt_arr : i.toInt.toNat < arr.val.size)
    (h_i_succ : i.toInt + 1 < 2^63)
    (h_v_nneg : 0 ≤ (arr.val[i.toInt.toNat]'h_lt_arr).toInt)
    (h_gt_99 : 99 < (arr.val[i.toInt.toNat]'h_lt_arr).toInt) :
    clever_121_add_elements.sum_at arr k i acc =
      clever_121_add_elements.sum_at arr k (i + 1) acc := by
  conv => lhs; unfold clever_121_add_elements.sum_at
  have h_idx := slice_index_eq_cast arr i h_lo h_lt_arr
  have h_cond_false := sum_at_in_range_cond_false arr k i h_lo h_lt_k h_lt_arr
  have h_v_not_lt0 : ¬ (arr.val[i.toInt.toNat]'h_lt_arr) < (0 : i64) := by
    intro h
    have := Int64.lt_iff_toInt_lt.mp h
    rw [i64_zero_toInt] at this; omega
  have h_dec_neg : decide ((arr.val[i.toInt.toNat]'h_lt_arr) < (0 : i64)) = false :=
    decide_eq_false h_v_not_lt0
  have h_v_not_le_99 : ¬ (arr.val[i.toInt.toNat]'h_lt_arr) ≤ (99 : i64) := by
    intro h
    have := Int64.le_iff_toInt_le.mp h
    rw [i64_99_toInt] at this; omega
  have h_dec_le_99 : decide ((arr.val[i.toInt.toNat]'h_lt_arr) ≤ (99 : i64)) = false :=
    decide_eq_false h_v_not_le_99
  have h_iplus : (i +? (1 : i64) : RustM i64) = RustM.ok (i + 1) :=
    i64_add_one_eq i h_i_succ
  unfold rust_primitives.cmp.ge rust_primitives.cmp.lt rust_primitives.cmp.le
    core_models.slice.Impl.len rust_primitives.slice.slice_length
    rust_primitives.hax.logical_op.or rust_primitives.hax.cast_op
  rw [show (Cast.cast i : RustM usize) = pure (Int64.toUSize64 i) from rfl]
  simp only [pure_bind, RustM_ok_bind, h_idx, h_iplus,
             h_dec_neg, h_dec_le_99,
             h_cond_false, Bool.false_eq_true, ↓reduceIte]

/-- Skip step, v < 0 branch. -/
private theorem sum_at_skip_neg
    (arr : RustSlice i64) (k i acc : i64)
    (h_lo : 0 ≤ i.toInt)
    (h_lt_k : i.toInt < k.toInt)
    (h_lt_arr : i.toInt.toNat < arr.val.size)
    (h_i_succ : i.toInt + 1 < 2^63)
    (h_v_neg : (arr.val[i.toInt.toNat]'h_lt_arr).toInt < 0)
    (h_v_natAbs_gt_99 : 99 < (arr.val[i.toInt.toNat]'h_lt_arr).toInt.natAbs)
    (h_v_not_min : (arr.val[i.toInt.toNat]'h_lt_arr) ≠ Int64.minValue) :
    clever_121_add_elements.sum_at arr k i acc =
      clever_121_add_elements.sum_at arr k (i + 1) acc := by
  conv => lhs; unfold clever_121_add_elements.sum_at
  have h_idx := slice_index_eq_cast arr i h_lo h_lt_arr
  have h_cond_false := sum_at_in_range_cond_false arr k i h_lo h_lt_k h_lt_arr
  have h_v_lt0 : (arr.val[i.toInt.toNat]'h_lt_arr) < (0 : i64) := by
    apply Int64.lt_iff_toInt_lt.mpr
    rw [i64_zero_toInt]; exact h_v_neg
  have h_dec_neg : decide ((arr.val[i.toInt.toNat]'h_lt_arr) < (0 : i64)) = true :=
    decide_eq_true h_v_lt0
  have h_negv_toInt : (-(arr.val[i.toInt.toNat]'h_lt_arr)).toInt =
      -(arr.val[i.toInt.toNat]'h_lt_arr).toInt :=
    Int64.toInt_neg_of_ne_intMin h_v_not_min
  have h_negv_gt_99 : (99 : Int) < (-(arr.val[i.toInt.toNat]'h_lt_arr)).toInt := by
    rw [h_negv_toInt]
    have h_eq : (arr.val[i.toInt.toNat]'h_lt_arr).toInt =
        -((arr.val[i.toInt.toNat]'h_lt_arr).toInt.natAbs : Int) := by
      have h_le : (arr.val[i.toInt.toNat]'h_lt_arr).toInt ≤ 0 := by omega
      exact Int.eq_neg_natAbs_of_nonpos h_le
    rw [h_eq]
    have : (99 : Int) < ((arr.val[i.toInt.toNat]'h_lt_arr).toInt.natAbs : Int) := by
      exact_mod_cast h_v_natAbs_gt_99
    omega
  have h_negv_not_le_99 : ¬ (-(arr.val[i.toInt.toNat]'h_lt_arr)) ≤ (99 : i64) := by
    intro h
    have := Int64.le_iff_toInt_le.mp h
    rw [i64_99_toInt] at this; omega
  have h_dec_le_99 :
      decide ((-(arr.val[i.toInt.toNat]'h_lt_arr)) ≤ (99 : i64)) = false :=
    decide_eq_false h_negv_not_le_99
  have h_neg_eq : (-? (arr.val[i.toInt.toNat]'h_lt_arr) : RustM i64) =
      RustM.ok (-(arr.val[i.toInt.toNat]'h_lt_arr)) :=
    i64_neg_eq _ h_v_not_min
  have h_iplus : (i +? (1 : i64) : RustM i64) = RustM.ok (i + 1) :=
    i64_add_one_eq i h_i_succ
  unfold rust_primitives.cmp.ge rust_primitives.cmp.lt rust_primitives.cmp.le
    core_models.slice.Impl.len rust_primitives.slice.slice_length
    rust_primitives.hax.logical_op.or rust_primitives.hax.cast_op
  rw [show (Cast.cast i : RustM usize) = pure (Int64.toUSize64 i) from rfl]
  simp only [pure_bind, RustM_ok_bind, h_idx, h_iplus,
             h_dec_neg, h_neg_eq, h_dec_le_99,
             h_cond_false, Bool.false_eq_true, ↓reduceIte]

/-! ## Strong induction master lemma. -/

private theorem sum_at_correct
    (arr : RustSlice i64) (k : i64)
    (hk_pos : 0 < k.toInt)
    (hno_min : ∀ (j : Nat) (h : j < arr.val.size),
                 j < k.toInt.toNat →
                   (arr.val[j]'h).toInt.natAbs < 2 ^ 63)
    (hfit : ∀ (j : Nat), j ≤ arr.val.size →
              -(2^63 : Int) ≤ cond_sum_int arr k.toInt.toNat j ∧
              cond_sum_int arr k.toInt.toNat j < 2^63) :
    ∀ (m : Nat) (i : i64) (acc : i64),
      0 ≤ i.toInt →
      i.toInt ≤ k.toInt →
      i.toInt.toNat ≤ arr.val.size →
      arr.val.size - i.toInt.toNat ≤ m →
      acc.toInt = cond_sum_int arr k.toInt.toNat i.toInt.toNat →
      ∃ r : i64,
        clever_121_add_elements.sum_at arr k i acc = RustM.ok r ∧
        r.toInt = cond_sum_int arr k.toInt.toNat arr.val.size := by
  intro m
  induction m with
  | zero =>
    intro i acc h_lo h_le_k h_le_arr h_m h_inv
    have h_ge_arr : arr.val.size ≤ i.toInt.toNat := by omega
    have h_oob : k.toInt ≤ i.toInt ∨ arr.val.size ≤ i.toInt.toNat := Or.inr h_ge_arr
    refine ⟨acc, sum_at_oob arr k i acc h_lo h_oob, ?_⟩
    have h_stable : cond_sum_int arr k.toInt.toNat i.toInt.toNat =
                    cond_sum_int arr k.toInt.toNat arr.val.size :=
      cond_sum_int_eq_of_ge arr k.toInt.toNat arr.val.size i.toInt.toNat
        (Or.inl (Nat.le_refl _)) h_ge_arr
    rw [h_inv, h_stable]
  | succ m ih =>
    intro i acc h_lo h_le_k h_le_arr h_m h_inv
    -- Case split on whether we're OOB (either by k or by arr.val.size).
    by_cases h_oob_disjunct : k.toInt ≤ i.toInt ∨ arr.val.size ≤ i.toInt.toNat
    · -- OOB: return acc.
      refine ⟨acc, sum_at_oob arr k i acc h_lo h_oob_disjunct, ?_⟩
      rcases h_oob_disjunct with h_k | h_arr
      · -- k.toInt ≤ i.toInt. Then i.toInt = k.toInt (since i ≤ k).
        have h_eq : i.toInt = k.toInt := by omega
        have h_i_nat_eq : i.toInt.toNat = k.toInt.toNat := by rw [h_eq]
        have h_i_nat_ge_k : k.toInt.toNat ≤ i.toInt.toNat := by omega
        have h_stable : cond_sum_int arr k.toInt.toNat i.toInt.toNat =
                        cond_sum_int arr k.toInt.toNat arr.val.size := by
          by_cases h_size : arr.val.size ≤ i.toInt.toNat
          · exact cond_sum_int_eq_of_ge arr k.toInt.toNat arr.val.size i.toInt.toNat
              (Or.inl (Nat.le_refl _)) h_size
          · have h_lt : i.toInt.toNat ≤ arr.val.size :=
              Nat.le_of_lt (Nat.lt_of_not_le h_size)
            exact (cond_sum_int_eq_of_ge arr k.toInt.toNat i.toInt.toNat arr.val.size
              (Or.inr h_i_nat_ge_k) h_lt).symm
        rw [h_inv, h_stable]
      · have h_stable : cond_sum_int arr k.toInt.toNat i.toInt.toNat =
                        cond_sum_int arr k.toInt.toNat arr.val.size :=
          cond_sum_int_eq_of_ge arr k.toInt.toNat arr.val.size i.toInt.toNat
            (Or.inl (Nat.le_refl _)) h_arr
        rw [h_inv, h_stable]
    · -- In range: i.toInt < k.toInt and i.toInt.toNat < arr.val.size.
      have h_not_le_k : ¬ k.toInt ≤ i.toInt := fun h => h_oob_disjunct (Or.inl h)
      have h_not_le_arr : ¬ arr.val.size ≤ i.toInt.toNat :=
        fun h => h_oob_disjunct (Or.inr h)
      have h_lt_k_int : i.toInt < k.toInt := by omega
      have h_lt_arr : i.toInt.toNat < arr.val.size := by omega
      -- Bound: i.toInt + 1 < 2^63 because i.toInt < k.toInt < 2^63.
      have h_k_lt := i64_toInt_lt k
      have h_i_succ : i.toInt + 1 < 2^63 := by omega
      -- arr[i.toInt.toNat] = v, where v.toInt.natAbs < 2^63 (by hno_min).
      have h_k_nat_eq : (k.toInt.toNat : Int) = k.toInt := Int.toNat_of_nonneg (by omega)
      have h_i_nat_lt_k : i.toInt.toNat < k.toInt.toNat := by
        have h_i_eq : (i.toInt.toNat : Int) = i.toInt := Int.toNat_of_nonneg h_lo
        have : (i.toInt.toNat : Int) < (k.toInt.toNat : Int) := by
          rw [h_i_eq, h_k_nat_eq]; exact h_lt_k_int
        exact_mod_cast this
      have h_v_natAbs := hno_min i.toInt.toNat h_lt_arr h_i_nat_lt_k
      have h_v_not_min : (arr.val[i.toInt.toNat]'h_lt_arr) ≠ Int64.minValue :=
        v_ne_minValue_of_natAbs _ h_v_natAbs
      -- The next i: i + 1, with i.toInt + 1 ≤ k.toInt.
      have h_i1_nat_eq : (i + 1).toInt.toNat = i.toInt.toNat + 1 := by
        rw [i64_add_one_toInt i h_i_succ]
        exact_mod_cast Int.toNat_add_nat (by omega) 1
      have h_i1_lo : 0 ≤ (i + 1).toInt := by
        rw [i64_add_one_toInt i h_i_succ]; omega
      have h_i1_le_k : (i + 1).toInt ≤ k.toInt := by
        rw [i64_add_one_toInt i h_i_succ]; omega
      have h_i1_le_arr : (i + 1).toInt.toNat ≤ arr.val.size := by
        rw [h_i1_nat_eq]; omega
      have h_m_le : arr.val.size - (i + 1).toInt.toNat ≤ m := by
        rw [h_i1_nat_eq]; omega
      -- The cond_sum step
      have h_cs_step := cond_sum_int_succ arr k.toInt.toNat i.toInt.toNat h_lt_arr
      -- Now case-split on take vs skip.
      by_cases h_take : (arr.val[i.toInt.toNat]'h_lt_arr).toInt.natAbs ≤ 99
      · -- Take: |v| ≤ 99.
        have h_cs_succ :
            cond_sum_int arr k.toInt.toNat (i.toInt.toNat + 1) =
              cond_sum_int arr k.toInt.toNat i.toInt.toNat +
                (arr.val[i.toInt.toNat]'h_lt_arr).toInt := by
          rw [h_cs_step]
          rw [if_pos ⟨h_i_nat_lt_k, h_take⟩]
        -- Fit precondition: bound new running sum.
        have h_fit_succ := hfit (i.toInt.toNat + 1) (by omega)
        -- No add overflow.
        have h_no_add : ¬ Int64.addOverflow acc (arr.val[i.toInt.toNat]'h_lt_arr) := by
          intro hov
          rw [Int64.addOverflow_iff] at hov
          rcases hov with hov_pos | hov_neg
          · have h_sum_eq :
                acc.toInt + (arr.val[i.toInt.toNat]'h_lt_arr).toInt =
                  cond_sum_int arr k.toInt.toNat (i.toInt.toNat + 1) := by
              rw [h_cs_succ, h_inv]
            rw [h_sum_eq] at hov_pos
            simp only [h63_eq] at hov_pos
            have := h_fit_succ.2; omega
          · have h_sum_eq :
                acc.toInt + (arr.val[i.toInt.toNat]'h_lt_arr).toInt =
                  cond_sum_int arr k.toInt.toNat (i.toInt.toNat + 1) := by
              rw [h_cs_succ, h_inv]
            rw [h_sum_eq] at hov_neg
            simp only [h63_eq] at hov_neg
            have := h_fit_succ.1; omega
        -- Apply the appropriate step lemma.
        by_cases h_v_sign : 0 ≤ (arr.val[i.toInt.toNat]'h_lt_arr).toInt
        · -- v ≥ 0: take_pos.
          have h_v_le_99 : (arr.val[i.toInt.toNat]'h_lt_arr).toInt ≤ 99 := by
            have h_nat : ((arr.val[i.toInt.toNat]'h_lt_arr).toInt.natAbs : Int) =
                          (arr.val[i.toInt.toNat]'h_lt_arr).toInt :=
              Int.natAbs_of_nonneg h_v_sign
            have : ((arr.val[i.toInt.toNat]'h_lt_arr).toInt.natAbs : Int) ≤ 99 := by
              exact_mod_cast h_take
            omega
          have h_step := sum_at_take_pos arr k i acc h_lo h_lt_k_int h_lt_arr h_i_succ
            h_v_sign h_v_le_99 h_no_add
          have h_new_acc_toInt :
              (acc + (arr.val[i.toInt.toNat]'h_lt_arr)).toInt =
                acc.toInt + (arr.val[i.toInt.toNat]'h_lt_arr).toInt :=
            Int64.toInt_add_of_not_addOverflow h_no_add
          have h_new_inv :
              (acc + (arr.val[i.toInt.toNat]'h_lt_arr)).toInt =
                cond_sum_int arr k.toInt.toNat (i + 1).toInt.toNat := by
            rw [h_new_acc_toInt, h_inv, h_i1_nat_eq, ← h_cs_succ]
          obtain ⟨r, h_rec_eq, h_r_int⟩ :=
            ih (i + 1) (acc + (arr.val[i.toInt.toNat]'h_lt_arr))
              h_i1_lo h_i1_le_k h_i1_le_arr h_m_le h_new_inv
          refine ⟨r, ?_, h_r_int⟩
          rw [h_step]; exact h_rec_eq
        · -- v < 0: take_neg.
          have h_v_neg_lt : (arr.val[i.toInt.toNat]'h_lt_arr).toInt < 0 := by omega
          have h_step := sum_at_take_neg arr k i acc h_lo h_lt_k_int h_lt_arr h_i_succ
            h_v_neg_lt h_take h_v_not_min h_no_add
          have h_new_acc_toInt :
              (acc + (arr.val[i.toInt.toNat]'h_lt_arr)).toInt =
                acc.toInt + (arr.val[i.toInt.toNat]'h_lt_arr).toInt :=
            Int64.toInt_add_of_not_addOverflow h_no_add
          have h_new_inv :
              (acc + (arr.val[i.toInt.toNat]'h_lt_arr)).toInt =
                cond_sum_int arr k.toInt.toNat (i + 1).toInt.toNat := by
            rw [h_new_acc_toInt, h_inv, h_i1_nat_eq, ← h_cs_succ]
          obtain ⟨r, h_rec_eq, h_r_int⟩ :=
            ih (i + 1) (acc + (arr.val[i.toInt.toNat]'h_lt_arr))
              h_i1_lo h_i1_le_k h_i1_le_arr h_m_le h_new_inv
          refine ⟨r, ?_, h_r_int⟩
          rw [h_step]; exact h_rec_eq
      · -- Skip: |v| > 99.
        have h_take_gt : 99 < (arr.val[i.toInt.toNat]'h_lt_arr).toInt.natAbs :=
          Nat.lt_of_not_le h_take
        have h_cs_succ :
            cond_sum_int arr k.toInt.toNat (i.toInt.toNat + 1) =
              cond_sum_int arr k.toInt.toNat i.toInt.toNat := by
          have h_neg : ¬ (i.toInt.toNat < k.toInt.toNat ∧
              (arr.val[i.toInt.toNat]'h_lt_arr).toInt.natAbs ≤ 99) := by
            intro ⟨_, hle⟩; exact Nat.not_lt_of_le hle h_take_gt
          rw [h_cs_step, if_neg h_neg]
          omega
        have h_new_inv :
            acc.toInt = cond_sum_int arr k.toInt.toNat (i + 1).toInt.toNat := by
          rw [h_inv, h_i1_nat_eq, h_cs_succ]
        by_cases h_v_sign : 0 ≤ (arr.val[i.toInt.toNat]'h_lt_arr).toInt
        · -- v ≥ 0 but v > 99.
          have h_v_gt_99 : 99 < (arr.val[i.toInt.toNat]'h_lt_arr).toInt := by
            have h_nat : ((arr.val[i.toInt.toNat]'h_lt_arr).toInt.natAbs : Int) =
                          (arr.val[i.toInt.toNat]'h_lt_arr).toInt :=
              Int.natAbs_of_nonneg h_v_sign
            have : (99 : Int) < ((arr.val[i.toInt.toNat]'h_lt_arr).toInt.natAbs : Int) := by
              exact_mod_cast h_take_gt
            omega
          have h_step := sum_at_skip_pos arr k i acc h_lo h_lt_k_int h_lt_arr h_i_succ
            h_v_sign h_v_gt_99
          obtain ⟨r, h_rec_eq, h_r_int⟩ :=
            ih (i + 1) acc h_i1_lo h_i1_le_k h_i1_le_arr h_m_le h_new_inv
          refine ⟨r, ?_, h_r_int⟩
          rw [h_step]; exact h_rec_eq
        · -- v < 0.
          have h_v_neg_lt : (arr.val[i.toInt.toNat]'h_lt_arr).toInt < 0 := by omega
          have h_step := sum_at_skip_neg arr k i acc h_lo h_lt_k_int h_lt_arr h_i_succ
            h_v_neg_lt h_take_gt h_v_not_min
          obtain ⟨r, h_rec_eq, h_r_int⟩ :=
            ih (i + 1) acc h_i1_lo h_i1_le_k h_i1_le_arr h_m_le h_new_inv
          refine ⟨r, ?_, h_r_int⟩
          rw [h_step]; exact h_rec_eq

/-! ## Top-level theorems. -/

/-- Boundary clause: when `k ≤ 0`, `add_elements arr k` returns `0`. -/
theorem add_elements_nonpositive_k_returns_zero
    (arr : RustSlice i64) (k : i64) (hk : k.toInt ≤ 0) :
    clever_121_add_elements.add_elements arr k = RustM.ok (0 : i64) := by
  unfold clever_121_add_elements.add_elements
  have h_le : k ≤ (0 : i64) := by
    apply Int64.le_iff_toInt_le.mpr
    rw [i64_zero_toInt]; exact hk
  have h_dec : decide (k ≤ (0 : i64)) = true := decide_eq_true h_le
  simp only [show (k <=? (0 : i64) : RustM Bool) =
                 (pure (decide (k ≤ (0 : i64))) : RustM Bool) from rfl,
             h_dec, pure_bind, ↓reduceIte]
  rfl

/-- Main correctness postcondition. -/
theorem add_elements_matches_spec
    (arr : RustSlice i64) (k : i64)
    (hk_pos : 0 < k.toInt)
    (hno_min : ∀ (j : Nat) (h : j < arr.val.size),
                 j < k.toInt.toNat →
                   (arr.val[j]'h).toInt.natAbs < 2 ^ 63)
    (hfit : ∀ (j : Nat), j ≤ arr.val.size →
              -(2^63 : Int) ≤ cond_sum_int arr k.toInt.toNat j ∧
              cond_sum_int arr k.toInt.toNat j < 2^63) :
    ∃ r : i64,
      clever_121_add_elements.add_elements arr k = RustM.ok r ∧
      r.toInt = cond_sum_int arr k.toInt.toNat arr.val.size := by
  unfold clever_121_add_elements.add_elements
  -- k > 0, so the k ≤? 0 branch is false.
  have h_not_le : ¬ k ≤ (0 : i64) := by
    intro h
    have := Int64.le_iff_toInt_le.mp h
    rw [i64_zero_toInt] at this; omega
  have h_dec : decide (k ≤ (0 : i64)) = false := decide_eq_false h_not_le
  simp only [show (k <=? (0 : i64) : RustM Bool) =
                 (pure (decide (k ≤ (0 : i64))) : RustM Bool) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
  -- Apply sum_at_correct at i = 0, acc = 0.
  have h_zero_lo : (0 : Int) ≤ (0 : i64).toInt := by rw [i64_zero_toInt]; omega
  have h_zero_le_k : (0 : i64).toInt ≤ k.toInt := by
    rw [i64_zero_toInt]; omega
  have h_zero_nat : (0 : i64).toInt.toNat ≤ arr.val.size := by
    rw [i64_zero_toInt]; show (0 : Nat) ≤ arr.val.size; omega
  have h_inv : (0 : i64).toInt = cond_sum_int arr k.toInt.toNat (0 : i64).toInt.toNat := by
    rw [i64_zero_toInt]
    show (0 : Int) = cond_sum_int arr k.toInt.toNat 0
    rfl
  have h_m_le : arr.val.size - (0 : i64).toInt.toNat ≤ arr.val.size := by
    rw [i64_zero_toInt]; show arr.val.size - (0 : Nat) ≤ arr.val.size; omega
  exact sum_at_correct arr k hk_pos hno_min hfit arr.val.size (0 : i64) (0 : i64)
    h_zero_lo h_zero_le_k h_zero_nat h_m_le h_inv

end Clever_121_add_elementsObligations
