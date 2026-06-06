-- Companion obligations file for the `clever_072_smallest_change` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_072_smallest_change

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_072_smallest_changeObligations

/-! ## Specifications

`num_mismatches arr i` counts mirror-pair mismatches `(arr[k], arr[n-1-k])`
for indices `k ∈ [i, n/2)`, expressed at the `Nat` level. Since the slice
size `n < 2^64` and the count is bounded by `n/2 < 2^63`, the result always
fits in `i64`, so the Lean statement can be universal without preconditions.

`is_palindrome arr` says every mirror pair `(arr[i], arr[n-1-i])` is equal. -/

/-- `mismatchAt arr i = 1` if the mirror pair at index `i` mismatches; else `0`.
    Returns `0` when the indices are out of bounds. -/
private def mismatchAt (arr : RustSlice i64) (i : Nat) : Nat :=
  if h : i < arr.val.size ∧ arr.val.size - 1 - i < arr.val.size then
    (if arr.val[i]'h.1 ≠ arr.val[arr.val.size - 1 - i]'h.2 then 1 else 0)
  else 0

private def num_mismatches (arr : RustSlice i64) (i : Nat) : Nat :=
  if h : i < arr.val.size / 2 then
    mismatchAt arr i + num_mismatches arr (i + 1)
  else 0
termination_by arr.val.size / 2 - i

private def is_palindrome (arr : RustSlice i64) : Prop :=
  ∀ i : Nat, i < arr.val.size / 2 →
    ∀ (hi : i < arr.val.size) (hmirror : arr.val.size - 1 - i < arr.val.size),
      arr.val[i]'hi = arr.val[arr.val.size - 1 - i]'hmirror

/-! ## Generic numeric helpers -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_zero_toNat : (0 : usize).toNat = 0 := rfl
private theorem usize_one_toNat  : (1 : usize).toNat = 1 := rfl
private theorem usize_two_toNat  : (2 : usize).toNat = 2 := rfl

private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide
private theorem i64_one_toInt  : (1 : i64).toInt = 1 := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

private theorem usize_sub_toNat (a b : usize) (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat :=
  USize64.toNat_sub_of_le' h

private theorem div_two_toNat (n : usize) :
    (n / 2).toNat = n.toNat / 2 := by
  show (n.toBitVec / (2 : usize).toBitVec).toNat = _
  rw [BitVec.toNat_udiv]
  rfl

/-- Indexing congruence: two indices with equal Nat values give equal elements. -/
private theorem getElem_idx_congr (arr : RustSlice i64) (a b : Nat)
    (ha : a < arr.val.size) (hb : b < arr.val.size) (h : a = b) :
    arr.val[a]'ha = arr.val[b]'hb := by
  subst h; rfl

/-! ## Equational lemmas for `num_mismatches` and `mismatchAt`. -/

private theorem num_mismatches_step (arr : RustSlice i64) (i : Nat)
    (h : i < arr.val.size / 2) :
    num_mismatches arr i = mismatchAt arr i + num_mismatches arr (i + 1) := by
  conv => lhs; unfold num_mismatches
  rw [dif_pos h]

private theorem num_mismatches_oob (arr : RustSlice i64) (i : Nat)
    (h : ¬ i < arr.val.size / 2) :
    num_mismatches arr i = 0 := by
  unfold num_mismatches
  rw [dif_neg h]

private theorem mismatchAt_eq (arr : RustSlice i64) (i : Nat)
    (hi : i < arr.val.size) (hmirror : arr.val.size - 1 - i < arr.val.size) :
    mismatchAt arr i =
      (if arr.val[i]'hi ≠ arr.val[arr.val.size - 1 - i]'hmirror then 1 else 0) := by
  unfold mismatchAt
  rw [dif_pos (And.intro hi hmirror)]

private theorem mismatchAt_le_one (arr : RustSlice i64) (i : Nat) :
    mismatchAt arr i ≤ 1 := by
  unfold mismatchAt
  by_cases h : i < arr.val.size ∧ arr.val.size - 1 - i < arr.val.size
  · rw [dif_pos h]
    by_cases h2 : arr.val[i]'h.1 ≠ arr.val[arr.val.size - 1 - i]'h.2
    · rw [if_pos h2]; omega
    · rw [if_neg h2]; omega
  · rw [dif_neg h]; omega

/-! ## Pre-computed reductions used inside the step lemmas -/

/-- `core_models.slice.Impl.len i64 arr = RustM.ok (USize64.ofNat arr.val.size)`. -/
private theorem len_pure_eval (arr : RustSlice i64) :
    core_models.slice.Impl.len i64 arr = RustM.ok (USize64.ofNat arr.val.size) := by
  unfold core_models.slice.Impl.len rust_primitives.slice.slice_length; rfl

/-- `(USize64.ofNat arr.val.size) /? 2 = RustM.ok ((USize64.ofNat arr.val.size) / 2)`. -/
private theorem div_two_pure (arr : RustSlice i64) :
    ((USize64.ofNat arr.val.size) /? (2 : usize) : RustM usize) =
      RustM.ok ((USize64.ofNat arr.val.size) / 2) := by
  show (rust_primitives.ops.arith.Div.div (USize64.ofNat arr.val.size) (2 : usize)
        : RustM usize) = _
  show (if (2 : usize) = 0 then (RustM.fail .divisionByZero : RustM usize)
        else pure ((USize64.ofNat arr.val.size) / 2)) = _
  rw [if_neg (by decide : (2 : usize) ≠ 0)]
  rfl

private theorem half_size_toNat (arr : RustSlice i64) :
    ((USize64.ofNat arr.val.size) / 2).toNat = arr.val.size / 2 := by
  rw [div_two_toNat]
  have h_size_lt : arr.val.size < 2^64 := arr.size_lt_usizeSize
  rw [USize64.toNat_ofNat_of_lt' h_size_lt]

/-- `(USize64.ofNat arr.val.size) -? 1 = RustM.ok (USize64.ofNat arr.val.size - 1)` when size > 0. -/
private theorem size_sub_one_pure (arr : RustSlice i64) (hne : 0 < arr.val.size) :
    ((USize64.ofNat arr.val.size) -? (1 : usize) : RustM usize) =
      RustM.ok ((USize64.ofNat arr.val.size) - 1) := by
  have h_size_lt : arr.val.size < 2^64 := arr.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat arr.val.size).toNat = arr.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_no_bv :
      BitVec.usubOverflow (USize64.ofNat arr.val.size).toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.usubOverflow (USize64.ofNat arr.val.size).toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have h_sov : USize64.subOverflow (USize64.ofNat arr.val.size) (1 : usize) = true := hbo
      have hh := USize64.subOverflow_iff.mp h_sov
      rw [usize_one_toNat, h_ofNat] at hh
      omega
  show (rust_primitives.ops.arith.Sub.sub (USize64.ofNat arr.val.size) (1 : usize)
        : RustM usize) = _
  show (if BitVec.usubOverflow (USize64.ofNat arr.val.size).toBitVec (1 : usize).toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure ((USize64.ofNat arr.val.size) - 1)) = _
  rw [h_no_bv]; rfl

private theorem size_sub_one_toNat (arr : RustSlice i64) (hne : 0 < arr.val.size) :
    ((USize64.ofNat arr.val.size) - 1).toNat = arr.val.size - 1 := by
  have h_size_lt : arr.val.size < 2^64 := arr.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat arr.val.size).toNat = arr.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h1 : (1 : usize).toNat ≤ (USize64.ofNat arr.val.size).toNat := by
    rw [usize_one_toNat, h_ofNat]; omega
  rw [USize64.toNat_sub_of_le' h1, h_ofNat, usize_one_toNat]

/-- `(USize64.ofNat arr.val.size - 1) -? i = RustM.ok ((USize64.ofNat arr.val.size - 1) - i)`
    when `i.toNat + 1 ≤ arr.val.size`. -/
private theorem sub_i_pure (arr : RustSlice i64) (i : usize) (hne : 0 < arr.val.size)
    (h_le : i.toNat + 1 ≤ arr.val.size) :
    (((USize64.ofNat arr.val.size) - 1) -? i : RustM usize) =
      RustM.ok (((USize64.ofNat arr.val.size) - 1) - i) := by
  have h_size_lt : arr.val.size < 2^64 := arr.size_lt_usizeSize
  have h_nm1_toNat : ((USize64.ofNat arr.val.size) - 1).toNat = arr.val.size - 1 :=
    size_sub_one_toNat arr hne
  have h_no_bv :
      BitVec.usubOverflow ((USize64.ofNat arr.val.size) - 1).toBitVec i.toBitVec = false := by
    generalize hbo : BitVec.usubOverflow ((USize64.ofNat arr.val.size) - 1).toBitVec i.toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have h_sov : USize64.subOverflow ((USize64.ofNat arr.val.size) - 1) i = true := hbo
      have hh := USize64.subOverflow_iff.mp h_sov
      rw [h_nm1_toNat] at hh
      omega
  show (rust_primitives.ops.arith.Sub.sub ((USize64.ofNat arr.val.size) - 1) i
        : RustM usize) = _
  show (if BitVec.usubOverflow ((USize64.ofNat arr.val.size) - 1).toBitVec i.toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure (((USize64.ofNat arr.val.size) - 1) - i)) = _
  rw [h_no_bv]; rfl

private theorem sub_i_toNat (arr : RustSlice i64) (i : usize) (hne : 0 < arr.val.size)
    (h_le : i.toNat + 1 ≤ arr.val.size) :
    (((USize64.ofNat arr.val.size) - 1) - i).toNat = arr.val.size - 1 - i.toNat := by
  have h_nm1_toNat : ((USize64.ofNat arr.val.size) - 1).toNat = arr.val.size - 1 :=
    size_sub_one_toNat arr hne
  have h_le_bv : i.toNat ≤ ((USize64.ofNat arr.val.size) - 1).toNat := by
    rw [h_nm1_toNat]; omega
  rw [USize64.toNat_sub_of_le' h_le_bv, h_nm1_toNat]

/-- Indexing via `arr[i]_?` evaluates to `ok` when bounds-checked. -/
private theorem slice_idx_ok (arr : RustSlice i64) (i : usize)
    (hi : i.toNat < arr.val.size) :
    (arr[i]_? : RustM i64) = RustM.ok (arr.val[i.toNat]'hi) := by
  show (if h : i.toNat < arr.val.size then (pure (arr.val[i]) : RustM i64)
        else RustM.fail Error.arrayOutOfBounds) = RustM.ok (arr.val[i.toNat]'hi)
  rw [dif_pos hi]; rfl

/-- Add `+? 1` for usize succeeds when no overflow. -/
private theorem usize_add_one_pure (i : usize) (h : i.toNat + 1 < 2^64) :
    (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  have h_no_bv : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hh := (USize64.uaddOverflow_iff i 1).mp hbo
      rw [usize_one_toNat] at hh
      omega
  show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = _
  show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure (i + 1)) = _
  rw [h_no_bv]; rfl

/-- Add `+? 1` for i64 succeeds when no overflow (i.e. `acc.toInt + 1 < 2^63`). -/
private theorem i64_add_one_pure (acc : i64) (h : acc.toInt + 1 < 2^63) :
    (acc +? (1 : i64) : RustM i64) = RustM.ok (acc + 1) := by
  have h_no_bv :
      BitVec.saddOverflow acc.toBitVec (1 : i64).toBitVec = false := by
    generalize hbo : BitVec.saddOverflow acc.toBitVec (1 : i64).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hov : Int64.addOverflow acc 1 := hbo
      rw [Int64.addOverflow_iff] at hov
      rw [i64_one_toInt] at hov
      have h_lo : Int64.minValue.toInt ≤ acc.toInt := acc.le_toInt
      have h_lo' : -(2^63 : Int) ≤ acc.toInt := by
        rw [← Int64.toInt_minValue]; exact h_lo
      have h_hi : acc.toInt < 2^63 := acc.toInt_lt
      rcases hov with hov_pos | hov_neg
      · omega
      · omega
  show (rust_primitives.ops.arith.Add.add acc (1 : i64) : RustM i64) = _
  show (if BitVec.saddOverflow acc.toBitVec (1 : i64).toBitVec
        then (.fail .integerOverflow : RustM i64)
        else pure (acc + 1)) = _
  rw [h_no_bv]; rfl

private theorem i64_add_one_toInt (acc : i64) (h : acc.toInt + 1 < 2^63) :
    (acc + 1).toInt = acc.toInt + 1 := by
  have h_no_ov : ¬ Int64.addOverflow acc 1 := by
    intro hov
    rw [Int64.addOverflow_iff, i64_one_toInt] at hov
    have h_lo : Int64.minValue.toInt ≤ acc.toInt := acc.le_toInt
    have h_lo' : -(2^63 : Int) ≤ acc.toInt := by
      rw [← Int64.toInt_minValue]; exact h_lo
    have h_hi : acc.toInt < 2^63 := acc.toInt_lt
    rcases hov with hov_pos | hov_neg
    · omega
    · omega
  rw [Int64.toInt_add_of_not_addOverflow h_no_ov, i64_one_toInt]

/-! ## Step lemmas for `count_mismatches_at`

Three branches of the recursive body, packaged so the strong-induction
work in `count_mismatches_at_correct` can rewrite the goal directly. -/

/-- OOB step: when `i.toNat ≥ arr.val.size / 2`, the function returns `RustM.ok acc`. -/
private theorem count_mismatches_at_oob (arr : RustSlice i64) (i : usize) (acc : i64)
    (hi : arr.val.size / 2 ≤ i.toNat) :
    clever_072_smallest_change.count_mismatches_at arr i acc = RustM.ok acc := by
  conv => lhs; unfold clever_072_smallest_change.count_mismatches_at
  rw [len_pure_eval arr, RustM_ok_bind, div_two_pure arr, RustM_ok_bind]
  have h_half_toNat : ((USize64.ofNat arr.val.size) / 2).toNat = arr.val.size / 2 :=
    half_size_toNat arr
  have h_cond : decide (((USize64.ofNat arr.val.size) / 2) ≤ i) = true := by
    rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_half_toNat]
    exact hi
  show ((rust_primitives.cmp.ge i ((USize64.ofNat arr.val.size) / 2) : RustM Bool) >>= _) = _
  show (pure (decide (((USize64.ofNat arr.val.size) / 2) ≤ i)) >>= _) = _
  rw [h_cond]; rfl

/-- Mismatch step: in the recursive case, when `arr[i] ≠ arr[n-1-i]`. -/
private theorem count_mismatches_at_mismatch (arr : RustSlice i64) (i : usize) (acc : i64)
    (h_lt : i.toNat < arr.val.size / 2)
    (h_acc_no_overflow : acc.toInt + 1 < 2^63)
    (hi : i.toNat < arr.val.size)
    (hmirror : arr.val.size - 1 - i.toNat < arr.val.size)
    (hne : arr.val[i.toNat]'hi ≠ arr.val[arr.val.size - 1 - i.toNat]'hmirror) :
    clever_072_smallest_change.count_mismatches_at arr i acc =
      clever_072_smallest_change.count_mismatches_at arr (i + 1) (acc + 1) := by
  have h_size_pos : 0 < arr.val.size :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) hi
  have h_i_plus_one_le : i.toNat + 1 ≤ arr.val.size := by omega
  have h_no_ov_i : i.toNat + 1 < 2^64 := by
    have h_size_lt : arr.val.size < 2^64 := arr.size_lt_usizeSize
    omega
  conv => lhs; unfold clever_072_smallest_change.count_mismatches_at
  rw [len_pure_eval arr, RustM_ok_bind, div_two_pure arr, RustM_ok_bind]
  have h_half_toNat : ((USize64.ofNat arr.val.size) / 2).toNat = arr.val.size / 2 :=
    half_size_toNat arr
  have h_cond : decide (((USize64.ofNat arr.val.size) / 2) ≤ i) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_half_toNat]
    omega
  show ((rust_primitives.cmp.ge i ((USize64.ofNat arr.val.size) / 2) : RustM Bool) >>= _) = _
  show (pure (decide (((USize64.ofNat arr.val.size) / 2) ≤ i)) >>= _) = _
  rw [h_cond, pure_bind]
  simp only [Bool.false_eq_true, ↓reduceIte]
  -- Now the body is the recursive arithmetic+indexing block.
  have h_idx_i : (arr[i]_? : RustM i64) = RustM.ok (arr.val[i.toNat]'hi) :=
    slice_idx_ok arr i hi
  have h_sub_lt : ((USize64.ofNat arr.val.size - 1) - i).toNat < arr.val.size := by
    rw [sub_i_toNat arr i h_size_pos h_i_plus_one_le]; omega
  have h_idx_mirror :
      (arr[((USize64.ofNat arr.val.size) - 1) - i]_? : RustM i64) =
        RustM.ok (arr.val[(((USize64.ofNat arr.val.size) - 1) - i).toNat]'h_sub_lt) :=
    slice_idx_ok arr (((USize64.ofNat arr.val.size) - 1) - i) h_sub_lt
  have h_mirror_eq :
      arr.val[(((USize64.ofNat arr.val.size) - 1) - i).toNat]'h_sub_lt =
        arr.val[arr.val.size - 1 - i.toNat]'hmirror := by
    apply getElem_idx_congr
    rw [sub_i_toNat arr i h_size_pos h_i_plus_one_le]
  have h_bne :
      (arr.val[i.toNat]'hi !=
        arr.val[(((USize64.ofNat arr.val.size) - 1) - i).toNat]'h_sub_lt) = true := by
    rw [bne_iff_ne]
    intro h_eq
    apply hne
    rw [h_eq, h_mirror_eq]
  -- Reduce arithmetic and indexing
  rw [size_sub_one_pure arr h_size_pos]
  simp only [RustM_ok_bind, sub_i_pure arr i h_size_pos h_i_plus_one_le, h_idx_i, h_idx_mirror]
  -- The != comparison reduces to its Bool value
  show (((arr.val[i.toNat]'hi) !=? (arr.val[(((USize64.ofNat arr.val.size) - 1) - i).toNat]'h_sub_lt)
          : RustM Bool) >>= _) = _
  show (pure ((arr.val[i.toNat]'hi) !=
              (arr.val[(((USize64.ofNat arr.val.size) - 1) - i).toNat]'h_sub_lt)) >>= _) = _
  rw [h_bne, pure_bind]
  simp only [↓reduceIte]
  rw [usize_add_one_pure i h_no_ov_i, RustM_ok_bind,
      i64_add_one_pure acc h_acc_no_overflow, RustM_ok_bind]

/-- Match step: in the recursive case, when `arr[i] = arr[n-1-i]`. -/
private theorem count_mismatches_at_match (arr : RustSlice i64) (i : usize) (acc : i64)
    (h_lt : i.toNat < arr.val.size / 2)
    (hi : i.toNat < arr.val.size)
    (hmirror : arr.val.size - 1 - i.toNat < arr.val.size)
    (heq : arr.val[i.toNat]'hi = arr.val[arr.val.size - 1 - i.toNat]'hmirror) :
    clever_072_smallest_change.count_mismatches_at arr i acc =
      clever_072_smallest_change.count_mismatches_at arr (i + 1) acc := by
  have h_size_pos : 0 < arr.val.size :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) hi
  have h_i_plus_one_le : i.toNat + 1 ≤ arr.val.size := by omega
  have h_no_ov_i : i.toNat + 1 < 2^64 := by
    have h_size_lt : arr.val.size < 2^64 := arr.size_lt_usizeSize
    omega
  conv => lhs; unfold clever_072_smallest_change.count_mismatches_at
  rw [len_pure_eval arr, RustM_ok_bind, div_two_pure arr, RustM_ok_bind]
  have h_half_toNat : ((USize64.ofNat arr.val.size) / 2).toNat = arr.val.size / 2 :=
    half_size_toNat arr
  have h_cond : decide (((USize64.ofNat arr.val.size) / 2) ≤ i) = false := by
    rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_half_toNat]
    omega
  show ((rust_primitives.cmp.ge i ((USize64.ofNat arr.val.size) / 2) : RustM Bool) >>= _) = _
  show (pure (decide (((USize64.ofNat arr.val.size) / 2) ≤ i)) >>= _) = _
  rw [h_cond, pure_bind]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have h_idx_i : (arr[i]_? : RustM i64) = RustM.ok (arr.val[i.toNat]'hi) :=
    slice_idx_ok arr i hi
  have h_sub_lt : ((USize64.ofNat arr.val.size - 1) - i).toNat < arr.val.size := by
    rw [sub_i_toNat arr i h_size_pos h_i_plus_one_le]; omega
  have h_idx_mirror :
      (arr[((USize64.ofNat arr.val.size) - 1) - i]_? : RustM i64) =
        RustM.ok (arr.val[(((USize64.ofNat arr.val.size) - 1) - i).toNat]'h_sub_lt) :=
    slice_idx_ok arr (((USize64.ofNat arr.val.size) - 1) - i) h_sub_lt
  have h_mirror_eq :
      arr.val[(((USize64.ofNat arr.val.size) - 1) - i).toNat]'h_sub_lt =
        arr.val[arr.val.size - 1 - i.toNat]'hmirror := by
    apply getElem_idx_congr
    rw [sub_i_toNat arr i h_size_pos h_i_plus_one_le]
  have h_bne :
      (arr.val[i.toNat]'hi !=
        arr.val[(((USize64.ofNat arr.val.size) - 1) - i).toNat]'h_sub_lt) = false := by
    rw [bne_eq_false_iff_eq, h_mirror_eq]
    exact heq
  rw [size_sub_one_pure arr h_size_pos]
  simp only [RustM_ok_bind, sub_i_pure arr i h_size_pos h_i_plus_one_le, h_idx_i, h_idx_mirror]
  show (((arr.val[i.toNat]'hi) !=? (arr.val[(((USize64.ofNat arr.val.size) - 1) - i).toNat]'h_sub_lt)
          : RustM Bool) >>= _) = _
  show (pure ((arr.val[i.toNat]'hi) !=
              (arr.val[(((USize64.ofNat arr.val.size) - 1) - i).toNat]'h_sub_lt)) >>= _) = _
  rw [h_bne, pure_bind]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [usize_add_one_pure i h_no_ov_i, RustM_ok_bind]

/-! ## Bound on `num_mismatches` -/

private theorem num_mismatches_le (arr : RustSlice i64) :
    ∀ i : Nat, num_mismatches arr i ≤ arr.val.size / 2 - i := by
  intro i
  induction hk : (arr.val.size / 2 - i) using Nat.strongRecOn generalizing i with
  | _ k ih =>
    by_cases h : i < arr.val.size / 2
    · rw [num_mismatches_step arr i h]
      have h_meas : arr.val.size / 2 - (i + 1) < k := by rw [← hk]; omega
      have h_ih := ih (arr.val.size / 2 - (i + 1)) h_meas (i + 1) rfl
      have h_m := mismatchAt_le_one arr i
      omega
    · rw [num_mismatches_oob arr i h]
      omega

private theorem num_mismatches_zero_le (arr : RustSlice i64) :
    num_mismatches arr 0 ≤ arr.val.size / 2 := by
  have h := num_mismatches_le arr 0
  omega

/-- The half-size fits inside i64: `arr.val.size / 2 < 2^63`. -/
private theorem half_size_lt_two_pow_63 (arr : RustSlice i64) :
    arr.val.size / 2 < 2^63 := by
  have h : arr.val.size < 2^64 := arr.size_lt_usizeSize
  omega

/-! ## Strong induction: `count_mismatches_at` agrees with `num_mismatches`

The induction measure is `arr.val.size / 2 - i.toNat`. The invariant
maintains `acc.toInt + num_mismatches arr i.toNat ≤ arr.val.size / 2`,
which discharges all the overflow obligations. -/
private theorem count_mismatches_at_correct (arr : RustSlice i64) :
    ∀ (m : Nat) (i : usize) (acc : i64),
      arr.val.size / 2 - i.toNat ≤ m →
      0 ≤ acc.toInt →
      acc.toInt + (num_mismatches arr i.toNat : Int) ≤ (arr.val.size / 2 : Int) →
      ∃ r : i64,
        clever_072_smallest_change.count_mismatches_at arr i acc = RustM.ok r ∧
        r.toInt = acc.toInt + (num_mismatches arr i.toNat : Int) := by
  intro m
  induction m with
  | zero =>
    intro i acc hm h_acc_nneg h_bound
    have hge : arr.val.size / 2 ≤ i.toNat := by omega
    have h_oob := count_mismatches_at_oob arr i acc hge
    refine ⟨acc, h_oob, ?_⟩
    have h_num0 : num_mismatches arr i.toNat = 0 := num_mismatches_oob arr i.toNat (by omega)
    rw [h_num0]; simp
  | succ m ih =>
    intro i acc hm h_acc_nneg h_bound
    by_cases hge : arr.val.size / 2 ≤ i.toNat
    · have h_oob := count_mismatches_at_oob arr i acc hge
      refine ⟨acc, h_oob, ?_⟩
      have h_num0 : num_mismatches arr i.toNat = 0 := num_mismatches_oob arr i.toNat (by omega)
      rw [h_num0]; simp
    · have h_lt : i.toNat < arr.val.size / 2 := Nat.lt_of_not_le hge
      have hi : i.toNat < arr.val.size :=
        Nat.lt_of_lt_of_le h_lt (Nat.div_le_self _ _)
      have h_size_pos : 0 < arr.val.size := Nat.lt_of_le_of_lt (Nat.zero_le _) hi
      have hmirror : arr.val.size - 1 - i.toNat < arr.val.size := by omega
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        have h_size_lt : arr.val.size < 2^64 := arr.size_lt_usizeSize
        omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_step_num := num_mismatches_step arr i.toNat h_lt
      have h_mismatchAt_eq := mismatchAt_eq arr i.toNat hi hmirror
      by_cases hne : arr.val[i.toNat]'hi ≠ arr.val[arr.val.size - 1 - i.toNat]'hmirror
      · -- Mismatch case: recursive call uses (i+1, acc+1)
        have h_mismatch_one : mismatchAt arr i.toNat = 1 := by
          rw [h_mismatchAt_eq, if_pos hne]
        have h_num_i_pos : 1 ≤ num_mismatches arr i.toNat := by
          rw [h_step_num, h_mismatch_one]; omega
        have h_acc_plus_one_lt : acc.toInt + 1 < 2^63 := by
          have h_half_lt : arr.val.size / 2 < 2^63 := half_size_lt_two_pow_63 arr
          have h1 : (1 : Int) ≤ (num_mismatches arr i.toNat : Int) := by
            have h_int : ((1 : Nat) : Int) ≤ ((num_mismatches arr i.toNat : Nat) : Int) :=
              Int.ofNat_le.mpr h_num_i_pos
            simpa using h_int
          have h_half_le : acc.toInt + (num_mismatches arr i.toNat : Int) ≤
                            (arr.val.size / 2 : Int) := h_bound
          have h_half_lt_int : ((arr.val.size / 2 : Nat) : Int) < (2^63 : Int) := by
            have : ((arr.val.size / 2 : Nat) : Int) = (arr.val.size / 2 : Int) := rfl
            omega
          omega
        have h_step :=
          count_mismatches_at_mismatch arr i acc h_lt h_acc_plus_one_lt hi hmirror hne
        rw [h_step]
        have h_acc_new_toInt : (acc + 1).toInt = acc.toInt + 1 :=
          i64_add_one_toInt acc h_acc_plus_one_lt
        have h_acc_new_nneg : 0 ≤ (acc + 1).toInt := by
          rw [h_acc_new_toInt]; omega
        have h_meas : arr.val.size / 2 - (i + 1).toNat ≤ m := by
          rw [h_i1]; omega
        have h_num_eq : num_mismatches arr i.toNat = 1 + num_mismatches arr (i.toNat + 1) := by
          rw [h_step_num, h_mismatch_one]
        have h_bound_new :
            (acc + 1).toInt + (num_mismatches arr (i + 1).toNat : Int) ≤
              (arr.val.size / 2 : Int) := by
          rw [h_acc_new_toInt, h_i1]
          have h_orig : acc.toInt + (num_mismatches arr i.toNat : Int) ≤
                          (arr.val.size / 2 : Int) := h_bound
          omega
        obtain ⟨r, h_rec, h_rec_toInt⟩ :=
          ih (i + 1) (acc + 1) h_meas h_acc_new_nneg h_bound_new
        refine ⟨r, h_rec, ?_⟩
        rw [h_rec_toInt, h_acc_new_toInt, h_i1]
        omega
      · -- Match case: recursive call uses (i+1, acc)
        have h_eq_pair : arr.val[i.toNat]'hi =
                          arr.val[arr.val.size - 1 - i.toNat]'hmirror :=
          Classical.not_not.mp hne
        have h_mismatch_zero : mismatchAt arr i.toNat = 0 := by
          rw [h_mismatchAt_eq, if_neg hne]
        have h_step :=
          count_mismatches_at_match arr i acc h_lt hi hmirror h_eq_pair
        rw [h_step]
        have h_meas : arr.val.size / 2 - (i + 1).toNat ≤ m := by
          rw [h_i1]; omega
        have h_num_eq : num_mismatches arr i.toNat = num_mismatches arr (i.toNat + 1) := by
          rw [h_step_num, h_mismatch_zero]; omega
        have h_bound_new :
            acc.toInt + (num_mismatches arr (i + 1).toNat : Int) ≤
              (arr.val.size / 2 : Int) := by
          rw [h_i1]
          have h_orig : acc.toInt + (num_mismatches arr i.toNat : Int) ≤
                          (arr.val.size / 2 : Int) := h_bound
          omega
        obtain ⟨r, h_rec, h_rec_toInt⟩ :=
          ih (i + 1) acc h_meas h_acc_nneg h_bound_new
        refine ⟨r, h_rec, ?_⟩
        rw [h_rec_toInt, h_i1]
        omega

/-! ## Top-level evaluator for `smallest_change` -/

/-- `smallest_change arr` returns the i64 representation of `num_mismatches arr 0`. -/
private theorem smallest_change_correct (arr : RustSlice i64) :
    ∃ r : i64,
      clever_072_smallest_change.smallest_change arr = RustM.ok r ∧
      r.toInt = (num_mismatches arr 0 : Int) := by
  unfold clever_072_smallest_change.smallest_change
  have h_zero_toNat : (0 : usize).toNat = 0 := usize_zero_toNat
  have h_acc_nneg : (0 : Int) ≤ (0 : i64).toInt := by rw [i64_zero_toInt]; omega
  have h_bound : (0 : i64).toInt + (num_mismatches arr (0 : usize).toNat : Int) ≤
                  ((arr.val.size / 2 : Nat) : Int) := by
    rw [h_zero_toNat, i64_zero_toInt, Int.zero_add]
    exact Int.ofNat_le.mpr (num_mismatches_zero_le arr)
  have h_meas : arr.val.size / 2 - (0 : usize).toNat ≤ arr.val.size / 2 := by
    rw [h_zero_toNat]; omega
  obtain ⟨r, h_eq, h_toInt⟩ :=
    count_mismatches_at_correct arr (arr.val.size / 2) (0 : usize) (0 : i64)
      h_meas h_acc_nneg h_bound
  refine ⟨r, h_eq, ?_⟩
  rw [h_toInt, h_zero_toNat, i64_zero_toInt, Int.zero_add]

/-! ## Bridge: `num_mismatches arr 0 = 0 ↔ is_palindrome arr` -/

private theorem num_mismatches_zero_iff (arr : RustSlice i64) :
    num_mismatches arr 0 = 0 ↔ is_palindrome arr := by
  constructor
  · intro h_zero i h_lt h_i_lt h_mirror_lt
    -- Strong induction: num_mismatches arr j = 0 → for all k ≥ j in [0, n/2), arr[k] = arr[n-1-k]
    have h_aux : ∀ (m : Nat) (j : Nat),
        arr.val.size / 2 - j ≤ m →
        num_mismatches arr j = 0 →
        ∀ k : Nat, j ≤ k → k < arr.val.size / 2 →
          ∀ (hk : k < arr.val.size) (hmk : arr.val.size - 1 - k < arr.val.size),
            arr.val[k]'hk = arr.val[arr.val.size - 1 - k]'hmk := by
      intro m
      induction m with
      | zero =>
        intro j _hm _hzero k hjk hk_lt _hk _hmk
        omega
      | succ m ih =>
        intro j hm hzero k hjk hk_lt hk hmk
        have hj_lt : j < arr.val.size / 2 := Nat.lt_of_le_of_lt hjk hk_lt
        have hj_i_lt : j < arr.val.size :=
          Nat.lt_of_lt_of_le hj_lt (Nat.div_le_self _ _)
        have h_size_pos : 0 < arr.val.size := Nat.lt_of_le_of_lt (Nat.zero_le _) hj_i_lt
        have hj_mirror_lt : arr.val.size - 1 - j < arr.val.size := by omega
        have h_step := num_mismatches_step arr j hj_lt
        have h_mAt := mismatchAt_eq arr j hj_i_lt hj_mirror_lt
        rw [h_step] at hzero
        have h_mAt_zero : mismatchAt arr j = 0 := by
          have h_rest_le : num_mismatches arr (j + 1) ≥ 0 := Nat.zero_le _
          have h_mAt_le : mismatchAt arr j ≤ 1 := mismatchAt_le_one arr j
          omega
        have h_eq_pair : arr.val[j]'hj_i_lt =
                          arr.val[arr.val.size - 1 - j]'hj_mirror_lt := by
          rw [h_mAt] at h_mAt_zero
          by_cases h_ne : arr.val[j]'hj_i_lt ≠ arr.val[arr.val.size - 1 - j]'hj_mirror_lt
          · exfalso; rw [if_pos h_ne] at h_mAt_zero; omega
          · exact Classical.not_not.mp h_ne
        have h_rest_zero : num_mismatches arr (j + 1) = 0 := by
          -- hzero : mismatchAt arr j + num_mismatches arr (j+1) = 0
          -- h_mAt_zero : mismatchAt arr j = 0
          omega
        by_cases hjk_eq : j = k
        · subst hjk_eq; exact h_eq_pair
        · have hjk_lt : j + 1 ≤ k := by omega
          have h_meas : arr.val.size / 2 - (j + 1) ≤ m := by omega
          exact ih (j + 1) h_meas h_rest_zero k hjk_lt hk_lt hk hmk
    exact h_aux (arr.val.size / 2) 0 (by omega) h_zero i (Nat.zero_le _) h_lt h_i_lt h_mirror_lt
  · intro hpal
    -- All pairs are equal; so num_mismatches is 0 at every i
    have h_aux : ∀ (m : Nat) (j : Nat),
        arr.val.size / 2 - j ≤ m →
        num_mismatches arr j = 0 := by
      intro m
      induction m with
      | zero =>
        intro j hm
        apply num_mismatches_oob arr j; omega
      | succ m ih =>
        intro j hm
        by_cases hj_lt : j < arr.val.size / 2
        · have hj_i_lt : j < arr.val.size :=
            Nat.lt_of_lt_of_le hj_lt (Nat.div_le_self _ _)
          have hj_mirror_lt : arr.val.size - 1 - j < arr.val.size := by
            have h_size_pos : 0 < arr.val.size := Nat.lt_of_le_of_lt (Nat.zero_le _) hj_i_lt
            omega
          have h_step := num_mismatches_step arr j hj_lt
          have h_mAt := mismatchAt_eq arr j hj_i_lt hj_mirror_lt
          have h_eq : arr.val[j]'hj_i_lt = arr.val[arr.val.size - 1 - j]'hj_mirror_lt :=
            hpal j hj_lt hj_i_lt hj_mirror_lt
          have h_mAt_zero : mismatchAt arr j = 0 := by
            rw [h_mAt, if_neg (Classical.not_not.mpr h_eq)]
          have h_meas : arr.val.size / 2 - (j + 1) ≤ m := by omega
          have h_rest := ih (j + 1) h_meas
          rw [h_step, h_mAt_zero, h_rest]
        · exact num_mismatches_oob arr j hj_lt
    exact h_aux (arr.val.size / 2) 0 (by omega)

/-! ## Reversal-invariance bridge for `num_mismatches` -/

/-- If two slices have the same size and `arr2[n-1-k] = arr1[k]` for all `k`,
    then they yield the same mismatch count at every index. -/
private theorem num_mismatches_reverse_eq (arr1 arr2 : RustSlice i64)
    (hsize : arr1.val.size = arr2.val.size)
    (hrev : ∀ k : Nat, ∀ (hk1 : k < arr1.val.size)
              (hk2 : arr2.val.size - 1 - k < arr2.val.size),
              arr2.val[arr2.val.size - 1 - k]'hk2 = arr1.val[k]'hk1) :
    num_mismatches arr1 0 = num_mismatches arr2 0 := by
  have h_aux : ∀ (m : Nat) (j : Nat),
      arr1.val.size / 2 - j ≤ m →
      num_mismatches arr1 j = num_mismatches arr2 j := by
    intro m
    induction m with
    | zero =>
      intro j hm
      have hj_ge1 : ¬ j < arr1.val.size / 2 := by omega
      have hj_ge2 : ¬ j < arr2.val.size / 2 := by rw [← hsize]; exact hj_ge1
      rw [num_mismatches_oob arr1 j hj_ge1, num_mismatches_oob arr2 j hj_ge2]
    | succ m ih =>
      intro j hm
      by_cases hj_lt : j < arr1.val.size / 2
      · have hj_lt2 : j < arr2.val.size / 2 := by rw [← hsize]; exact hj_lt
        have hj_i_lt1 : j < arr1.val.size :=
          Nat.lt_of_lt_of_le hj_lt (Nat.div_le_self _ _)
        have h_size_pos1 : 0 < arr1.val.size := Nat.lt_of_le_of_lt (Nat.zero_le _) hj_i_lt1
        have hj_mirror_lt1 : arr1.val.size - 1 - j < arr1.val.size := by omega
        have hj_i_lt2 : j < arr2.val.size := by rw [← hsize]; exact hj_i_lt1
        have hj_mirror_lt2 : arr2.val.size - 1 - j < arr2.val.size := by
          rw [← hsize]; exact hj_mirror_lt1
        have h_step1 := num_mismatches_step arr1 j hj_lt
        have h_step2 := num_mismatches_step arr2 j hj_lt2
        have h_mAt1 := mismatchAt_eq arr1 j hj_i_lt1 hj_mirror_lt1
        have h_mAt2 := mismatchAt_eq arr2 j hj_i_lt2 hj_mirror_lt2
        -- Bridge: arr1[j] = arr1[n-1-j]  iff  arr2[j] = arr2[n-1-j].
        have h_mirror_arr2_pair :
            arr2.val[arr2.val.size - 1 - j]'hj_mirror_lt2 = arr1.val[j]'hj_i_lt1 :=
          hrev j hj_i_lt1 hj_mirror_lt2
        have h_arr2_j_eq :
            arr2.val[j]'hj_i_lt2 = arr1.val[arr1.val.size - 1 - j]'hj_mirror_lt1 := by
          have h_other_mirror_lt :
              arr2.val.size - 1 - (arr1.val.size - 1 - j) < arr2.val.size := by
            rw [← hsize]; omega
          have h_apply := hrev (arr1.val.size - 1 - j) hj_mirror_lt1 h_other_mirror_lt
          have h_idx_collapse : arr2.val.size - 1 - (arr1.val.size - 1 - j) = j := by
            rw [← hsize]; omega
          have h_arr2_idx_eq :
              arr2.val[arr2.val.size - 1 - (arr1.val.size - 1 - j)]'h_other_mirror_lt =
                arr2.val[j]'hj_i_lt2 :=
            getElem_idx_congr arr2 _ _ h_other_mirror_lt hj_i_lt2 h_idx_collapse
          rw [← h_arr2_idx_eq]; exact h_apply
        have h_mAt_eq : mismatchAt arr1 j = mismatchAt arr2 j := by
          rw [h_mAt1, h_mAt2, h_arr2_j_eq, h_mirror_arr2_pair]
          by_cases h_eq : arr1.val[j]'hj_i_lt1 = arr1.val[arr1.val.size - 1 - j]'hj_mirror_lt1
          · rw [if_neg (Classical.not_not.mpr h_eq), if_neg (Classical.not_not.mpr h_eq.symm)]
          · have h_ne_sym : arr1.val[arr1.val.size - 1 - j]'hj_mirror_lt1 ≠
                              arr1.val[j]'hj_i_lt1 := fun h => h_eq h.symm
            rw [if_pos h_eq, if_pos h_ne_sym]
        rw [h_step1, h_step2, h_mAt_eq]
        have h_meas : arr1.val.size / 2 - (j + 1) ≤ m := by omega
        rw [ih (j + 1) h_meas]
      · have hj_ge2 : ¬ j < arr2.val.size / 2 := by rw [← hsize]; exact hj_lt
        rw [num_mismatches_oob arr1 j hj_lt, num_mismatches_oob arr2 j hj_ge2]
  exact h_aux (arr1.val.size / 2) 0 (by omega)

/-! ## Top-level contract clauses -/

/-- Functional correctness against the reference oracle: `smallest_change`
    returns a successful `i64` whose integer value equals the count of
    mismatched mirror pairs. Encodes the `matches_brute_force` proptest. -/
theorem matches_brute_force (arr : RustSlice i64) :
    ∃ r : i64,
      clever_072_smallest_change.smallest_change arr = RustM.ok r ∧
      r.toInt = (num_mismatches arr 0 : Int) :=
  smallest_change_correct arr

/-- Zero-iff-palindrome: the function returns `0` exactly when the input is
    already a palindrome. Encodes the `zero_iff_palindrome` proptest. -/
theorem zero_iff_palindrome (arr : RustSlice i64) :
    ∃ r : i64,
      clever_072_smallest_change.smallest_change arr = RustM.ok r ∧
      (r = 0 ↔ is_palindrome arr) := by
  obtain ⟨r, h_eq, h_toInt⟩ := smallest_change_correct arr
  refine ⟨r, h_eq, ?_⟩
  rw [← num_mismatches_zero_iff arr]
  constructor
  · intro h_r_zero
    have h_toInt_zero : r.toInt = 0 := by rw [h_r_zero, i64_zero_toInt]
    have h_eq_zero : ((num_mismatches arr 0 : Nat) : Int) = 0 := by
      rw [← h_toInt]; exact h_toInt_zero
    exact_mod_cast h_eq_zero
  · intro h_num_zero
    have h_toInt_zero : r.toInt = 0 := by
      rw [h_toInt, h_num_zero]; rfl
    apply Int64.toInt_inj.mp
    rw [h_toInt_zero, i64_zero_toInt]

/-- Reversal invariance: if `arr2` is the mirror of `arr1` (same length and
    `arr2[n-1-i] = arr1[i]` for every valid `i`), the function returns the
    same result on both inputs. Encodes the `reverse_invariant` proptest. -/
theorem reverse_invariant (arr1 arr2 : RustSlice i64)
    (hsize : arr1.val.size = arr2.val.size)
    (hrev : ∀ i : Nat, ∀ (hi1 : i < arr1.val.size)
              (hi2 : arr2.val.size - 1 - i < arr2.val.size),
              arr2.val[arr2.val.size - 1 - i]'hi2 = arr1.val[i]'hi1) :
    ∃ r : i64,
      clever_072_smallest_change.smallest_change arr1 = RustM.ok r ∧
      clever_072_smallest_change.smallest_change arr2 = RustM.ok r := by
  obtain ⟨r1, h_eq1, h_toInt1⟩ := smallest_change_correct arr1
  obtain ⟨r2, h_eq2, h_toInt2⟩ := smallest_change_correct arr2
  have h_num_eq : num_mismatches arr1 0 = num_mismatches arr2 0 :=
    num_mismatches_reverse_eq arr1 arr2 hsize hrev
  have h_r_toInt_eq : r1.toInt = r2.toInt := by
    rw [h_toInt1, h_toInt2, h_num_eq]
  have h_r_eq : r1 = r2 := Int64.toInt_inj.mp h_r_toInt_eq
  refine ⟨r1, h_eq1, ?_⟩
  rw [h_eq2, h_r_eq]

end Clever_072_smallest_changeObligations
