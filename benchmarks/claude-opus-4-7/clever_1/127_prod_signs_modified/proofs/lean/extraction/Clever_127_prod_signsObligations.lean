-- Companion obligations file for the `clever_127_prod_signs` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_127_prod_signs

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_127_prod_signsObligations

/-! ## Integer-valued specification oracles. -/

/-- Integer signum on `Int`. -/
private def sgn_int (n : Int) : Int :=
  if n = 0 then 0 else if 0 < n then 1 else -1

/-- Integer-valued prefix sum of absolute values. -/
private def sum_abs_int (arr : RustSlice i64) : Nat → Int
  | 0     => 0
  | k + 1 =>
      sum_abs_int arr k +
        (if h : k < arr.val.size then ((arr.val[k]'h).toInt.natAbs : Int) else 0)

/-- Integer-valued prefix product of signums. -/
private def sign_product_int (arr : RustSlice i64) : Nat → Int
  | 0     => 1
  | k + 1 =>
      sign_product_int arr k *
        (if h : k < arr.val.size then sgn_int (arr.val[k]'h).toInt else 1)

/-! ## Helpers -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide
private theorem i64_one_toInt : (1 : i64).toInt = 1 := by decide
private theorem i64_neg_one_toInt : (-1 : i64).toInt = -1 := by decide

private theorem i64_toInt_lt (x : i64) : x.toInt < 2 ^ 63 := by
  have h := Int64.toInt_lt x; simpa using h

private theorem i64_toInt_ge (x : i64) : -(2 ^ 63 : Int) ≤ x.toInt := by
  have h := Int64.le_toInt x; simpa using h

private theorem h63_eq : (2 : Int) ^ (64 - 1) = 2 ^ 63 := by decide

/-- `sum_abs_int` is non-negative for all `k`. -/
private theorem sum_abs_int_nonneg (arr : RustSlice i64) :
    ∀ (k : Nat), 0 ≤ sum_abs_int arr k
  | 0 => Int.le_refl 0
  | k + 1 => by
    show 0 ≤ sum_abs_int arr k +
          (if h : k < arr.val.size then ((arr.val[k]'h).toInt.natAbs : Int) else 0)
    have ih := sum_abs_int_nonneg arr k
    by_cases hk : k < arr.val.size
    · rw [dif_pos hk]
      have h_pos : 0 ≤ ((arr.val[k]'hk).toInt.natAbs : Int) := Int.natCast_nonneg _
      omega
    · rw [dif_neg hk]; omega

/-- Step of `sum_abs_int`. -/
private theorem sum_abs_int_succ
    (arr : RustSlice i64) (k : Nat) (hk : k < arr.val.size) :
    sum_abs_int arr (k + 1) =
      sum_abs_int arr k + ((arr.val[k]'hk).toInt.natAbs : Int) := by
  show sum_abs_int arr k
        + (if h : k < arr.val.size then ((arr.val[k]'h).toInt.natAbs : Int) else 0)
       = sum_abs_int arr k + ((arr.val[k]'hk).toInt.natAbs : Int)
  rw [dif_pos hk]

/-- Step of `sign_product_int`. -/
private theorem sign_product_int_succ
    (arr : RustSlice i64) (k : Nat) (hk : k < arr.val.size) :
    sign_product_int arr (k + 1) =
      sign_product_int arr k * sgn_int (arr.val[k]'hk).toInt := by
  show sign_product_int arr k
        * (if h : k < arr.val.size then sgn_int (arr.val[k]'h).toInt else 1)
       = sign_product_int arr k * sgn_int (arr.val[k]'hk).toInt
  rw [dif_pos hk]

/-- `sgn_int` always returns a value in `{−1, 0, 1}`. -/
private theorem sgn_int_in_set (n : Int) :
    sgn_int n = 0 ∨ sgn_int n = 1 ∨ sgn_int n = -1 := by
  unfold sgn_int
  by_cases h0 : n = 0
  · left; rw [if_pos h0]
  · right
    rw [if_neg h0]
    by_cases hp : 0 < n
    · left; rw [if_pos hp]
    · right; rw [if_neg hp]

/-- `sign_product_int` always lies in `{−1, 0, 1}`. -/
private theorem sign_product_int_in_set (arr : RustSlice i64) :
    ∀ (k : Nat), sign_product_int arr k = 0 ∨ sign_product_int arr k = 1 ∨
                 sign_product_int arr k = -1
  | 0 => Or.inr (Or.inl rfl)
  | k + 1 => by
    show
        (sign_product_int arr k *
          (if h : k < arr.val.size then sgn_int (arr.val[k]'h).toInt else 1)) = 0 ∨
        (sign_product_int arr k *
          (if h : k < arr.val.size then sgn_int (arr.val[k]'h).toInt else 1)) = 1 ∨
        (sign_product_int arr k *
          (if h : k < arr.val.size then sgn_int (arr.val[k]'h).toInt else 1)) = -1
    have ih := sign_product_int_in_set arr k
    by_cases hk : k < arr.val.size
    · rw [dif_pos hk]
      have hsgn := sgn_int_in_set (arr.val[k]'hk).toInt
      rcases ih with hi | hi | hi <;> rcases hsgn with hs | hs | hs <;>
        rw [hi, hs] <;> simp
    · rw [dif_neg hk]
      rcases ih with hi | hi | hi <;> rw [hi] <;> simp

/-! ## Generic step helpers. -/

/-- `(i +? 1 : RustM usize) = RustM.ok (i + 1)` when `i.toNat + 1 < 2^64`. -/
private theorem usize_add_one_eq (i : usize) (h : i.toNat + 1 < 2^64) :
    (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
  have h_no_bv : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hii := (USize64.uaddOverflow_iff i 1).mp hbo
      rw [usize_one_toNat] at hii
      omega
  show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
  show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure (i + 1)) = _
  rw [h_no_bv]; rfl

/-- The unary negation `-? v` on i64 reduces to `pure (-v)` when v ≠ minValue. -/
private theorem i64_neg_eq (v : i64) (h_not_min : v ≠ Int64.minValue) :
    (-? v : RustM i64) = RustM.ok (-v) := by
  show (rust_primitives.ops.arith.Neg.neg v : RustM i64) = _
  show (if v = Int64.minValue
        then (.fail .integerOverflow : RustM i64)
        else pure (-v)) = _
  rw [if_neg h_not_min]; rfl

/-- `a +? b = pure (a + b)` when the i64 addition doesn't overflow. -/
private theorem i64_add_eq (a b : i64) (h_no : ¬ Int64.addOverflow a b) :
    (a +? b : RustM i64) = RustM.ok (a + b) := by
  have h_no_bv : BitVec.saddOverflow a.toBitVec b.toBitVec = false := by
    cases hb : BitVec.saddOverflow a.toBitVec b.toBitVec with
    | false => rfl
    | true => exact absurd hb h_no
  show (rust_primitives.ops.arith.Add.add a b : RustM i64) = _
  show (if BitVec.saddOverflow a.toBitVec b.toBitVec
        then (.fail .integerOverflow : RustM i64)
        else pure (a + b)) = _
  rw [h_no_bv]; rfl

/-- `a *? b = pure (a * b)` when the i64 multiplication doesn't overflow. -/
private theorem i64_mul_eq (a b : i64) (h_no : ¬ Int64.mulOverflow a b) :
    (a *? b : RustM i64) = RustM.ok (a * b) := by
  have h_no_bv : BitVec.smulOverflow a.toBitVec b.toBitVec = false := by
    cases hb : BitVec.smulOverflow a.toBitVec b.toBitVec with
    | false => rfl
    | true => exact absurd hb h_no
  show (rust_primitives.ops.arith.Mul.mul a b : RustM i64) = _
  show (if BitVec.smulOverflow a.toBitVec b.toBitVec
        then (.fail .integerOverflow : RustM i64)
        else pure (a * b)) = _
  rw [h_no_bv]; rfl

private theorem slice_index_eq (arr : RustSlice i64) (i : usize)
    (hi : i.toNat < arr.val.size) :
    (arr[i]_? : RustM i64) = RustM.ok (arr.val[i.toNat]'hi) := by
  show (if h : i.toNat < arr.val.size then pure (arr.val[i])
          else .fail .arrayOutOfBounds)
      = RustM.ok (arr.val[i.toNat]'hi)
  rw [dif_pos hi]; rfl

/-- For the final `sum_abs *? sign`: when `sum_abs ∈ [0, 2^63)` and
    `sign.toInt ∈ {-1, 0, 1}`, no overflow can occur. -/
private theorem no_mul_overflow_of_sign_bounded
    (sum_abs sign : i64)
    (h_lo : 0 ≤ sum_abs.toInt) (h_hi : sum_abs.toInt < 2^63)
    (h_sign : sign.toInt = 0 ∨ sign.toInt = 1 ∨ sign.toInt = -1) :
    ¬ Int64.mulOverflow sum_abs sign := by
  intro hov
  rw [Int64.mulOverflow_iff] at hov
  simp only [h63_eq] at hov
  rcases h_sign with hs | hs | hs
  · rw [hs] at hov
    have h_eq : sum_abs.toInt * 0 = 0 := Int.mul_zero _
    rw [h_eq] at hov
    rcases hov with hp | hn <;> omega
  · rw [hs] at hov
    have h_eq : sum_abs.toInt * 1 = sum_abs.toInt := Int.mul_one _
    rw [h_eq] at hov
    rcases hov with hp | hn <;> omega
  · rw [hs] at hov
    have h_eq : sum_abs.toInt * (-1) = -sum_abs.toInt := by
      show sum_abs.toInt * (-1) = -sum_abs.toInt
      rw [Int.mul_neg, Int.mul_one]
    rw [h_eq] at hov
    rcases hov with hp | hn <;> omega

/-! ## Failure / None clause. -/

theorem empty_returns_none
    (arr : RustSlice i64) (hempty : arr.val.size = 0) :
    clever_127_prod_signs.prod_signs arr
      = RustM.ok core_models.option.Option.None := by
  unfold clever_127_prod_signs.prod_signs
  have h_size_lt : arr.val.size < USize64.size := arr.size_lt_usizeSize
  have h_ofNat_toNat : (USize64.ofNat arr.val.size).toNat = arr.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_zero_eq : USize64.ofNat arr.val.size = (0 : usize) := by
    apply USize64.toNat_inj.mp
    rw [h_ofNat_toNat, hempty]; rfl
  have h_dec : decide (USize64.ofNat arr.val.size = (0 : usize)) = true := by
    rw [decide_eq_true_iff]; exact h_zero_eq
  show (do
    let __do_lift ← (core_models.slice.Impl.is_empty i64 arr : RustM Bool)
    if __do_lift = true then pure core_models.option.Option.None
    else _) = RustM.ok core_models.option.Option.None
  unfold core_models.slice.Impl.is_empty core_models.slice.Impl.len
    rust_primitives.slice.slice_length
  show (do
    let __do_lift ← (do
      let __do_lift1 ← (pure (USize64.ofNat arr.val.size) : RustM usize)
      (__do_lift1 ==? (0 : usize) : RustM Bool))
    if __do_lift = true then pure core_models.option.Option.None
    else _) = RustM.ok core_models.option.Option.None
  simp only [pure_bind]
  show (do
    let __do_lift ← (pure (decide (USize64.ofNat arr.val.size = (0 : usize))) : RustM Bool)
    if __do_lift = true then pure core_models.option.Option.None
    else _) = RustM.ok core_models.option.Option.None
  rw [h_dec]
  simp only [pure_bind, ↓reduceIte]
  rfl

/-! ## Step lemmas for `run_at`. -/

private theorem run_at_oob (arr : RustSlice i64) (i : usize)
    (sum_abs sign : i64)
    (hi : arr.val.size ≤ i.toNat) :
    clever_127_prod_signs.run_at arr i sum_abs sign =
      (sum_abs *? sign : RustM i64) := by
  conv => lhs; unfold clever_127_prod_signs.run_at
  have h_ofNat : (USize64.ofNat arr.val.size).toNat = arr.val.size :=
    USize64.toNat_ofNat_of_lt' arr.size_lt_usizeSize
  have h_le : USize64.ofNat arr.val.size ≤ i := by
    rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  have h_ge : i ≥ USize64.ofNat arr.val.size := h_le
  have h_cond : decide (i ≥ USize64.ofNat arr.val.size) = true :=
    decide_eq_true h_ge
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]

private theorem run_at_in_range_cond_false (arr : RustSlice i64) (i : usize)
    (hi : i.toNat < arr.val.size) :
    decide (i ≥ USize64.ofNat arr.val.size) = false := by
  have h_ofNat : (USize64.ofNat arr.val.size).toNat = arr.val.size :=
    USize64.toNat_ofNat_of_lt' arr.size_lt_usizeSize
  rw [decide_eq_false_iff_not]
  intro h_ge
  have h_le : USize64.ofNat arr.val.size ≤ i := h_ge
  rw [USize64.le_iff_toNat_le, h_ofNat] at h_le
  omega

/-- Recursion step for v < 0 branch: av = -v, s = -1. -/
private theorem run_at_recurse_neg
    (arr : RustSlice i64) (i : usize) (sum_abs sign : i64)
    (hi : i.toNat < arr.val.size)
    (h_v_neg : (arr.val[i.toNat]'hi).toInt < 0)
    (h_v_not_min : (arr.val[i.toNat]'hi) ≠ Int64.minValue)
    (h_no_ov_i : i.toNat + 1 < 2^64)
    (h_no_add : ¬ Int64.addOverflow sum_abs (-(arr.val[i.toNat]'hi)))
    (h_no_mul : ¬ Int64.mulOverflow sign (-1 : i64)) :
    clever_127_prod_signs.run_at arr i sum_abs sign =
      clever_127_prod_signs.run_at arr (i + 1)
        (sum_abs + (-(arr.val[i.toNat]'hi))) (sign * (-1 : i64)) := by
  conv => lhs; unfold clever_127_prod_signs.run_at
  have h_cond := run_at_in_range_cond_false arr i hi
  have h_idx := slice_index_eq arr i hi
  have h_v_lt_zero : (arr.val[i.toNat]'hi) < (0 : i64) := by
    apply Int64.lt_iff_toInt_lt.mpr
    rw [i64_zero_toInt]; exact h_v_neg
  have h_dec_lt : decide ((arr.val[i.toNat]'hi) < (0 : i64)) = true :=
    decide_eq_true h_v_lt_zero
  have h_v_ne_zero : ¬ ((arr.val[i.toNat]'hi) = (0 : i64)) := by
    intro h_eq
    have : (arr.val[i.toNat]'hi).toInt = (0 : i64).toInt := by rw [h_eq]
    rw [i64_zero_toInt] at this; omega
  have h_dec_eq : decide ((arr.val[i.toNat]'hi) = (0 : i64)) = false :=
    decide_eq_false h_v_ne_zero
  have h_v_not_gt : ¬ ((arr.val[i.toNat]'hi) > (0 : i64)) := by
    intro h_gt
    have : (0 : i64).toInt < (arr.val[i.toNat]'hi).toInt :=
      Int64.lt_iff_toInt_lt.mp h_gt
    rw [i64_zero_toInt] at this; omega
  have h_dec_gt : decide ((arr.val[i.toNat]'hi) > (0 : i64)) = false :=
    decide_eq_false h_v_not_gt
  have h_neg_eq : (-? (arr.val[i.toNat]'hi) : RustM i64) =
      RustM.ok (-(arr.val[i.toNat]'hi)) := i64_neg_eq _ h_v_not_min
  have h_iplus : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
    usize_add_one_eq i h_no_ov_i
  have h_sum_plus : (sum_abs +? (-(arr.val[i.toNat]'hi)) : RustM i64) =
      RustM.ok (sum_abs + (-(arr.val[i.toNat]'hi))) :=
    i64_add_eq sum_abs _ h_no_add
  have h_sign_mul : (sign *? (-1 : i64) : RustM i64) =
      RustM.ok (sign * (-1 : i64)) := i64_mul_eq sign _ h_no_mul
  have h_lt_eq : (rust_primitives.cmp.lt (arr.val[i.toNat]'hi) (0 : i64) : RustM Bool) =
      pure (decide ((arr.val[i.toNat]'hi) < (0 : i64))) := rfl
  have h_eq_eq : (rust_primitives.cmp.eq (arr.val[i.toNat]'hi) (0 : i64) : RustM Bool) =
      pure (decide ((arr.val[i.toNat]'hi) = (0 : i64))) := rfl
  have h_gt_eq : (rust_primitives.cmp.gt (arr.val[i.toNat]'hi) (0 : i64) : RustM Bool) =
      pure (decide ((arr.val[i.toNat]'hi) > (0 : i64))) := rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_lt_eq, h_eq_eq, h_gt_eq,
             h_dec_lt, h_dec_eq, h_dec_gt,
             h_neg_eq, h_iplus, h_sum_plus, h_sign_mul]

/-- Recursion step for v = 0 branch: av = v = 0, s = 0. -/
private theorem run_at_recurse_zero
    (arr : RustSlice i64) (i : usize) (sum_abs sign : i64)
    (hi : i.toNat < arr.val.size)
    (h_v_eq : (arr.val[i.toNat]'hi) = (0 : i64))
    (h_no_ov_i : i.toNat + 1 < 2^64)
    (h_no_add : ¬ Int64.addOverflow sum_abs (arr.val[i.toNat]'hi))
    (h_no_mul : ¬ Int64.mulOverflow sign (0 : i64)) :
    clever_127_prod_signs.run_at arr i sum_abs sign =
      clever_127_prod_signs.run_at arr (i + 1)
        (sum_abs + (arr.val[i.toNat]'hi)) (sign * (0 : i64)) := by
  conv => lhs; unfold clever_127_prod_signs.run_at
  have h_cond := run_at_in_range_cond_false arr i hi
  have h_idx := slice_index_eq arr i hi
  have h_v_not_lt : ¬ ((arr.val[i.toNat]'hi) < (0 : i64)) := by
    intro h_lt
    have : (arr.val[i.toNat]'hi).toInt < (0 : i64).toInt :=
      Int64.lt_iff_toInt_lt.mp h_lt
    rw [i64_zero_toInt, h_v_eq, i64_zero_toInt] at this; omega
  have h_dec_lt : decide ((arr.val[i.toNat]'hi) < (0 : i64)) = false :=
    decide_eq_false h_v_not_lt
  have h_dec_eq : decide ((arr.val[i.toNat]'hi) = (0 : i64)) = true :=
    decide_eq_true h_v_eq
  have h_iplus : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
    usize_add_one_eq i h_no_ov_i
  have h_sum_plus : (sum_abs +? (arr.val[i.toNat]'hi) : RustM i64) =
      RustM.ok (sum_abs + (arr.val[i.toNat]'hi)) :=
    i64_add_eq sum_abs _ h_no_add
  have h_sign_mul : (sign *? (0 : i64) : RustM i64) =
      RustM.ok (sign * (0 : i64)) := i64_mul_eq sign _ h_no_mul
  have h_lt_eq : (rust_primitives.cmp.lt (arr.val[i.toNat]'hi) (0 : i64) : RustM Bool) =
      pure (decide ((arr.val[i.toNat]'hi) < (0 : i64))) := rfl
  have h_eq_eq : (rust_primitives.cmp.eq (arr.val[i.toNat]'hi) (0 : i64) : RustM Bool) =
      pure (decide ((arr.val[i.toNat]'hi) = (0 : i64))) := rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_lt_eq, h_eq_eq,
             h_dec_lt, h_dec_eq,
             h_iplus, h_sum_plus, h_sign_mul]

/-- Recursion step for v > 0 branch: av = v, s = 1. -/
private theorem run_at_recurse_pos
    (arr : RustSlice i64) (i : usize) (sum_abs sign : i64)
    (hi : i.toNat < arr.val.size)
    (h_v_pos : (0 : Int) < (arr.val[i.toNat]'hi).toInt)
    (h_no_ov_i : i.toNat + 1 < 2^64)
    (h_no_add : ¬ Int64.addOverflow sum_abs (arr.val[i.toNat]'hi))
    (h_no_mul : ¬ Int64.mulOverflow sign (1 : i64)) :
    clever_127_prod_signs.run_at arr i sum_abs sign =
      clever_127_prod_signs.run_at arr (i + 1)
        (sum_abs + (arr.val[i.toNat]'hi)) (sign * (1 : i64)) := by
  conv => lhs; unfold clever_127_prod_signs.run_at
  have h_cond := run_at_in_range_cond_false arr i hi
  have h_idx := slice_index_eq arr i hi
  have h_v_not_lt : ¬ ((arr.val[i.toNat]'hi) < (0 : i64)) := by
    intro h_lt
    have : (arr.val[i.toNat]'hi).toInt < (0 : i64).toInt :=
      Int64.lt_iff_toInt_lt.mp h_lt
    rw [i64_zero_toInt] at this; omega
  have h_dec_lt : decide ((arr.val[i.toNat]'hi) < (0 : i64)) = false :=
    decide_eq_false h_v_not_lt
  have h_v_ne_zero : ¬ ((arr.val[i.toNat]'hi) = (0 : i64)) := by
    intro h_eq
    have : (arr.val[i.toNat]'hi).toInt = (0 : i64).toInt := by rw [h_eq]
    rw [i64_zero_toInt] at this; omega
  have h_dec_eq : decide ((arr.val[i.toNat]'hi) = (0 : i64)) = false :=
    decide_eq_false h_v_ne_zero
  have h_v_gt : (arr.val[i.toNat]'hi) > (0 : i64) := by
    apply Int64.lt_iff_toInt_lt.mpr
    rw [i64_zero_toInt]; exact h_v_pos
  have h_dec_gt : decide ((arr.val[i.toNat]'hi) > (0 : i64)) = true :=
    decide_eq_true h_v_gt
  have h_iplus : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
    usize_add_one_eq i h_no_ov_i
  have h_sum_plus : (sum_abs +? (arr.val[i.toNat]'hi) : RustM i64) =
      RustM.ok (sum_abs + (arr.val[i.toNat]'hi)) :=
    i64_add_eq sum_abs _ h_no_add
  have h_sign_mul : (sign *? (1 : i64) : RustM i64) =
      RustM.ok (sign * (1 : i64)) := i64_mul_eq sign _ h_no_mul
  have h_lt_eq : (rust_primitives.cmp.lt (arr.val[i.toNat]'hi) (0 : i64) : RustM Bool) =
      pure (decide ((arr.val[i.toNat]'hi) < (0 : i64))) := rfl
  have h_eq_eq : (rust_primitives.cmp.eq (arr.val[i.toNat]'hi) (0 : i64) : RustM Bool) =
      pure (decide ((arr.val[i.toNat]'hi) = (0 : i64))) := rfl
  have h_gt_eq : (rust_primitives.cmp.gt (arr.val[i.toNat]'hi) (0 : i64) : RustM Bool) =
      pure (decide ((arr.val[i.toNat]'hi) > (0 : i64))) := rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_lt_eq, h_eq_eq, h_gt_eq,
             h_dec_lt, h_dec_eq, h_dec_gt,
             h_iplus, h_sum_plus, h_sign_mul]

/-! ## OOB handler (used for both `m = 0` and `m+1` OOB cases). -/

/-- At OOB: given the running invariants, `run_at` returns
    `RustM.ok (sum_abs * sign)` with the desired `toInt`. -/
private theorem run_at_at_size_ok (arr : RustSlice i64) (i : usize)
    (sum_abs sign : i64)
    (hfit_size : sum_abs_int arr arr.val.size < 2^63)
    (hi_eq : i.toNat = arr.val.size)
    (hinv_s : sum_abs.toInt = sum_abs_int arr i.toNat)
    (hinv_p : sign.toInt = sign_product_int arr i.toNat) :
    ∃ r : i64,
      clever_127_prod_signs.run_at arr i sum_abs sign = RustM.ok r ∧
      r.toInt = sum_abs_int arr arr.val.size *
                sign_product_int arr arr.val.size := by
  have h_sum_inv : sum_abs.toInt = sum_abs_int arr arr.val.size := by
    rw [hinv_s, hi_eq]
  have h_sign_inv : sign.toInt = sign_product_int arr arr.val.size := by
    rw [hinv_p, hi_eq]
  have h_sum_nneg : 0 ≤ sum_abs.toInt := by
    rw [h_sum_inv]; exact sum_abs_int_nonneg arr arr.val.size
  have h_sum_lt : sum_abs.toInt < 2^63 := by rw [h_sum_inv]; exact hfit_size
  have h_sign_set : sign.toInt = 0 ∨ sign.toInt = 1 ∨ sign.toInt = -1 := by
    rw [h_sign_inv]; exact sign_product_int_in_set arr arr.val.size
  have hi_ge : arr.val.size ≤ i.toNat := by omega
  have h_no_mul : ¬ Int64.mulOverflow sum_abs sign :=
    no_mul_overflow_of_sign_bounded sum_abs sign h_sum_nneg h_sum_lt h_sign_set
  refine ⟨sum_abs * sign, ?_, ?_⟩
  · rw [run_at_oob arr i sum_abs sign hi_ge]
    exact i64_mul_eq sum_abs sign h_no_mul
  · rw [Int64.toInt_mul_of_not_mulOverflow h_no_mul, h_sum_inv, h_sign_inv]

/-! ## Main contract: strong induction lemma. -/

/-- Helper for the no-mul-overflow check of `sign * s` when BOTH factors
    are in `{-1, 0, 1}`: the product is in `{-1, 0, 1}`, never overflows.
    (Only requiring `s ∈ {-1,0,1}` is unsound: `sign = -2^63, s = -1` would
    overflow.) -/
private theorem no_mul_overflow_sign_unit (sign : i64) (s : i64)
    (h_sign : sign.toInt = 0 ∨ sign.toInt = 1 ∨ sign.toInt = -1)
    (h_s : s.toInt = 0 ∨ s.toInt = 1 ∨ s.toInt = -1) :
    ¬ Int64.mulOverflow sign s := by
  intro hov
  rw [Int64.mulOverflow_iff] at hov
  simp only [h63_eq] at hov
  rcases h_sign with hsi | hsi | hsi <;> rcases h_s with hsj | hsj | hsj <;>
    rw [hsi, hsj] at hov <;> rcases hov with hp | hn <;> omega

private theorem run_at_correct (arr : RustSlice i64)
    (hno_min : ∀ (k : Nat) (h : k < arr.val.size),
                  (arr.val[k]'h) ≠ Int64.minValue)
    (hfit : ∀ k : Nat, k ≤ arr.val.size →
                  sum_abs_int arr k < 2^63) :
    ∀ (m : Nat) (i : usize) (sum_abs sign : i64),
      arr.val.size - i.toNat ≤ m →
      i.toNat ≤ arr.val.size →
      sum_abs.toInt = sum_abs_int arr i.toNat →
      sign.toInt = sign_product_int arr i.toNat →
      ∃ r : i64,
        clever_127_prod_signs.run_at arr i sum_abs sign = RustM.ok r ∧
        r.toInt = sum_abs_int arr arr.val.size *
                  sign_product_int arr arr.val.size := by
  intro m
  induction m with
  | zero =>
    intro i sum_abs sign hm hi_le hinv_s hinv_p
    have hi_eq : i.toNat = arr.val.size := by omega
    exact run_at_at_size_ok arr i sum_abs sign (hfit arr.val.size (Nat.le_refl _))
      hi_eq hinv_s hinv_p
  | succ m ih =>
    intro i sum_abs sign hm hi_le hinv_s hinv_p
    by_cases hi_ge : arr.val.size ≤ i.toNat
    · have hi_eq : i.toNat = arr.val.size := by omega
      exact run_at_at_size_ok arr i sum_abs sign (hfit arr.val.size (Nat.le_refl _))
        hi_eq hinv_s hinv_p
    · have hi_lt : i.toNat < arr.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : arr.val.size < USize64.size := arr.size_lt_usizeSize
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        have : USize64.size = 2^64 := usize_size_eq
        omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ arr.val.size := by rw [h_i1]; omega
      have h_m_le : arr.val.size - (i + 1).toNat ≤ m := by rw [h_i1]; omega
      let v := arr.val[i.toNat]'hi_lt
      have h_v_not_min : v ≠ Int64.minValue := hno_min i.toNat hi_lt
      have h_sum_succ :
          sum_abs_int arr (i.toNat + 1) =
            sum_abs_int arr i.toNat + (v.toInt.natAbs : Int) :=
        sum_abs_int_succ arr i.toNat hi_lt
      have h_sign_succ :
          sign_product_int arr (i.toNat + 1) =
            sign_product_int arr i.toNat * sgn_int v.toInt :=
        sign_product_int_succ arr i.toNat hi_lt
      have h_i1_le_nat : i.toNat + 1 ≤ arr.val.size := by rw [← h_i1]; exact h_i1_le
      have h_fit_succ := hfit (i.toNat + 1) h_i1_le_nat
      have h_sum_nneg : 0 ≤ sum_abs.toInt := by
        rw [hinv_s]; exact sum_abs_int_nonneg arr i.toNat
      have h_sum_curr_lt : sum_abs.toInt < 2^63 := by
        rw [hinv_s]; exact hfit i.toNat (Nat.le_of_lt hi_lt)
      have h_sign_set : sign.toInt = 0 ∨ sign.toInt = 1 ∨ sign.toInt = -1 := by
        rw [hinv_p]; exact sign_product_int_in_set arr i.toNat
      by_cases h_v_zero : v.toInt = 0
      · -- v = 0 case.
        have h_v_eq : v = (0 : i64) := by
          have h_t : v.toInt = (0 : i64).toInt := by rw [h_v_zero, i64_zero_toInt]
          exact Int64.toInt_inj.mp h_t
        have h_sgn_zero : sgn_int v.toInt = 0 := by
          unfold sgn_int; rw [if_pos h_v_zero]
        have h_natAbs_zero : (v.toInt.natAbs : Int) = 0 := by
          rw [h_v_zero]; rfl
        have h_no_add : ¬ Int64.addOverflow sum_abs v := by
          intro hov
          rw [Int64.addOverflow_iff, h_v_eq, i64_zero_toInt] at hov
          simp only [h63_eq] at hov
          rcases hov with hp | hn <;> omega
        have h_no_mul : ¬ Int64.mulOverflow sign (0 : i64) :=
          no_mul_overflow_sign_unit sign 0 h_sign_set (Or.inl i64_zero_toInt)
        have h_step :=
          run_at_recurse_zero arr i sum_abs sign hi_lt h_v_eq h_no_ov_i h_no_add h_no_mul
        have h_new_sum_inv : (sum_abs + v).toInt = sum_abs_int arr (i + 1).toNat := by
          rw [Int64.toInt_add_of_not_addOverflow h_no_add, hinv_s, h_v_eq, i64_zero_toInt]
          rw [h_i1, h_sum_succ, h_natAbs_zero]
        have h_new_sign_inv : (sign * (0 : i64)).toInt = sign_product_int arr (i + 1).toNat := by
          rw [Int64.toInt_mul_of_not_mulOverflow h_no_mul, i64_zero_toInt]
          rw [h_i1, h_sign_succ, h_sgn_zero, hinv_p]
        obtain ⟨r, h_rec_eq, h_r_int⟩ :=
          ih (i + 1) (sum_abs + v) (sign * (0 : i64))
            h_m_le h_i1_le h_new_sum_inv h_new_sign_inv
        refine ⟨r, ?_, h_r_int⟩
        rw [h_step]; exact h_rec_eq
      · by_cases h_v_pos : 0 < v.toInt
        · -- v > 0.
          have h_sgn_one : sgn_int v.toInt = 1 := by
            unfold sgn_int; rw [if_neg h_v_zero, if_pos h_v_pos]
          have h_natAbs_eq : (v.toInt.natAbs : Int) = v.toInt :=
            Int.natAbs_of_nonneg (Int.le_of_lt h_v_pos)
          have h_no_add : ¬ Int64.addOverflow sum_abs v := by
            intro hov
            rw [Int64.addOverflow_iff] at hov
            simp only [h63_eq] at hov
            have h_sum_eq :
                sum_abs.toInt + v.toInt = sum_abs_int arr (i.toNat + 1) := by
              rw [hinv_s, h_sum_succ, h_natAbs_eq]
            rcases hov with hov_pos | hov_neg
            · rw [h_sum_eq] at hov_pos; omega
            · rw [h_sum_eq] at hov_neg
              have h_succ_nneg := sum_abs_int_nonneg arr (i.toNat + 1)
              omega
          have h_no_mul : ¬ Int64.mulOverflow sign (1 : i64) :=
            no_mul_overflow_sign_unit sign 1 h_sign_set (Or.inr (Or.inl i64_one_toInt))
          have h_step :=
            run_at_recurse_pos arr i sum_abs sign hi_lt h_v_pos h_no_ov_i h_no_add h_no_mul
          have h_new_sum_inv : (sum_abs + v).toInt = sum_abs_int arr (i + 1).toNat := by
            rw [Int64.toInt_add_of_not_addOverflow h_no_add, hinv_s]
            rw [h_i1, h_sum_succ, h_natAbs_eq]
          have h_new_sign_inv : (sign * (1 : i64)).toInt = sign_product_int arr (i + 1).toNat := by
            rw [Int64.toInt_mul_of_not_mulOverflow h_no_mul, i64_one_toInt]
            rw [h_i1, h_sign_succ, h_sgn_one, hinv_p]
          obtain ⟨r, h_rec_eq, h_r_int⟩ :=
            ih (i + 1) (sum_abs + v) (sign * (1 : i64))
              h_m_le h_i1_le h_new_sum_inv h_new_sign_inv
          refine ⟨r, ?_, h_r_int⟩
          rw [h_step]; exact h_rec_eq
        · -- v < 0.
          have h_v_neg : v.toInt < 0 := by
            have h_le : v.toInt ≤ 0 := Int.not_lt.mp h_v_pos
            omega
          have h_sgn_neg : sgn_int v.toInt = -1 := by
            unfold sgn_int; rw [if_neg h_v_zero, if_neg h_v_pos]
          have h_natAbs_eq : (v.toInt.natAbs : Int) = -v.toInt := by
            have h_le : v.toInt ≤ 0 := Int.le_of_lt h_v_neg
            have := Int.eq_neg_natAbs_of_nonpos h_le
            omega
          have h_negv_toInt : (-v).toInt = -v.toInt :=
            Int64.toInt_neg_of_ne_intMin h_v_not_min
          have h_no_add : ¬ Int64.addOverflow sum_abs (-v) := by
            intro hov
            rw [Int64.addOverflow_iff, h_negv_toInt] at hov
            simp only [h63_eq] at hov
            have h_sum_eq :
                sum_abs.toInt + (-v.toInt) = sum_abs_int arr (i.toNat + 1) := by
              rw [hinv_s, h_sum_succ, h_natAbs_eq]
            rcases hov with hov_pos | hov_neg
            · rw [h_sum_eq] at hov_pos; omega
            · rw [h_sum_eq] at hov_neg
              have h_succ_nneg := sum_abs_int_nonneg arr (i.toNat + 1)
              omega
          have h_no_mul : ¬ Int64.mulOverflow sign (-1 : i64) :=
            no_mul_overflow_sign_unit sign (-1) h_sign_set (Or.inr (Or.inr i64_neg_one_toInt))
          have h_step :=
            run_at_recurse_neg arr i sum_abs sign hi_lt h_v_neg h_v_not_min h_no_ov_i h_no_add h_no_mul
          have h_new_sum_inv : (sum_abs + (-v)).toInt = sum_abs_int arr (i + 1).toNat := by
            rw [Int64.toInt_add_of_not_addOverflow h_no_add, hinv_s, h_negv_toInt]
            rw [h_i1, h_sum_succ, h_natAbs_eq]
          have h_new_sign_inv : (sign * (-1 : i64)).toInt = sign_product_int arr (i + 1).toNat := by
            rw [Int64.toInt_mul_of_not_mulOverflow h_no_mul, i64_neg_one_toInt]
            rw [h_i1, h_sign_succ, h_sgn_neg, hinv_p]
          obtain ⟨r, h_rec_eq, h_r_int⟩ :=
            ih (i + 1) (sum_abs + (-v)) (sign * (-1 : i64))
              h_m_le h_i1_le h_new_sum_inv h_new_sign_inv
          refine ⟨r, ?_, h_r_int⟩
          rw [h_step]; exact h_rec_eq

theorem matches_spec_formula
    (arr : RustSlice i64)
    (hne : 0 < arr.val.size)
    (hno_min : ∀ (k : Nat) (h : k < arr.val.size),
                  (arr.val[k]'h) ≠ Int64.minValue)
    (hfit : ∀ k : Nat, k ≤ arr.val.size →
                  sum_abs_int arr k < 2^63) :
    ∃ r : i64,
      clever_127_prod_signs.prod_signs arr
        = RustM.ok (core_models.option.Option.Some r) ∧
      r.toInt = sum_abs_int arr arr.val.size *
                sign_product_int arr arr.val.size := by
  unfold clever_127_prod_signs.prod_signs
  have h_size_lt : arr.val.size < USize64.size := arr.size_lt_usizeSize
  have h_ofNat_toNat : (USize64.ofNat arr.val.size).toNat = arr.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_zero_ne : USize64.ofNat arr.val.size ≠ (0 : usize) := by
    intro h_eq
    have h_t : (USize64.ofNat arr.val.size).toNat = (0 : usize).toNat := by rw [h_eq]
    rw [h_ofNat_toNat] at h_t
    have : arr.val.size = 0 := h_t
    omega
  have h_dec : decide (USize64.ofNat arr.val.size = (0 : usize)) = false :=
    decide_eq_false h_zero_ne
  have h_is_empty :
      (core_models.slice.Impl.is_empty i64 arr : RustM Bool) = pure false := by
    show (do
      let __do_lift ← (core_models.slice.Impl.len i64 arr : RustM usize)
      (__do_lift ==? (0 : usize) : RustM Bool)) = pure false
    unfold core_models.slice.Impl.len rust_primitives.slice.slice_length
    simp only [pure_bind]
    show (rust_primitives.cmp.eq (USize64.ofNat arr.val.size) (0 : usize) : RustM Bool) =
          pure false
    show (pure (decide (USize64.ofNat arr.val.size = (0 : usize))) : RustM Bool) = pure false
    rw [h_dec]
  rw [h_is_empty]
  simp only [pure_bind, Bool.false_eq_true, ↓reduceIte]
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_inv_s : (0 : i64).toInt = sum_abs_int arr (0 : usize).toNat := by
    rw [h_zero_toNat, i64_zero_toInt]; rfl
  have h_inv_p : (1 : i64).toInt = sign_product_int arr (0 : usize).toNat := by
    rw [h_zero_toNat, i64_one_toInt]; rfl
  have h_m_le : arr.val.size - (0 : usize).toNat ≤ arr.val.size := by
    rw [h_zero_toNat]; omega
  have h_i_le : (0 : usize).toNat ≤ arr.val.size := by
    rw [h_zero_toNat]; omega
  obtain ⟨r, h_rec_eq, h_r_int⟩ :=
    run_at_correct arr hno_min hfit arr.val.size (0 : usize) (0 : i64) (1 : i64)
      h_m_le h_i_le h_inv_s h_inv_p
  refine ⟨r, ?_, h_r_int⟩
  rw [h_rec_eq]
  rfl

end Clever_127_prod_signsObligations
