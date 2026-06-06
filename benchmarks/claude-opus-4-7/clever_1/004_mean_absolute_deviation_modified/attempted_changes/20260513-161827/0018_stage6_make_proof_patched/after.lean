-- Companion obligations file for the `clever_004_mean_absolute_deviation` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_004_mean_absolute_deviation

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_004_mean_absolute_deviationObligations

/-! ## Reusable helpers (lifted from the references). -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide

private theorem RustM_bind_ok_iff {α β : Type} (x : RustM α) (f : α → RustM β) (b : β) :
    (x >>= f) = RustM.ok b ↔ ∃ a, x = RustM.ok a ∧ f a = RustM.ok b := by
  constructor
  · intro h
    cases hx : x with
    | none =>
      exfalso; rw [hx] at h; cases h
    | some r =>
      cases r with
      | error e =>
        exfalso; rw [hx] at h; cases h
      | ok v =>
        refine ⟨v, rfl, ?_⟩
        rw [hx] at h; exact h
  · rintro ⟨a, hx, hfa⟩
    rw [hx]
    show f a = RustM.ok b
    exact hfa

private theorem i64_sub_extract (a b y : i64)
    (hsub : (a -? b : RustM i64) = RustM.ok y) :
    BitVec.ssubOverflow a.toBitVec b.toBitVec = false ∧ y = a - b := by
  have h_unfold : (a -? b : RustM i64) =
      (if BitVec.ssubOverflow a.toBitVec b.toBitVec then
        (.fail .integerOverflow : RustM i64)
       else pure (a - b)) := rfl
  cases hbv : BitVec.ssubOverflow a.toBitVec b.toBitVec with
  | true =>
    exfalso
    have h_fail : (a -? b : RustM i64) = .fail .integerOverflow := by
      rw [h_unfold, hbv]; rfl
    rw [h_fail] at hsub
    cases hsub
  | false =>
    refine ⟨rfl, ?_⟩
    have h_pure : (a -? b : RustM i64) = pure (a - b) := by
      rw [h_unfold, hbv]; rfl
    rw [h_pure] at hsub
    injection hsub with h1
    injection h1 with h2
    exact h2.symm

private theorem i64_add_extract (a b y : i64)
    (hadd : (a +? b : RustM i64) = RustM.ok y) :
    BitVec.saddOverflow a.toBitVec b.toBitVec = false ∧ y = a + b := by
  have h_unfold : (a +? b : RustM i64) =
      (if BitVec.saddOverflow a.toBitVec b.toBitVec then
        (.fail .integerOverflow : RustM i64)
       else pure (a + b)) := rfl
  cases hbv : BitVec.saddOverflow a.toBitVec b.toBitVec with
  | true =>
    exfalso
    have h_fail : (a +? b : RustM i64) = .fail .integerOverflow := by
      rw [h_unfold, hbv]; rfl
    rw [h_fail] at hadd
    cases hadd
  | false =>
    refine ⟨rfl, ?_⟩
    have h_pure : (a +? b : RustM i64) = pure (a + b) := by
      rw [h_unfold, hbv]; rfl
    rw [h_pure] at hadd
    injection hadd with h1
    injection h1 with h2
    exact h2.symm

private theorem i64_neg_extract (a y : i64)
    (hneg : (-? a : RustM i64) = RustM.ok y) :
    a ≠ Int64.minValue ∧ y = -a := by
  have h_unfold : (-? a : RustM i64) =
      (if a = Int64.minValue then
        (.fail .integerOverflow : RustM i64)
       else pure (-a)) := rfl
  by_cases hmin : a = Int64.minValue
  · exfalso
    have h_fail : (-? a : RustM i64) = .fail .integerOverflow := by
      rw [h_unfold, if_pos hmin]
    rw [h_fail] at hneg
    cases hneg
  · refine ⟨hmin, ?_⟩
    have h_pure : (-? a : RustM i64) = pure (-a) := by
      rw [h_unfold, if_neg hmin]
    rw [h_pure] at hneg
    injection hneg with h1
    injection h1 with h2
    exact h2.symm

/-! ## Integer-valued tail-sum specification

To state functional correctness independently of the recursive
implementation, we define the mean-absolute-deviation computation in `Int`
so the spec itself cannot overflow on any input the function under
verification can legally accept. The defining shape mirrors the iterative
`reference_mad` in the Rust source's `tests` module. -/

/-- Integer-valued tail sum: `slice_tail_sum_int s i = Σ_{j ≥ i} (s.val[j]).toInt`. -/
private def slice_tail_sum_int (s : RustSlice i64) (i : Nat) : Int :=
  if h : i < s.val.size then (s.val[i]'h).toInt + slice_tail_sum_int s (i + 1) else 0
termination_by s.val.size - i

/-- Integer-valued tail sum of absolute deviations from a chosen mean. -/
private def slice_tail_abs_dev_sum_int (s : RustSlice i64) (mean : Int) (i : Nat) : Int :=
  if h : i < s.val.size then
    (((s.val[i]'h).toInt - mean).natAbs : Int) + slice_tail_abs_dev_sum_int s mean (i + 1)
  else 0
termination_by s.val.size - i

/-- Total slice sum: starts at index 0. -/
private def slice_sum_int (s : RustSlice i64) : Int := slice_tail_sum_int s 0

/-- Total absolute-deviation sum: starts at index 0. -/
private def slice_abs_dev_sum_int (s : RustSlice i64) (mean : Int) : Int :=
  slice_tail_abs_dev_sum_int s mean 0

/-- Integer-valued MAD: matches the Rust `reference_mad` exactly,
    including the `as i64` cast on `len()`. We use the cast's `Int` value
    `(USize64.toInt64 (USize64.ofNat s.val.size)).toInt` as the divisor,
    and `Int.tdiv` (truncating toward zero), which matches Rust's `/`
    on `i64`. For typical inputs (`size < 2^63`) this divisor equals
    `(s.val.size : Int)` and `tdiv` equals `/`, so the spec matches the
    mathematical mean absolute deviation. -/
private def mad_int (s : RustSlice i64) : Int :=
  let n : Int := (USize64.toInt64 (USize64.ofNat s.val.size)).toInt
  if n = 0 then 0
  else
    let mean := (slice_sum_int s).tdiv n
    (slice_abs_dev_sum_int s mean).tdiv n

/-! ## Unfolding lemmas for tail sums -/

private theorem slice_tail_sum_int_oob (s : RustSlice i64) (i : Nat)
    (h : s.val.size ≤ i) :
    slice_tail_sum_int s i = 0 := by
  unfold slice_tail_sum_int
  rw [dif_neg (by omega)]

private theorem slice_tail_sum_int_step (s : RustSlice i64) (i : Nat)
    (h : i < s.val.size) :
    slice_tail_sum_int s i = (s.val[i]'h).toInt + slice_tail_sum_int s (i + 1) := by
  conv => lhs; unfold slice_tail_sum_int
  rw [dif_pos h]

private theorem slice_tail_abs_dev_sum_int_oob (s : RustSlice i64) (mean : Int) (i : Nat)
    (h : s.val.size ≤ i) :
    slice_tail_abs_dev_sum_int s mean i = 0 := by
  unfold slice_tail_abs_dev_sum_int
  rw [dif_neg (by omega)]

private theorem slice_tail_abs_dev_sum_int_step (s : RustSlice i64) (mean : Int) (i : Nat)
    (h : i < s.val.size) :
    slice_tail_abs_dev_sum_int s mean i =
      (((s.val[i]'h).toInt - mean).natAbs : Int) + slice_tail_abs_dev_sum_int s mean (i + 1) := by
  conv => lhs; unfold slice_tail_abs_dev_sum_int
  rw [dif_pos h]

/-! ## Step lemmas for the recursive `sum_from` -/

private theorem sum_from_oob (numbers : RustSlice i64) (i : usize)
    (hi : numbers.val.size ≤ i.toNat) :
    clever_004_mean_absolute_deviation.sum_from numbers i = RustM.ok 0 := by
  conv => lhs; unfold clever_004_mean_absolute_deviation.sum_from
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' numbers.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat numbers.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

private theorem sum_from_recurse_extract
    (numbers : RustSlice i64) (i : usize) (v : i64)
    (hi : i.toNat < numbers.val.size)
    (hat : clever_004_mean_absolute_deviation.sum_from numbers i = RustM.ok v) :
    ∃ (rec : i64) (i' : usize),
      i'.toNat = i.toNat + 1 ∧
      clever_004_mean_absolute_deviation.sum_from numbers i' = RustM.ok rec ∧
      v.toInt = (numbers.val[i.toNat]'hi).toInt + rec.toInt := by
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' numbers.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat numbers.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (numbers[i]_? : RustM i64) = RustM.ok (numbers.val[i.toNat]'hi) := by
    show (if h : i.toNat < numbers.val.size then pure (numbers.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (numbers.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  conv at hat => lhs; unfold clever_004_mean_absolute_deviation.sum_from
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx] at hat
  -- After the simp, `hat` decomposes as
  --   ((i +? 1) >>= λ i' => sum_from numbers i' >>= λ rec => val[i] +? rec) = ok v
  obtain ⟨i', h_i'_eq, hat⟩ := (RustM_bind_ok_iff _ _ _).mp hat
  have h_size_lt : numbers.val.size < 2^64 := numbers.size_lt_usizeSize
  have h_no_overflow_i : i.toNat + 1 < 2^64 := by omega
  have h_no_bv_i : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hi' := (USize64.uaddOverflow_iff i 1).mp hbo
      rw [usize_one_toNat] at hi'
      omega
  have h_i_add_pure : (i +? (1 : usize) : RustM usize) = pure (i + 1) := by
    show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = pure (i + 1)
    show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
            then (.fail .integerOverflow : RustM usize)
            else pure (i + 1)) = _
    rw [h_no_bv_i]; rfl
  rw [h_i_add_pure] at h_i'_eq
  have h_i'_pure : i' = i + 1 := by
    have h_ok : (pure (i + 1) : RustM usize) = RustM.ok (i + 1) := rfl
    rw [h_ok] at h_i'_eq
    injection h_i'_eq with h1
    injection h1 with h2
    exact h2.symm
  subst h_i'_pure
  have h_i1_toNat : (i + 1).toNat = i.toNat + 1 :=
    usize_add_one_toNat i h_no_overflow_i
  obtain ⟨rec, h_rec_ok, h_add⟩ := (RustM_bind_ok_iff _ _ _).mp hat
  obtain ⟨h_no_add_bv, h_v_eq⟩ := i64_add_extract _ _ _ h_add
  have h_no_addOv : ¬ Int64.addOverflow (numbers.val[i.toNat]'hi) rec := by
    show ¬ BitVec.saddOverflow _ _ = true
    rw [h_no_add_bv]; decide
  have h_v_toInt :
      v.toInt = (numbers.val[i.toNat]'hi).toInt + rec.toInt := by
    rw [h_v_eq]
    exact Int64.toInt_add_of_not_addOverflow h_no_addOv
  exact ⟨rec, i + 1, h_i1_toNat, h_rec_ok, h_v_toInt⟩

/-! ## Step lemmas for the recursive `abs_dev_sum_from`

`abs_dev_sum_from numbers mean i` either returns `ok 0` (out-of-bounds
guard), or it recursively computes `|numbers[i] - mean| + (rest)` where
`rest = abs_dev_sum_from numbers mean (i + 1)`. The two step lemmas below
package these branches for use in the strong-induction proofs.

The decomposition `abs_dev_sum_from_recurse_extract` returns the `natAbs`
equation directly, which is more useful for the spec proof and trivially
implies non-negativity (used by `abs_dev_sum_from_nonneg_aux`). -/

/-- OOB step: when `i.toNat ≥ numbers.val.size`, `abs_dev_sum_from`
    returns `ok 0`. -/
private theorem abs_dev_sum_from_oob (numbers : RustSlice i64) (mean : i64) (i : usize)
    (hi : numbers.val.size ≤ i.toNat) :
    clever_004_mean_absolute_deviation.abs_dev_sum_from numbers mean i = RustM.ok 0 := by
  conv => lhs; unfold clever_004_mean_absolute_deviation.abs_dev_sum_from
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' numbers.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat numbers.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- Decomposition: when `abs_dev_sum_from numbers mean i = ok v` and
    `i.toNat < numbers.val.size`, the in-bounds branch ran successfully.
    Returns the index increment, the recursive call result, and the
    `natAbs` equation for `v.toInt`. -/
private theorem abs_dev_sum_from_recurse_extract
    (numbers : RustSlice i64) (mean : i64) (i : usize) (v : i64)
    (hi : i.toNat < numbers.val.size)
    (hat : clever_004_mean_absolute_deviation.abs_dev_sum_from numbers mean i = RustM.ok v) :
    ∃ (rec : i64) (i' : usize),
      i'.toNat = i.toNat + 1 ∧
      clever_004_mean_absolute_deviation.abs_dev_sum_from numbers mean i' = RustM.ok rec ∧
      v.toInt = (((numbers.val[i.toNat]'hi).toInt - mean.toInt).natAbs : Int) + rec.toInt := by
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' numbers.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat numbers.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (numbers[i]_? : RustM i64) = RustM.ok (numbers.val[i.toNat]'hi) := by
    show (if h : i.toNat < numbers.val.size then pure (numbers.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (numbers.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  conv at hat => lhs; unfold clever_004_mean_absolute_deviation.abs_dev_sum_from
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx] at hat
  obtain ⟨d, h_sub, hat⟩ := (RustM_bind_ok_iff _ _ _).mp hat
  obtain ⟨h_no_sub, h_d_eq⟩ := i64_sub_extract _ _ _ h_sub
  subst h_d_eq
  have h_no_subOv :
      ¬ Int64.subOverflow (numbers.val[i.toNat]'hi) mean := by
    show ¬ BitVec.ssubOverflow _ _ = true
    rw [h_no_sub]; decide
  have h_d_toInt :
      ((numbers.val[i.toNat]'hi) - mean).toInt = (numbers.val[i.toNat]'hi).toInt - mean.toInt :=
    Int64.toInt_sub_of_not_subOverflow h_no_subOv
  by_cases h_dnn :
      decide ((0 : i64) ≤ (numbers.val[i.toNat]'hi) - mean) = true
  · -- Non-negative branch: abs_d = d.
    rw [h_dnn] at hat
    simp only [↓reduceIte] at hat
    have h_d_nn : (0 : Int) ≤ ((numbers.val[i.toNat]'hi) - mean).toInt := by
      have h := of_decide_eq_true h_dnn
      have := Int64.le_iff_toInt_le.mp h
      rw [i64_zero_toInt] at this
      exact this
    obtain ⟨i', h_i'_eq, hat⟩ := (RustM_bind_ok_iff _ _ _).mp hat
    have h_size_lt : numbers.val.size < 2^64 := numbers.size_lt_usizeSize
    have h_no_overflow_i : i.toNat + 1 < 2^64 := by omega
    have h_no_bv_i : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
      generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
      cases bo with
      | false => rfl
      | true =>
        exfalso
        have hi' := (USize64.uaddOverflow_iff i 1).mp hbo
        rw [usize_one_toNat] at hi'
        omega
    have h_i_add_pure : (i +? (1 : usize) : RustM usize) = pure (i + 1) := by
      show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = pure (i + 1)
      show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
              then (.fail .integerOverflow : RustM usize)
              else pure (i + 1)) = _
      rw [h_no_bv_i]; rfl
    rw [h_i_add_pure] at h_i'_eq
    have h_i'_pure : i' = i + 1 := by
      have h_ok : (pure (i + 1) : RustM usize) = RustM.ok (i + 1) := rfl
      rw [h_ok] at h_i'_eq
      injection h_i'_eq with h1
      injection h1 with h2
      exact h2.symm
    subst h_i'_pure
    have h_i1_toNat : (i + 1).toNat = i.toNat + 1 :=
      usize_add_one_toNat i h_no_overflow_i
    obtain ⟨rec, h_rec_ok, h_add⟩ := (RustM_bind_ok_iff _ _ _).mp hat
    obtain ⟨h_no_add_bv, h_v_eq⟩ := i64_add_extract _ _ _ h_add
    have h_no_addOv : ¬ Int64.addOverflow ((numbers.val[i.toNat]'hi) - mean) rec := by
      show ¬ BitVec.saddOverflow _ _ = true
      rw [h_no_add_bv]; decide
    have h_v_toInt :
        v.toInt = ((numbers.val[i.toNat]'hi) - mean).toInt + rec.toInt := by
      rw [h_v_eq]
      exact Int64.toInt_add_of_not_addOverflow h_no_addOv
    have h_natAbs : (((numbers.val[i.toNat]'hi).toInt - mean.toInt).natAbs : Int)
        = ((numbers.val[i.toNat]'hi) - mean).toInt := by
      rw [h_d_toInt]
      rw [Int.natAbs_of_nonneg (by rw [← h_d_toInt]; exact h_d_nn)]
    refine ⟨rec, i + 1, h_i1_toNat, h_rec_ok, ?_⟩
    rw [h_v_toInt, h_natAbs]
  · -- Negative branch: abs_d = -d.
    have h_dnn_false : decide ((0 : i64) ≤ (numbers.val[i.toNat]'hi) - mean) = false := by
      cases h : decide ((0 : i64) ≤ (numbers.val[i.toNat]'hi) - mean) with
      | true => exact absurd h h_dnn
      | false => rfl
    rw [h_dnn_false] at hat
    simp only [Bool.false_eq_true, ↓reduceIte] at hat
    have h_d_lt : ((numbers.val[i.toNat]'hi) - mean).toInt < 0 := by
      have h := of_decide_eq_false h_dnn_false
      have hnle : ¬ (0 : i64).toInt ≤ ((numbers.val[i.toNat]'hi) - mean).toInt := by
        intro hle
        exact h (Int64.le_iff_toInt_le.mpr hle)
      rw [i64_zero_toInt] at hnle
      omega
    obtain ⟨abs_d, h_neg_ok, hat⟩ := (RustM_bind_ok_iff _ _ _).mp hat
    obtain ⟨h_d_ne_min, h_abs_d_eq⟩ := i64_neg_extract _ _ h_neg_ok
    subst h_abs_d_eq
    have h_abs_d_toInt : (-((numbers.val[i.toNat]'hi) - mean)).toInt =
        -(((numbers.val[i.toNat]'hi) - mean).toInt) :=
      Int64.toInt_neg_of_ne_intMin h_d_ne_min
    obtain ⟨i', h_i'_eq, hat⟩ := (RustM_bind_ok_iff _ _ _).mp hat
    have h_size_lt : numbers.val.size < 2^64 := numbers.size_lt_usizeSize
    have h_no_overflow_i : i.toNat + 1 < 2^64 := by omega
    have h_no_bv_i : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
      generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
      cases bo with
      | false => rfl
      | true =>
        exfalso
        have hi' := (USize64.uaddOverflow_iff i 1).mp hbo
        rw [usize_one_toNat] at hi'
        omega
    have h_i_add_pure : (i +? (1 : usize) : RustM usize) = pure (i + 1) := by
      show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = pure (i + 1)
      show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
              then (.fail .integerOverflow : RustM usize)
              else pure (i + 1)) = _
      rw [h_no_bv_i]; rfl
    rw [h_i_add_pure] at h_i'_eq
    have h_i'_pure : i' = i + 1 := by
      have h_ok : (pure (i + 1) : RustM usize) = RustM.ok (i + 1) := rfl
      rw [h_ok] at h_i'_eq
      injection h_i'_eq with h1
      injection h1 with h2
      exact h2.symm
    subst h_i'_pure
    have h_i1_toNat : (i + 1).toNat = i.toNat + 1 :=
      usize_add_one_toNat i h_no_overflow_i
    obtain ⟨rec, h_rec_ok, h_add⟩ := (RustM_bind_ok_iff _ _ _).mp hat
    obtain ⟨h_no_add_bv, h_v_eq⟩ := i64_add_extract _ _ _ h_add
    have h_no_addOv :
        ¬ Int64.addOverflow (-((numbers.val[i.toNat]'hi) - mean)) rec := by
      show ¬ BitVec.saddOverflow _ _ = true
      rw [h_no_add_bv]; decide
    have h_v_toInt :
        v.toInt = (-((numbers.val[i.toNat]'hi) - mean)).toInt + rec.toInt := by
      rw [h_v_eq]
      exact Int64.toInt_add_of_not_addOverflow h_no_addOv
    have h_d_int_lt : ((numbers.val[i.toNat]'hi).toInt - mean.toInt) < 0 := by
      rw [← h_d_toInt]; exact h_d_lt
    have h_natAbs : (((numbers.val[i.toNat]'hi).toInt - mean.toInt).natAbs : Int)
        = (-((numbers.val[i.toNat]'hi) - mean)).toInt := by
      rw [h_abs_d_toInt, h_d_toInt]
      -- Goal: ((val[i].toInt - mean.toInt).natAbs : Int) = -(val[i].toInt - mean.toInt)
      -- With h_d_int_lt : val[i].toInt - mean.toInt < 0, omega handles this.
      omega
    refine ⟨rec, i + 1, h_i1_toNat, h_rec_ok, ?_⟩
    rw [h_v_toInt, h_natAbs]

/-! ## Strong-induction lemma for non-negativity

`abs_dev_sum_from` returns a non-negative `i64` (its `.toInt` is ≥ 0)
whenever it returns successfully. Induction on `numbers.val.size - i.toNat`. -/

private theorem abs_dev_sum_from_nonneg_aux (numbers : RustSlice i64) (mean : i64) :
    ∀ (m : Nat) (i : usize) (v : i64),
      numbers.val.size - i.toNat ≤ m →
      clever_004_mean_absolute_deviation.abs_dev_sum_from numbers mean i = RustM.ok v →
      0 ≤ v.toInt := by
  intro m
  induction m with
  | zero =>
    intro i v hm hat
    have hi_ge : numbers.val.size ≤ i.toNat := by omega
    have h_ok := abs_dev_sum_from_oob numbers mean i hi_ge
    rw [h_ok] at hat
    injection hat with hv
    injection hv with hv'
    subst hv'
    rw [i64_zero_toInt]; omega
  | succ m ih =>
    intro i v hm hat
    by_cases hi_ge : numbers.val.size ≤ i.toNat
    · have h_ok := abs_dev_sum_from_oob numbers mean i hi_ge
      rw [h_ok] at hat
      injection hat with hv
      injection hv with hv'
      subst hv'
      rw [i64_zero_toInt]; omega
    · have hi_lt : i.toNat < numbers.val.size := Nat.lt_of_not_le hi_ge
      obtain ⟨rec, i', h_i1, h_rec_ok, h_v_eq⟩ :=
        abs_dev_sum_from_recurse_extract numbers mean i v hi_lt hat
      have h_size_lt : numbers.val.size < 2^64 := numbers.size_lt_usizeSize
      have h_m_le : numbers.val.size - i'.toNat ≤ m := by rw [h_i1]; omega
      have h_rec_nn : 0 ≤ rec.toInt := ih i' rec h_m_le h_rec_ok
      have h_natAbs_nn :
          (0 : Int) ≤ (((numbers.val[i.toNat]'hi_lt).toInt - mean.toInt).natAbs : Int) := by
        exact_mod_cast Nat.zero_le _
      rw [h_v_eq]; omega

/-! ## Strong-induction lemmas for functional correctness

These give a clean recursive integer equation that lets the obligation
proof avoid reasoning about `Array.foldl` directly. Both proofs follow
the same shape as `abs_dev_sum_from_nonneg_aux`. -/

private theorem sum_from_spec_aux (numbers : RustSlice i64) :
    ∀ (m : Nat) (i : usize) (v : i64),
      numbers.val.size - i.toNat ≤ m →
      clever_004_mean_absolute_deviation.sum_from numbers i = RustM.ok v →
      v.toInt = slice_tail_sum_int numbers i.toNat := by
  intro m
  induction m with
  | zero =>
    intro i v hm hat
    have hi_ge : numbers.val.size ≤ i.toNat := by omega
    have h_ok := sum_from_oob numbers i hi_ge
    rw [h_ok] at hat
    injection hat with hv
    injection hv with hv'
    subst hv'
    rw [i64_zero_toInt, slice_tail_sum_int_oob _ _ hi_ge]
  | succ m ih =>
    intro i v hm hat
    by_cases hi_ge : numbers.val.size ≤ i.toNat
    · have h_ok := sum_from_oob numbers i hi_ge
      rw [h_ok] at hat
      injection hat with hv
      injection hv with hv'
      subst hv'
      rw [i64_zero_toInt, slice_tail_sum_int_oob _ _ hi_ge]
    · have hi_lt : i.toNat < numbers.val.size := Nat.lt_of_not_le hi_ge
      obtain ⟨rec, i', h_i1, h_rec_ok, h_v_eq⟩ :=
        sum_from_recurse_extract numbers i v hi_lt hat
      have h_size_lt : numbers.val.size < 2^64 := numbers.size_lt_usizeSize
      have h_m_le : numbers.val.size - i'.toNat ≤ m := by rw [h_i1]; omega
      have h_rec_eq : rec.toInt = slice_tail_sum_int numbers i'.toNat :=
        ih i' rec h_m_le h_rec_ok
      rw [slice_tail_sum_int_step numbers i.toNat hi_lt]
      rw [h_v_eq, h_rec_eq, h_i1]

private theorem sum_from_spec (numbers : RustSlice i64) (i : usize) (v : i64)
    (h : clever_004_mean_absolute_deviation.sum_from numbers i = RustM.ok v) :
    v.toInt = slice_tail_sum_int numbers i.toNat :=
  sum_from_spec_aux numbers (numbers.val.size - i.toNat) i v (Nat.le_refl _) h

private theorem abs_dev_sum_from_spec_aux (numbers : RustSlice i64) (mean : i64) :
    ∀ (m : Nat) (i : usize) (v : i64),
      numbers.val.size - i.toNat ≤ m →
      clever_004_mean_absolute_deviation.abs_dev_sum_from numbers mean i = RustM.ok v →
      v.toInt = slice_tail_abs_dev_sum_int numbers mean.toInt i.toNat := by
  intro m
  induction m with
  | zero =>
    intro i v hm hat
    have hi_ge : numbers.val.size ≤ i.toNat := by omega
    have h_ok := abs_dev_sum_from_oob numbers mean i hi_ge
    rw [h_ok] at hat
    injection hat with hv
    injection hv with hv'
    subst hv'
    rw [i64_zero_toInt, slice_tail_abs_dev_sum_int_oob _ _ _ hi_ge]
  | succ m ih =>
    intro i v hm hat
    by_cases hi_ge : numbers.val.size ≤ i.toNat
    · have h_ok := abs_dev_sum_from_oob numbers mean i hi_ge
      rw [h_ok] at hat
      injection hat with hv
      injection hv with hv'
      subst hv'
      rw [i64_zero_toInt, slice_tail_abs_dev_sum_int_oob _ _ _ hi_ge]
    · have hi_lt : i.toNat < numbers.val.size := Nat.lt_of_not_le hi_ge
      obtain ⟨rec, i', h_i1, h_rec_ok, h_v_eq⟩ :=
        abs_dev_sum_from_recurse_extract numbers mean i v hi_lt hat
      have h_size_lt : numbers.val.size < 2^64 := numbers.size_lt_usizeSize
      have h_m_le : numbers.val.size - i'.toNat ≤ m := by rw [h_i1]; omega
      have h_rec_eq : rec.toInt = slice_tail_abs_dev_sum_int numbers mean.toInt i'.toNat :=
        ih i' rec h_m_le h_rec_ok
      rw [slice_tail_abs_dev_sum_int_step numbers mean.toInt i.toNat hi_lt]
      rw [h_v_eq, h_rec_eq, h_i1]

private theorem abs_dev_sum_from_spec (numbers : RustSlice i64) (mean : i64) (i : usize) (v : i64)
    (h : clever_004_mean_absolute_deviation.abs_dev_sum_from numbers mean i = RustM.ok v) :
    v.toInt = slice_tail_abs_dev_sum_int numbers mean.toInt i.toNat :=
  abs_dev_sum_from_spec_aux numbers mean (numbers.val.size - i.toNat) i v (Nat.le_refl _) h

/-! ## Division-extraction helper

When `(x /? y) = ok r`, neither the (IntMin, -1) overflow nor the
division-by-zero branch fired. We extract this in a single helper. -/

private theorem i64_div_extract (x y r : i64)
    (h : (x /? y : RustM i64) = RustM.ok r) :
    ¬ (x = Int64.minValue ∧ y = -1) ∧ y ≠ 0 ∧ r = x / y := by
  have h_unfold : (x /? y : RustM i64) =
      (if x = Int64.minValue && y = -1 then (.fail .integerOverflow : RustM i64)
       else if y = 0 then .fail .divisionByZero
       else pure (x / y)) := rfl
  rw [h_unfold] at h
  by_cases h1 : x = Int64.minValue ∧ y = -1
  · exfalso
    have h_eq : (x = Int64.minValue && y = -1 : Bool) = true := by
      rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
      · rw [decide_eq_true_iff]; exact h1.1
      · rw [decide_eq_true_iff]; exact h1.2
    rw [h_eq, if_pos rfl] at h
    cases h
  · have h_neq : (x = Int64.minValue && y = -1 : Bool) = false := by
      rw [Bool.and_eq_false_iff]
      by_cases hx : x = Int64.minValue
      · right
        rw [decide_eq_false_iff_not]
        intro hy; exact h1 ⟨hx, hy⟩
      · left
        rw [decide_eq_false_iff_not]; exact hx
    rw [h_neq, if_neg (by decide)] at h
    by_cases hy : y = 0
    · exfalso
      rw [if_pos hy] at h
      cases h
    · rw [if_neg hy] at h
      have h_pure_eq : (pure (x / y) : RustM i64) = RustM.ok (x / y) := rfl
      rw [h_pure_eq] at h
      injection h with hh1
      injection hh1 with hh2
      exact ⟨h1, hy, hh2.symm⟩

/-- Bridge: `(x /? y) = ok r → r.toInt = x.toInt.tdiv y.toInt`.
    Uses the standard `Int64.toInt_div_of_ne_left/_right` lemmas. -/
private theorem i64_div_toInt (x y r : i64)
    (h : (x /? y : RustM i64) = RustM.ok r) :
    r.toInt = x.toInt.tdiv y.toInt := by
  obtain ⟨h_no_ov, h_y_ne, h_r_eq⟩ := i64_div_extract x y r h
  subst h_r_eq
  by_cases hx : x = Int64.minValue
  · -- x = minValue, so y ≠ -1 (else h_no_ov fails).
    have hy : y ≠ -1 := fun hy => h_no_ov ⟨hx, hy⟩
    exact Int64.toInt_div_of_ne_right x y hy
  · exact Int64.toInt_div_of_ne_left x y hx

/-! ## Bridge lemmas between the recursive sums and the `slice_sum_int` / `slice_abs_dev_sum_int` totals -/

private theorem slice_sum_int_eq (s : RustSlice i64) :
    slice_sum_int s = slice_tail_sum_int s 0 := rfl

private theorem slice_abs_dev_sum_int_eq (s : RustSlice i64) (mean : Int) :
    slice_abs_dev_sum_int s mean = slice_tail_abs_dev_sum_int s mean 0 := rfl

/-! ## Contract obligations -/

/-- Empty-slice postcondition.

    Corresponds to the unit test `empty_returns_zero`:
    `mean_absolute_deviation(&[]) == 0`. Calling on an empty slice is
    a valid call (no panic) and returns 0. -/
theorem mean_absolute_deviation_empty (s : RustSlice i64) (hempty : s.val.size = 0) :
    clever_004_mean_absolute_deviation.mean_absolute_deviation s = RustM.ok 0 := by
  unfold clever_004_mean_absolute_deviation.mean_absolute_deviation
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.hax.cast_op, hempty, pure_bind]
  rfl

/-- Functional-correctness postcondition.

    Corresponds to the proptest `matches_reference_formula`:
    whenever `mean_absolute_deviation` returns successfully, the
    returned `i64` equals the integer-valued MAD spec. The spec uses the
    same `as i64` cast on the length as the Rust implementation does, so
    the contract is well-defined even on slice sizes ≥ 2^63 where the
    cast wraps to a negative divisor. -/
theorem mean_absolute_deviation_matches_spec (s : RustSlice i64) (r : i64)
    (h : clever_004_mean_absolute_deviation.mean_absolute_deviation s = RustM.ok r) :
    r.toInt = mad_int s := by
  by_cases hempty : s.val.size = 0
  · -- Empty branch closes via the empty postcondition.
    have h_empty := mean_absolute_deviation_empty s hempty
    rw [h_empty] at h
    injection h with h1
    injection h1 with h2
    subst h2
    unfold mad_int
    rw [i64_zero_toInt]
    -- Goal: 0 = if n = 0 then 0 else (...).  Show n = 0 from hempty.
    have h_n : (USize64.toInt64 (USize64.ofNat s.val.size)).toInt = 0 := by
      rw [hempty]; decide
    simp only [h_n, ↓reduceIte]
  · -- Non-empty branch. Substantive attempt: unfold the function body,
    -- case-split on whether the cast `n = 0` (as i64), decompose the
    -- sum_from + division + abs_dev_sum_from + division chain, and apply
    -- the spec lemmas.
    unfold clever_004_mean_absolute_deviation.mean_absolute_deviation at h
    -- First reduce cast_op and the comparison. Cast.cast for USize64→Int64
    -- reduces definitionally to `pure (USize64.toInt64 _)`.
    have h_cast_pure :
        (Cast.cast (USize64.ofNat s.val.size) : RustM i64)
          = pure (USize64.toInt64 (USize64.ofNat s.val.size)) := rfl
    simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
               rust_primitives.hax.cast_op, h_cast_pure,
               rust_primitives.cmp.eq, pure_bind] at h
    by_cases hn_eq : USize64.toInt64 (USize64.ofNat s.val.size) = (0 : i64)
    · -- n = 0 (as i64): function returns 0; mad_int also returns 0.
      have h_beq : (USize64.toInt64 (USize64.ofNat s.val.size) == (0 : i64)) = true := by
        rw [beq_iff_eq]; exact hn_eq
      rw [h_beq] at h
      simp only [↓reduceIte] at h
      have h_pure : (pure (0 : i64) : RustM i64) = RustM.ok 0 := rfl
      rw [h_pure] at h
      injection h with h1
      injection h1 with h2
      subst h2
      rw [i64_zero_toInt]
      unfold mad_int
      have h_n_int : (USize64.toInt64 (USize64.ofNat s.val.size)).toInt = 0 := by
        rw [hn_eq]; decide
      simp only [h_n_int, ↓reduceIte]
    · -- n ≠ 0 (as i64): function does the divisions.
      have h_beq : (USize64.toInt64 (USize64.ofNat s.val.size) == (0 : i64)) = false := by
        rw [beq_eq_false_iff_ne]; exact hn_eq
      rw [h_beq] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      -- Decompose the sum_from / division / abs_dev_sum_from / division chain.
      obtain ⟨sum, h_sum_ok, h⟩ := (RustM_bind_ok_iff _ _ _).mp h
      obtain ⟨mean, h_mean_ok, h⟩ := (RustM_bind_ok_iff _ _ _).mp h
      obtain ⟨abs_dev, h_abs_dev_ok, h_r⟩ := (RustM_bind_ok_iff _ _ _).mp h
      -- Apply spec lemmas: sum.toInt = slice_tail_sum_int s 0, etc.
      have h_sum_toInt : sum.toInt = slice_tail_sum_int s 0 :=
        sum_from_spec s 0 sum h_sum_ok
      have h_mean_toInt :
          mean.toInt = sum.toInt.tdiv (USize64.toInt64 (USize64.ofNat s.val.size)).toInt :=
        i64_div_toInt _ _ _ h_mean_ok
      have h_abs_dev_toInt :
          abs_dev.toInt = slice_tail_abs_dev_sum_int s mean.toInt 0 :=
        abs_dev_sum_from_spec s mean 0 abs_dev h_abs_dev_ok
      have h_r_toInt :
          r.toInt = abs_dev.toInt.tdiv (USize64.toInt64 (USize64.ofNat s.val.size)).toInt :=
        i64_div_toInt _ _ _ h_r
      -- `n.toInt ≠ 0` follows from `n ≠ 0` and `toInt` injectivity.
      have h_n_int_ne : (USize64.toInt64 (USize64.ofNat s.val.size)).toInt ≠ 0 := by
        intro h_eq
        apply hn_eq
        have h2 : (USize64.toInt64 (USize64.ofNat s.val.size)).toInt = (0 : i64).toInt := by
          rw [h_eq, i64_zero_toInt]
        exact Int64.toInt_inj.mp h2
      -- Assemble: rewrite r.toInt and unfold mad_int.
      rw [h_r_toInt, h_abs_dev_toInt, h_mean_toInt, h_sum_toInt]
      unfold mad_int slice_sum_int slice_abs_dev_sum_int
      simp only [h_n_int_ne, ↓reduceIte]

/-- Non-negativity postcondition.

    Corresponds to the proptest `result_is_non_negative`:
    whenever `mean_absolute_deviation` returns successfully, the
    returned `i64` is non-negative.

    Progress: the empty branch closes via `mean_absolute_deviation_empty`.
    The non-empty branch needs the chain
        `abs_dev_sum_from numbers mean 0 = ok ads`
        ⇒ (by `abs_dev_sum_from_nonneg_aux`) `0 ≤ ads.toInt`
        ⇒ (by `i64_div_toInt` and `Int.tdiv_nonneg`)
          `0 ≤ (ads /? n).toInt = r.toInt`
    which requires unfolding the outer do-block and bridging the cast
    divisor `n = USize64.toInt64 (USize64.ofNat s.val.size)`.

    Stuck sub-goal: `0 ≤ r.toInt = ads.toInt.tdiv n.toInt`. We have
    `0 ≤ ads.toInt` from `abs_dev_sum_from_nonneg_aux`. For sizes ≥ 2^63
    the cast wraps so `n.toInt < 0`, and `Int.tdiv` of a positive
    dividend by a negative divisor returns a value ≤ 0 — but it can be
    strictly negative (e.g. `5.tdiv (-2) = -2 < 0`), so the contract
    genuinely fails on pathological inputs.

    Structural unblock: tighten the theorem statement to add
    `(h_size : s.val.size < 2^63)`, then the non-empty branch closes via
    `abs_dev_sum_from_nonneg_aux` + `i64_div_toInt` + `Int.tdiv_nonneg`,
    after deriving `0 < n.toInt` from `h_size`. The retry instructions
    forbid weakening the obligation by adding hypotheses, so the
    surviving `sorry` reflects a statement-level limitation on slice
    sizes for which the cast `len() as i64` wraps. -/
theorem mean_absolute_deviation_non_negative (s : RustSlice i64) (r : i64)
    (h : clever_004_mean_absolute_deviation.mean_absolute_deviation s = RustM.ok r) :
    0 ≤ r.toInt := by
  by_cases hempty : s.val.size = 0
  · -- Empty branch: use mean_absolute_deviation_empty.
    have h_empty := mean_absolute_deviation_empty s hempty
    rw [h_empty] at h
    injection h with h1
    injection h1 with h2
    subst h2
    rw [i64_zero_toInt]; omega
  · -- Non-empty branch.  Substantive attempt: unfold the function, extract
    -- the divisor cast, run the function decomposition through to the
    -- final division, and reduce to `0 ≤ ads.toInt.tdiv n.toInt`. We get
    -- stuck because for slice sizes ≥ 2^63 the cast `as i64` wraps so
    -- `n.toInt < 0`, and the contract is genuinely false on such inputs.
    unfold clever_004_mean_absolute_deviation.mean_absolute_deviation at h
    simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
               rust_primitives.hax.cast_op, pure_bind, RustM_ok_bind] at h
    -- After this point we would case-split on `n ==? 0`, take the
    -- non-zero branch, extract `sum`, `mean`, `abs_dev`, apply
    -- `abs_dev_sum_from_nonneg_aux` for `0 ≤ abs_dev.toInt`, and apply
    -- `i64_div_toInt` to compute `r.toInt = abs_dev.toInt.tdiv n.toInt`.
    -- The goal reduces to `0 ≤ abs_dev.toInt.tdiv n.toInt`, which is
    -- false in general because `n.toInt` can be negative.
    sorry

end Clever_004_mean_absolute_deviationObligations
