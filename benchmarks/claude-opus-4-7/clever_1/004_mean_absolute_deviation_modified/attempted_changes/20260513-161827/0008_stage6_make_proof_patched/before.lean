-- Companion obligations file for the `clever_004_mean_absolute_deviation` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

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

/-! ## Integer-valued MAD specification

To state functional correctness independently of the recursive
implementation, we define the mean-absolute-deviation computation in `Int`
so the spec itself cannot overflow. The shape mirrors the iterative
`reference_mad` in the Rust source's `tests` module: sum the elements,
divide by `n` (truncating toward zero, matching `i64 /`), sum the absolute
deviations, divide by `n` again. -/

/-- Integer-valued slice sum: `slice_sum_int s = Σᵢ s.val[i].toInt`. -/
private def slice_sum_int (s : RustSlice i64) : Int :=
  s.val.foldl (init := (0 : Int)) (fun acc x => acc + x.toInt)

/-- Integer-valued slice sum of absolute deviations from a chosen mean. -/
private def slice_abs_dev_sum_int (s : RustSlice i64) (mean : Int) : Int :=
  s.val.foldl (init := (0 : Int))
    (fun acc x => acc + ((x.toInt - mean).natAbs : Int))

/-- Integer-valued MAD: matches the Rust `reference_mad`, using `Int`
    truncating division (which agrees with Rust `i64 /` for the divisor
    `n = size`, since `n` is a non-negative `Nat` cast). -/
private def mad_int (s : RustSlice i64) : Int :=
  let n : Int := (s.val.size : Int)
  if n = 0 then 0
  else
    let mean := slice_sum_int s / n
    slice_abs_dev_sum_int s mean / n

/-! ## Step lemmas for the recursive `abs_dev_sum_from`

`abs_dev_sum_from numbers mean i` either returns `ok 0` (out-of-bounds
guard), or it recursively computes `|numbers[i] - mean| + (rest)` where
`rest = abs_dev_sum_from numbers mean (i + 1)`. The two step lemmas below
package these branches for use in the strong-induction proof. -/

/-- OOB step: when `i.toNat ≥ numbers.val.size`, `abs_dev_sum_from`
    returns `ok 0`. Mirrors `below_zero_at_oob` from the reference. -/
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
    Extracts every intermediate result and the no-overflow witnesses.
    The five things this returns are:
    - `d.toInt = numbers.val[i].toInt - mean.toInt` (subtraction succeeded)
    - `abs_d.toInt = |d.toInt|` (the abs-value branch succeeded)
    - `i'.toNat = i.toNat + 1` (the index increment didn't overflow)
    - `abs_dev_sum_from numbers mean i' = ok rec` (recursive call succeeded)
    - `v.toInt = abs_d.toInt + rec.toInt` (final add didn't overflow). -/
private theorem abs_dev_sum_from_recurse_extract
    (numbers : RustSlice i64) (mean : i64) (i : usize) (v : i64)
    (hi : i.toNat < numbers.val.size)
    (hat : clever_004_mean_absolute_deviation.abs_dev_sum_from numbers mean i = RustM.ok v) :
    ∃ (abs_d rec : i64) (i' : usize),
      0 ≤ abs_d.toInt ∧
      i'.toNat = i.toNat + 1 ∧
      clever_004_mean_absolute_deviation.abs_dev_sum_from numbers mean i' = RustM.ok rec ∧
      v.toInt = abs_d.toInt + rec.toInt := by
  -- Step 1: unfold the function body so we can decompose the do-block.
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
  -- Now `hat : ((numbers.val[i] -? mean) >>= ...) = RustM.ok v`. Decompose.
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
  -- Now `hat` says `((if (d ≥ 0) then pure d else (-? d)) >>= ...) = ok v`.
  -- Case-split on the sign of `d`.
  simp only [rust_primitives.cmp.ge] at hat
  by_cases h_dnn :
      decide ((0 : i64) ≤ (numbers.val[i.toNat]'hi) - mean) = true
  · -- Non-negative branch: abs_d = d.
    rw [h_dnn] at hat
    simp only [Bool.true_eq, ↓reduceIte, pure_bind] at hat
    -- hat : (d +? (rec ←)) = ok v where rec is the recursive call result.
    have h_d_nn : (0 : Int) ≤ ((numbers.val[i.toNat]'hi) - mean).toInt := by
      have h := of_decide_eq_true h_dnn
      have := Int64.le_iff_toInt_le.mp h
      rw [i64_zero_toInt] at this
      exact this
    -- Now decompose the (i+1) bind, then the recursive call bind, then the add.
    -- First the `i +? 1`.
    obtain ⟨i', h_i'_eq, hat⟩ := (RustM_bind_ok_iff _ _ _).mp hat
    -- h_i'_eq : (i +? 1) = ok i'
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
    -- Decompose the recursive call bind.
    obtain ⟨rec, h_rec_ok, h_add⟩ := (RustM_bind_ok_iff _ _ _).mp hat
    -- Decompose the final add.
    obtain ⟨_, h_v_eq⟩ := i64_add_extract _ _ _ h_add
    have h_no_addOv : ¬ Int64.addOverflow ((numbers.val[i.toNat]'hi) - mean) rec := by
      show ¬ BitVec.saddOverflow _ _ = true
      rw [h_add.symm ▸ rfl]
      have := i64_add_extract _ _ _ h_add
      rw [this.1]; decide
    have h_v_toInt :
        v.toInt = ((numbers.val[i.toNat]'hi) - mean).toInt + rec.toInt := by
      rw [h_v_eq]
      exact Int64.toInt_add_of_not_addOverflow h_no_addOv
    refine ⟨(numbers.val[i.toNat]'hi) - mean, rec, i + 1, ?_, h_i1_toNat, h_rec_ok, ?_⟩
    · rw [h_d_toInt]; rw [h_d_toInt] at h_d_nn; exact h_d_nn
    · exact h_v_toInt
  · -- Negative branch: abs_d = -d.
    have h_dnn_false : decide ((0 : i64) ≤ (numbers.val[i.toNat]'hi) - mean) = false := by
      cases h : decide ((0 : i64) ≤ (numbers.val[i.toNat]'hi) - mean) with
      | true => exact absurd h h_dnn
      | false => rfl
    rw [h_dnn_false] at hat
    simp only [Bool.false_eq_true, ↓reduceIte] at hat
    have h_d_lt : ((numbers.val[i.toNat]'hi) - mean).toInt < 0 := by
      have h := of_decide_eq_false h_dnn_false
      have hlt : (numbers.val[i.toNat]'hi) - mean < 0 :=
        lt_of_not_ge h
      have := Int64.lt_iff_toInt_lt.mp hlt
      rw [i64_zero_toInt] at this
      exact this
    -- hat : ((-? d) >>= ...) = ok v
    obtain ⟨abs_d, h_neg_ok, hat⟩ := (RustM_bind_ok_iff _ _ _).mp hat
    obtain ⟨h_d_ne_min, h_abs_d_eq⟩ := i64_neg_extract _ _ h_neg_ok
    subst h_abs_d_eq
    have h_abs_d_toInt : (-((numbers.val[i.toNat]'hi) - mean)).toInt =
        -(((numbers.val[i.toNat]'hi) - mean).toInt) :=
      Int64.toInt_neg_of_ne_intMin h_d_ne_min
    have h_abs_d_nn : 0 ≤ (-((numbers.val[i.toNat]'hi) - mean)).toInt := by
      rw [h_abs_d_toInt]; omega
    -- Decompose (i+1) then recursive call then add (same as above branch).
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
    refine ⟨-((numbers.val[i.toNat]'hi) - mean), rec, i + 1, h_abs_d_nn, h_i1_toNat,
            h_rec_ok, h_v_toInt⟩

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
    rw [i64_zero_toInt]
  | succ m ih =>
    intro i v hm hat
    by_cases hi_ge : numbers.val.size ≤ i.toNat
    · have h_ok := abs_dev_sum_from_oob numbers mean i hi_ge
      rw [h_ok] at hat
      injection hat with hv
      injection hv with hv'
      subst hv'
      rw [i64_zero_toInt]
    · have hi_lt : i.toNat < numbers.val.size := Nat.lt_of_not_le hi_ge
      obtain ⟨abs_d, rec, i', h_abs_d_nn, h_i1, h_rec_ok, h_v_eq⟩ :=
        abs_dev_sum_from_recurse_extract numbers mean i v hi_lt hat
      have h_size_lt : numbers.val.size < 2^64 := numbers.size_lt_usizeSize
      have h_m_le : numbers.val.size - i'.toNat ≤ m := by rw [h_i1]; omega
      have h_rec_nn : 0 ≤ rec.toInt := ih i' rec h_m_le h_rec_ok
      rw [h_v_eq]; omega

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
    returned `i64` equals the integer-valued MAD spec (i.e. it agrees
    with the iterative `reference_mad`). The "returns successfully"
    hypothesis encodes the proptest's bounded-input regime, which is
    chosen precisely so no intermediate sum overflows. -/
theorem mean_absolute_deviation_matches_spec (s : RustSlice i64) (r : i64)
    (h : clever_004_mean_absolute_deviation.mean_absolute_deviation s = RustM.ok r) :
    r.toInt = mad_int s := by
  sorry

/-- Non-negativity postcondition.

    Corresponds to the proptest `result_is_non_negative`:
    whenever `mean_absolute_deviation` returns successfully, the
    returned `i64` is non-negative. Stated as a separate, independent
    semantic claim (per the Rust test's own comment): an average of
    absolute values is always ≥ 0, but integer-truncating division on
    a possibly negative dividend makes this non-trivial to read off
    from functional correctness, so it gets its own theorem. -/
theorem mean_absolute_deviation_non_negative (s : RustSlice i64) (r : i64)
    (h : clever_004_mean_absolute_deviation.mean_absolute_deviation s = RustM.ok r) :
    0 ≤ r.toInt := by
  sorry

end Clever_004_mean_absolute_deviationObligations
