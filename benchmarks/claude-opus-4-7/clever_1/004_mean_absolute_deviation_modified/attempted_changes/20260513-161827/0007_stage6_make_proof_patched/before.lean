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
