-- Companion obligations file for the `clever_096_multiply` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_096_multiply

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_096_multiplyObligations

/-! ## i64 ⇄ Int bridge helpers -/

private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide
private theorem i64_ten_toInt : (10 : i64).toInt = 10 := by decide
private theorem int64_minValue_toInt : (Int64.minValue : i64).toInt = -(2 ^ 63 : Int) := by decide

/-- `-? a = pure (-a)` when `a ≠ Int64.minValue`. -/
private theorem i64_neg_pure (a : i64) (h_ne : a ≠ Int64.minValue) :
    (-? a : RustM i64) = pure (-a) := by
  show (rust_primitives.ops.arith.Neg.neg a : RustM i64) = pure (-a)
  show (if a = Int64.minValue
        then (.fail .integerOverflow : RustM i64)
        else pure (-a)) = _
  rw [if_neg h_ne]

/-- `-? Int64.minValue` fails. -/
private theorem i64_neg_fail_min :
    (-? (Int64.minValue : i64) : RustM i64) = .fail .integerOverflow := by
  show (rust_primitives.ops.arith.Neg.neg (Int64.minValue : i64) : RustM i64) = .fail .integerOverflow
  show (if (Int64.minValue : i64) = Int64.minValue
        then (.fail .integerOverflow : RustM i64)
        else pure (-Int64.minValue)) = .fail .integerOverflow
  rw [if_pos rfl]

/-- `a %? b = pure (a % b)` when (a ≠ minValue or b ≠ -1) and b ≠ 0. -/
private theorem i64_mod_pure (a b : i64)
    (h_not_min_neg_one : ¬ (a = Int64.minValue ∧ b = -1))
    (h_b_ne : b ≠ 0) :
    (a %? b : RustM i64) = pure (a % b) := by
  show (rust_primitives.ops.arith.Rem.rem a b : RustM i64) = pure (a % b)
  show (if a = Int64.minValue && b = -1 then (.fail .integerOverflow : RustM i64)
        else if b = 0 then .fail .divisionByZero else pure (a % b)) = _
  have h_and : (a = Int64.minValue && b = -1) = false := by
    rcases Decidable.em (a = Int64.minValue) with ha | ha
    · rcases Decidable.em (b = -1) with hb | hb
      · exact absurd ⟨ha, hb⟩ h_not_min_neg_one
      · simp [hb]
    · simp [ha]
  rw [h_and, if_neg h_b_ne]
  rfl

/-- `a *? b = pure (a * b)` when no overflow. -/
private theorem i64_mul_pure (a b : i64) (h_no : ¬ Int64.mulOverflow a b) :
    (a *? b : RustM i64) = pure (a * b) := by
  have h_bv : BitVec.smulOverflow a.toBitVec b.toBitVec = false := by
    cases hb : BitVec.smulOverflow a.toBitVec b.toBitVec with
    | false => rfl
    | true => exact absurd hb h_no
  show (rust_primitives.ops.arith.Mul.mul a b : RustM i64) = pure (a * b)
  show (if BitVec.smulOverflow a.toBitVec b.toBitVec then
          (.fail .integerOverflow : RustM i64)
        else pure (a * b)) = pure (a * b)
  rw [h_bv]; rfl

/-- `a <? b` reduces to `pure (decide (a < b))`. -/
private theorem i64_lt_def (a b : i64) :
    (a <? b : RustM Bool) = pure (decide (a < b)) := rfl

/-! ## Product reduction lemma.

Given absolute values `aa, bb` non-negative with `aa.toInt = |a|.toInt` and
`bb.toInt = |b|.toInt`, the modular product reduces and equals the
unit-digit product. -/

private theorem product_reduces
    (aa bb a b : i64)
    (h_aa_natAbs : aa.toInt = (a.toInt.natAbs : Int))
    (h_bb_natAbs : bb.toInt = (b.toInt.natAbs : Int))
    (h_aa_nn : 0 ≤ aa.toInt)
    (h_bb_nn : 0 ≤ bb.toInt) :
    ∃ r : i64,
      ((aa %? (10 : i64) : RustM i64) >>= fun ra =>
        (bb %? (10 : i64) : RustM i64) >>= fun rb => (ra *? rb : RustM i64))
        = RustM.ok r ∧
      (r.toInt : Int) =
        ((a.toInt.natAbs % 10 : Nat) : Int) *
          ((b.toInt.natAbs % 10 : Nat) : Int) := by
  have h_ten_ne_neg_one : (10 : i64) ≠ -1 := by decide
  have h_ten_ne_zero : (10 : i64) ≠ 0 := by decide
  have h_aa_mod_pure : (aa %? (10 : i64) : RustM i64) = pure (aa % 10) := by
    apply i64_mod_pure
    · intro ⟨_, h⟩; exact h_ten_ne_neg_one h
    · exact h_ten_ne_zero
  have h_bb_mod_pure : (bb %? (10 : i64) : RustM i64) = pure (bb % 10) := by
    apply i64_mod_pure
    · intro ⟨_, h⟩; exact h_ten_ne_neg_one h
    · exact h_ten_ne_zero
  rw [h_aa_mod_pure]
  simp only [pure_bind]
  rw [h_bb_mod_pure]
  simp only [pure_bind]
  -- aa.toInt mod 10
  have h_aa_mod_toInt : (aa % (10 : i64)).toInt = aa.toInt % 10 := by
    have h_mod_int : (aa % (10 : i64)).toInt = aa.toInt.tmod (10 : i64).toInt :=
      Int64.toInt_mod aa (10 : i64)
    rw [h_mod_int, i64_ten_toInt, Int.tmod_eq_emod_of_nonneg h_aa_nn]
  have h_bb_mod_toInt : (bb % (10 : i64)).toInt = bb.toInt % 10 := by
    have h_mod_int : (bb % (10 : i64)).toInt = bb.toInt.tmod (10 : i64).toInt :=
      Int64.toInt_mod bb (10 : i64)
    rw [h_mod_int, i64_ten_toInt, Int.tmod_eq_emod_of_nonneg h_bb_nn]
  have h_aa_mod_nn : 0 ≤ (aa % (10 : i64)).toInt := by
    rw [h_aa_mod_toInt]; exact Int.emod_nonneg _ (by decide)
  have h_aa_mod_lt : (aa % (10 : i64)).toInt < 10 := by
    rw [h_aa_mod_toInt]; exact Int.emod_lt_of_pos _ (by decide)
  have h_bb_mod_nn : 0 ≤ (bb % (10 : i64)).toInt := by
    rw [h_bb_mod_toInt]; exact Int.emod_nonneg _ (by decide)
  have h_bb_mod_lt : (bb % (10 : i64)).toInt < 10 := by
    rw [h_bb_mod_toInt]; exact Int.emod_lt_of_pos _ (by decide)
  -- No overflow
  have h_no_mul : ¬ Int64.mulOverflow (aa % 10) (bb % 10) := by
    intro hov
    rw [Int64.mulOverflow_iff] at hov
    have h_prod_le : (aa % 10).toInt * (bb % 10).toInt ≤ 9 * 9 := by
      have h1 : (aa % 10).toInt ≤ 9 := by omega
      have h2 : (bb % 10).toInt ≤ 9 := by omega
      exact Int.mul_le_mul h1 h2 h_bb_mod_nn (by decide)
    have h_prod_nn : 0 ≤ (aa % 10).toInt * (bb % 10).toInt :=
      Int.mul_nonneg h_aa_mod_nn h_bb_mod_nn
    have h63 : (2 : Int) ^ (64 - 1) = 2 ^ 63 := by decide
    rw [h63] at hov
    have h81_lt : (9 * 9 : Int) < 2 ^ 63 := by decide
    rcases hov with hp | hn
    · omega
    · omega
  rw [i64_mul_pure (aa % 10) (bb % 10) h_no_mul]
  refine ⟨(aa % 10) * (bb % 10), rfl, ?_⟩
  rw [Int64.toInt_mul_of_not_mulOverflow h_no_mul,
      h_aa_mod_toInt, h_bb_mod_toInt, h_aa_natAbs, h_bb_natAbs,
      Int.natCast_emod a.toInt.natAbs 10, Int.natCast_emod b.toInt.natAbs 10]
  rfl

/-! ## Helpers for sign-case discharge. -/

private theorem a_neg_natAbs (a : i64) (ha : a ≠ Int64.minValue)
    (h_a_lt : a < (0 : i64)) :
    (-a).toInt = (a.toInt.natAbs : Int) := by
  rw [Int64.toInt_neg_of_ne_intMin ha]
  have h_a_neg : a.toInt < 0 := by
    have := Int64.lt_iff_toInt_lt.mp h_a_lt
    rw [i64_zero_toInt] at this; exact this
  -- Goal: -a.toInt = (a.toInt.natAbs : Int)
  have h1 : ((-a.toInt).natAbs : Int) = -a.toInt := Int.natAbs_of_nonneg (by omega)
  rw [Int.natAbs_neg] at h1
  exact h1.symm

private theorem a_neg_nn (a : i64) (ha : a ≠ Int64.minValue)
    (h_a_lt : a < (0 : i64)) :
    0 ≤ (-a).toInt := by
  rw [Int64.toInt_neg_of_ne_intMin ha]
  have h_a_neg : a.toInt < 0 := by
    have := Int64.lt_iff_toInt_lt.mp h_a_lt
    rw [i64_zero_toInt] at this; exact this
  omega

private theorem a_nn_nn (a : i64) (h_a_nlt : ¬ a < (0 : i64)) :
    0 ≤ a.toInt := by
  by_cases h : 0 ≤ a.toInt
  · exact h
  · exfalso
    apply h_a_nlt
    apply Int64.lt_iff_toInt_lt.mpr
    rw [i64_zero_toInt]
    omega

private theorem a_nn_natAbs (a : i64) (h_a_nlt : ¬ a < (0 : i64)) :
    a.toInt = (a.toInt.natAbs : Int) :=
  (Int.natAbs_of_nonneg (a_nn_nn a h_a_nlt)).symm

/-! ## Failure clauses. -/

/-- Failure when `a = i64::MIN`: the inner `-? a` overflows, so the
    function panics with `Error.integerOverflow`.  -/
theorem multiply_fail_when_a_is_min
    (b : i64) :
    clever_096_multiply.multiply Int64.minValue b =
      RustM.fail Error.integerOverflow := by
  unfold clever_096_multiply.multiply
  simp only [i64_lt_def, pure_bind,
             show decide ((Int64.minValue : i64) < 0) = true from by decide,
             if_true]
  rw [i64_neg_fail_min]
  rfl

/-- Failure when `a ≠ i64::MIN` but `b = i64::MIN`: the first abs block
    succeeds, but the second `-? b` overflows. -/
theorem multiply_fail_when_b_is_min
    (a : i64) (ha : a ≠ Int64.minValue) :
    clever_096_multiply.multiply a Int64.minValue =
      RustM.fail Error.integerOverflow := by
  unfold clever_096_multiply.multiply
  simp only [i64_lt_def, pure_bind]
  by_cases h_a_lt : a < (0 : i64)
  · have h_dec : decide (a < (0 : i64)) = true := decide_eq_true h_a_lt
    rw [h_dec]
    simp only [if_true]
    rw [i64_neg_pure a ha]
    simp only [pure_bind,
               show decide ((Int64.minValue : i64) < 0) = true from by decide,
               if_true]
    rw [i64_neg_fail_min]
    rfl
  · have h_dec : decide (a < (0 : i64)) = false := decide_eq_false h_a_lt
    rw [h_dec]
    simp only [Bool.false_eq_true, if_false,
               show decide ((Int64.minValue : i64) < 0) = true from by decide,
               if_true]
    rw [i64_neg_fail_min]
    rfl

/-! ## Main postcondition. -/

/-- Main postcondition: `multiply(a, b)` returns the product of the unit
    digits of `|a|` and `|b|`, expressed via `Int.natAbs` and `%`. -/
theorem multiply_matches_unit_digit_product
    (a b : i64)
    (ha : a ≠ Int64.minValue) (hb : b ≠ Int64.minValue) :
    ∃ r : i64,
      clever_096_multiply.multiply a b = RustM.ok r ∧
      (r.toInt : Int) =
        ((a.toInt.natAbs % 10 : Nat) : Int) *
          ((b.toInt.natAbs % 10 : Nat) : Int) := by
  unfold clever_096_multiply.multiply
  simp only [i64_lt_def, pure_bind]
  by_cases h_a_lt : a < (0 : i64)
  · have h_dec_a : decide (a < (0 : i64)) = true := decide_eq_true h_a_lt
    rw [h_dec_a]
    simp only [if_true]
    rw [i64_neg_pure a ha]
    simp only [pure_bind]
    by_cases h_b_lt : b < (0 : i64)
    · have h_dec_b : decide (b < (0 : i64)) = true := decide_eq_true h_b_lt
      rw [h_dec_b]
      simp only [if_true]
      rw [i64_neg_pure b hb]
      simp only [pure_bind]
      exact product_reduces (-a) (-b) a b
        (a_neg_natAbs a ha h_a_lt)
        (a_neg_natAbs b hb h_b_lt)
        (a_neg_nn a ha h_a_lt)
        (a_neg_nn b hb h_b_lt)
    · have h_dec_b : decide (b < (0 : i64)) = false := decide_eq_false h_b_lt
      rw [h_dec_b]
      simp only [Bool.false_eq_true, if_false]
      exact product_reduces (-a) b a b
        (a_neg_natAbs a ha h_a_lt)
        (a_nn_natAbs b h_b_lt)
        (a_neg_nn a ha h_a_lt)
        (a_nn_nn b h_b_lt)
  · have h_dec_a : decide (a < (0 : i64)) = false := decide_eq_false h_a_lt
    rw [h_dec_a]
    simp only [Bool.false_eq_true, if_false]
    by_cases h_b_lt : b < (0 : i64)
    · have h_dec_b : decide (b < (0 : i64)) = true := decide_eq_true h_b_lt
      rw [h_dec_b]
      simp only [if_true]
      rw [i64_neg_pure b hb]
      simp only [pure_bind]
      exact product_reduces a (-b) a b
        (a_nn_natAbs a h_a_lt)
        (a_neg_natAbs b hb h_b_lt)
        (a_nn_nn a h_a_lt)
        (a_neg_nn b hb h_b_lt)
    · have h_dec_b : decide (b < (0 : i64)) = false := decide_eq_false h_b_lt
      rw [h_dec_b]
      simp only [Bool.false_eq_true, if_false]
      exact product_reduces a b a b
        (a_nn_natAbs a h_a_lt)
        (a_nn_natAbs b h_b_lt)
        (a_nn_nn a h_a_lt)
        (a_nn_nn b h_b_lt)

end Clever_096_multiplyObligations
