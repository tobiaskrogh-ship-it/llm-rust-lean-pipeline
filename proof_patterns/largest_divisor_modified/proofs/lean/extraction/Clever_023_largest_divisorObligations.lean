-- Companion obligations file for the `clever_023_largest_divisor` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_023_largest_divisor

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_023_largest_divisorObligations

/-! ## Helper lemmas / closed-form postcondition

The recursive helper `largest_divisor_at n d` searches downward from `d`
for a divisor of `n`. For the valid regime `2 ≤ n.toInt`, we package its
full postcondition into a single helper. The four obligations below are
corollaries: instantiating the helper at `d = n - 1` exposes maximality
among all `k < n`. -/

private theorem int64_min_lt : Int64.minValue.toInt = -9223372036854775808 := by
  decide

private theorem int64_toInt_zero : ((0 : i64).toInt) = 0 := rfl
private theorem int64_toInt_one  : ((1 : i64).toInt) = 1 := rfl

/-- The recursive postcondition for `largest_divisor_at`. -/
private theorem largest_divisor_at_postcondition
    (n : i64) (hn : 2 ≤ n.toInt) :
    ∀ d : i64,
      0 ≤ d.toInt → d.toInt < n.toInt →
      ∃ r : i64,
        clever_023_largest_divisor.largest_divisor_at n d = RustM.ok r
        ∧ 1 ≤ r.toInt ∧ r.toInt < n.toInt
        ∧ r.toInt ∣ n.toInt
        ∧ ∀ k : Int, r.toInt < k → k ≤ d.toInt → ¬ k ∣ n.toInt := by
  intro d
  induction hk : d.toInt.toNat using Nat.strongRecOn generalizing d with
  | _ k ih =>
    intro hd_pos hd_lt
    -- Standard upper/lower bounds on Int64 values.
    have hn_lt_max : n.toInt < 9223372036854775808 := by
      have h := Int64.toInt_lt n
      simpa using h
    have hn_ge_min : -9223372036854775808 ≤ n.toInt := by
      have h := Int64.le_toInt n
      simpa using h
    unfold clever_023_largest_divisor.largest_divisor_at
    by_cases hd0 : d.toInt = 0
    · -- d.toInt = 0: function returns 1.
      have hd_le : d ≤ (0 : i64) := by
        apply Int64.le_iff_toInt_le.mpr
        rw [hd0, int64_toInt_zero]
        omega
      have h_dec : decide (d ≤ (0 : i64)) = true := decide_eq_true hd_le
      simp only [show (d <=? (0 : i64)) =
                   (pure (decide (d ≤ (0 : i64))) : RustM Bool) from rfl,
                 h_dec, pure_bind, ↓reduceIte]
      refine ⟨1, rfl, ?_, ?_, ?_, ?_⟩
      · rw [int64_toInt_one]; omega
      · rw [int64_toInt_one]; omega
      · rw [int64_toInt_one]; exact Int.one_dvd _
      · intro k hk1 hk2
        rw [int64_toInt_one] at hk1; omega
    · -- d.toInt > 0: test n % d == 0.
      have hd_gt0 : 0 < d.toInt := by omega
      have hd_not_le : ¬ d ≤ (0 : i64) := by
        intro h
        have h' : d.toInt ≤ ((0 : i64).toInt) := Int64.le_iff_toInt_le.mp h
        rw [int64_toInt_zero] at h'; omega
      have h_dec : decide (d ≤ (0 : i64)) = false := decide_eq_false hd_not_le
      simp only [show (d <=? (0 : i64)) =
                   (pure (decide (d ≤ (0 : i64))) : RustM Bool) from rfl,
                 h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
      have hn_ne_min : n ≠ Int64.minValue := by
        intro h
        have h' : n.toInt = Int64.minValue.toInt := by rw [h]
        rw [int64_min_lt] at h'; omega
      have hd_ne_zero : d ≠ (0 : i64) := by
        intro h
        have h' : d.toInt = ((0 : i64).toInt) := by rw [h]
        rw [int64_toInt_zero] at h'; omega
      have h_rem : (n %? d : RustM i64) = pure (n % d) := by
        show (rust_primitives.ops.arith.Rem.rem n d : RustM i64) = pure (n % d)
        show (if n = Int64.minValue && d = -1 then
                (.fail .integerOverflow : RustM i64)
              else if d = 0 then .fail .divisionByZero
              else pure (n % d)) = pure (n % d)
        have h_and : (n = Int64.minValue && d = -1) = false := by
          rcases Decidable.em (n = Int64.minValue) with hn_eq | hn_neq
          · exact absurd hn_eq hn_ne_min
          · simp [hn_neq]
        rw [h_and, if_neg hd_ne_zero]
        rfl
      rw [h_rem]
      simp only [pure_bind]
      have h_modInt : (n % d).toInt = n.toInt.tmod d.toInt := Int64.toInt_mod n d
      have hn_nn : 0 ≤ n.toInt := by omega
      have h_modInt' : (n % d).toInt = n.toInt % d.toInt := by
        rw [h_modInt, Int.tmod_eq_emod_of_nonneg hn_nn]
      by_cases h_mod_zero : (n % d) = (0 : i64)
      · -- divisor found.
        have h_dec2 : decide ((n % d) = (0 : i64)) = true :=
          decide_eq_true h_mod_zero
        simp only [show ((n % d) ==? (0 : i64)) =
                     (pure (decide ((n % d) = (0 : i64))) : RustM Bool) from rfl,
                   h_dec2, pure_bind, ↓reduceIte]
        refine ⟨d, rfl, hd_gt0, hd_lt, ?_, ?_⟩
        · have h_mz : (n % d).toInt = 0 := by rw [h_mod_zero, int64_toInt_zero]
          rw [h_modInt'] at h_mz
          exact Int.dvd_of_emod_eq_zero h_mz
        · intro k hk1 hk2; omega
      · -- recurse with d - 1.
        have h_dec2 : decide ((n % d) = (0 : i64)) = false :=
          decide_eq_false h_mod_zero
        simp only [show ((n % d) ==? (0 : i64)) =
                     (pure (decide ((n % d) = (0 : i64))) : RustM Bool) from rfl,
                   h_dec2, pure_bind, Bool.false_eq_true, ↓reduceIte]
        have h_no_overflow : ¬ Int64.subOverflow d 1 := by
          intro h
          rw [Int64.subOverflow_iff] at h
          rw [int64_toInt_one] at h
          have h63 : (2 : Int) ^ (64 - 1) = 9223372036854775808 := by decide
          rw [h63] at h
          rcases h with h | h
          · omega
          · omega
        have h_sub : (d -? (1 : i64) : RustM i64) = pure (d - 1) := by
          show (rust_primitives.ops.arith.Sub.sub d 1 : RustM i64) = pure (d - 1)
          show (if BitVec.ssubOverflow d.toBitVec ((1 : i64).toBitVec) then
                  (.fail .integerOverflow : RustM i64)
                else pure (d - 1)) = pure (d - 1)
          have h_no_bv : BitVec.ssubOverflow d.toBitVec ((1 : i64).toBitVec) = false := by
            simpa [Int64.subOverflow] using h_no_overflow
          rw [h_no_bv]; rfl
        rw [h_sub]
        simp only [pure_bind]
        have h_sub_toInt : (d - 1).toInt = d.toInt - 1 := by
          rw [Int64.toInt_sub_of_not_subOverflow h_no_overflow, int64_toInt_one]
        have h_d_sub_pos : 0 ≤ (d - 1).toInt := by rw [h_sub_toInt]; omega
        have h_d_sub_lt : (d - 1).toInt < n.toInt := by rw [h_sub_toInt]; omega
        have h_measure : (d - 1).toInt.toNat < k := by
          rw [h_sub_toInt, ← hk]
          have h_dnat : d.toInt = (d.toInt.toNat : Int) :=
            (Int.toNat_of_nonneg hd_pos).symm
          omega
        obtain ⟨r, hr_eq, hr_one, hr_lt, hr_dvd, hr_max⟩ :=
          ih (d - 1).toInt.toNat h_measure (d - 1) rfl h_d_sub_pos h_d_sub_lt
        refine ⟨r, hr_eq, hr_one, hr_lt, hr_dvd, ?_⟩
        intro k hk1 hk2
        by_cases heq : k = d.toInt
        · -- k = d.toInt: contradicts n % d ≠ 0.
          intro hdvd
          apply h_mod_zero
          apply Int64.toInt_inj.mp
          rw [h_modInt', int64_toInt_zero]
          rw [heq] at hdvd
          exact Int.emod_eq_zero_of_dvd hdvd
        · -- k < d.toInt (since k ≤ d.toInt and k ≠ d.toInt)
          have hk2' : k ≤ (d - 1).toInt := by rw [h_sub_toInt]; omega
          exact hr_max k hk1 hk2'

/-! ## Contract clauses

The Rust function `largest_divisor n` documents:
  * for `n ≤ 1` it returns `0` (sentinel: no proper divisor defined);
  * for `n ≥ 2` it returns the largest proper divisor of `n`. -/

/-- Edge regime: for `n ≤ 1` (including `0` and all negatives), the
    function returns `0`. -/
theorem largest_divisor_returns_zero_when_n_at_most_one
    (n : i64) (h : n ≤ (1 : i64)) :
    clever_023_largest_divisor.largest_divisor n = RustM.ok (0 : i64) := by
  unfold clever_023_largest_divisor.largest_divisor
  have h_dec : decide (n ≤ (1 : i64)) = true := decide_eq_true h
  simp only [show (n <=? (1 : i64)) =
               (pure (decide (n ≤ (1 : i64))) : RustM Bool) from rfl,
             h_dec, pure_bind, ↓reduceIte]
  rfl

/-- Helper bundling the four facts about `largest_divisor n` in the valid
    regime `2 ≤ n`. -/
private theorem largest_divisor_postcondition
    (n : i64) (h : (2 : i64) ≤ n) :
    ∃ d : i64,
      clever_023_largest_divisor.largest_divisor n = RustM.ok d
      ∧ 1 ≤ d.toInt ∧ d.toInt < n.toInt
      ∧ d.toInt ∣ n.toInt
      ∧ ∀ k : Int, d.toInt < k → k < n.toInt → ¬ k ∣ n.toInt := by
  have hn_ge2 : 2 ≤ n.toInt := by
    have hh := Int64.le_iff_toInt_le.mp h
    simpa using hh
  have h_n_not_le_1 : ¬ n ≤ (1 : i64) := by
    intro hle
    have hh := Int64.le_iff_toInt_le.mp hle
    rw [int64_toInt_one] at hh
    omega
  have h_n_no_overflow : ¬ Int64.subOverflow n 1 := by
    intro hov
    rw [Int64.subOverflow_iff, int64_toInt_one] at hov
    have hn_lt_max : n.toInt < 9223372036854775808 := by
      have hh := Int64.toInt_lt n; simpa using hh
    have hn_ge_min : -9223372036854775808 ≤ n.toInt := by
      have hh := Int64.le_toInt n; simpa using hh
    have h63 : (2 : Int) ^ (64 - 1) = 9223372036854775808 := by decide
    rw [h63] at hov
    rcases hov with hov | hov
    · omega
    · omega
  have h_n_sub : (n -? (1 : i64) : RustM i64) = pure (n - 1) := by
    show (rust_primitives.ops.arith.Sub.sub n 1 : RustM i64) = pure (n - 1)
    show (if BitVec.ssubOverflow n.toBitVec ((1 : i64).toBitVec) then
            (.fail .integerOverflow : RustM i64)
          else pure (n - 1)) = pure (n - 1)
    have h_no_bv : BitVec.ssubOverflow n.toBitVec ((1 : i64).toBitVec) = false := by
      simpa [Int64.subOverflow] using h_n_no_overflow
    rw [h_no_bv]; rfl
  have h_dec : decide (n ≤ (1 : i64)) = false := decide_eq_false h_n_not_le_1
  unfold clever_023_largest_divisor.largest_divisor
  simp only [show (n <=? (1 : i64)) =
               (pure (decide (n ≤ (1 : i64))) : RustM Bool) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
  rw [h_n_sub]
  simp only [pure_bind]
  have h_nm1_toInt : (n - 1).toInt = n.toInt - 1 := by
    rw [Int64.toInt_sub_of_not_subOverflow h_n_no_overflow, int64_toInt_one]
  have h_pos : 0 ≤ (n - 1).toInt := by rw [h_nm1_toInt]; omega
  have h_lt  : (n - 1).toInt < n.toInt := by rw [h_nm1_toInt]; omega
  obtain ⟨r, hr_eq, hr_one, hr_lt, hr_dvd, hr_max⟩ :=
    largest_divisor_at_postcondition n hn_ge2 (n - 1) h_pos h_lt
  refine ⟨r, hr_eq, hr_one, hr_lt, hr_dvd, ?_⟩
  intro k hk1 hk2
  have hk2' : k ≤ (n - 1).toInt := by rw [h_nm1_toInt]; omega
  exact hr_max k hk1 hk2'

/-- Postcondition 1 (divisibility): the returned value divides `n`. -/
theorem largest_divisor_result_divides_n
    (n : i64) (h : (2 : i64) ≤ n) :
    ∃ d : i64,
      clever_023_largest_divisor.largest_divisor n = RustM.ok d
      ∧ d.toInt ∣ n.toInt := by
  obtain ⟨d, hd_eq, _, _, hd_dvd, _⟩ := largest_divisor_postcondition n h
  exact ⟨d, hd_eq, hd_dvd⟩

/-- Postcondition 2 (proper divisor): the returned value is strictly less than `n`. -/
theorem largest_divisor_result_strictly_less_than_n
    (n : i64) (h : (2 : i64) ≤ n) :
    ∃ d : i64,
      clever_023_largest_divisor.largest_divisor n = RustM.ok d
      ∧ d < n := by
  obtain ⟨d, hd_eq, _, hd_lt, _, _⟩ := largest_divisor_postcondition n h
  exact ⟨d, hd_eq, Int64.lt_iff_toInt_lt.mpr hd_lt⟩

/-- Postcondition 3 (maximality): no integer strictly between the returned
    value and `n` divides `n`. -/
theorem largest_divisor_result_is_maximal
    (n : i64) (h : (2 : i64) ≤ n) :
    ∃ d : i64,
      clever_023_largest_divisor.largest_divisor n = RustM.ok d
      ∧ ∀ k : i64, d < k → k < n → ¬ k.toInt ∣ n.toInt := by
  obtain ⟨d, hd_eq, _, _, _, hd_max⟩ := largest_divisor_postcondition n h
  refine ⟨d, hd_eq, ?_⟩
  intro k hk1 hk2
  exact hd_max k.toInt
    (Int64.lt_iff_toInt_lt.mp hk1)
    (Int64.lt_iff_toInt_lt.mp hk2)

end Clever_023_largest_divisorObligations
