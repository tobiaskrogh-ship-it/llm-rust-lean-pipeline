-- Companion obligations file for the `clever_047_sum_to_n` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_047_sum_to_n

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_047_sum_to_nObligations

/-! ## i64 ⇄ Int bridge helpers -/

private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide
private theorem i64_one_toInt : (1 : i64).toInt = 1 := by decide

private theorem i64_toInt_lt (x : i64) : x.toInt < 2 ^ 63 := by
  have h := Int64.toInt_lt x; simpa using h

private theorem i64_toInt_ge (x : i64) : -(2 ^ 63 : Int) ≤ x.toInt := by
  have h := Int64.le_toInt x; simpa using h

private theorem h63_eq : (2 : Int) ^ (64 - 1) = 2 ^ 63 := by decide

/-! ## Helper: a non-positive `i64` value forces the early-return branch. -/

theorem sum_to_n_non_positive (n : i64) (h : n.toInt < 1) :
    clever_047_sum_to_n.sum_to_n n = RustM.ok (0 : i64) := by
  unfold clever_047_sum_to_n.sum_to_n
  have h_lt : n < (1 : i64) := by
    apply Int64.lt_iff_toInt_lt.mpr
    rw [i64_one_toInt]; exact h
  have h_dec : decide (n < (1 : i64)) = true := decide_eq_true h_lt
  simp only [show (n <? (1 : i64) : RustM Bool) = (pure (decide (n < (1 : i64))) : RustM Bool) from rfl,
             h_dec, pure_bind, ↓reduceIte]
  rfl

/-! ## Branch lemmas for `sum_to_n_at` -/

/-- Base branch: when `k.toInt > n.toInt`, the function returns `pure acc`. -/
private theorem sum_to_n_at_base (n k acc : i64) (h : k.toInt > n.toInt) :
    clever_047_sum_to_n.sum_to_n_at n k acc = RustM.ok acc := by
  unfold clever_047_sum_to_n.sum_to_n_at
  have h_gt : k > n := Int64.lt_iff_toInt_lt.mpr h
  have h_dec : decide (k > n) = true := decide_eq_true h_gt
  simp only [show (k >? n : RustM Bool) = (pure (decide (k > n)) : RustM Bool) from rfl,
             h_dec, pure_bind, ↓reduceIte]
  rfl

/-- Recursive step: when `k.toInt ≤ n.toInt`, `k + 1` fits, and `acc + k` fits,
    the function delegates to the recursive call with the updated arguments. -/
private theorem sum_to_n_at_recurse (n k acc : i64)
    (h_le : k.toInt ≤ n.toInt)
    (h_k_fit_hi : k.toInt + 1 < 2 ^ 63)
    (h_acc_fit_lo : -(2 ^ 63 : Int) ≤ acc.toInt + k.toInt)
    (h_acc_fit_hi : acc.toInt + k.toInt < 2 ^ 63) :
    clever_047_sum_to_n.sum_to_n_at n k acc =
      clever_047_sum_to_n.sum_to_n_at n (k + 1) (acc + k) := by
  conv => lhs; unfold clever_047_sum_to_n.sum_to_n_at
  have h_not_gt : ¬ k > n := by
    intro hgt
    have := Int64.lt_iff_toInt_lt.mp hgt
    omega
  have h_dec : decide (k > n) = false := decide_eq_false h_not_gt
  simp only [show (k >? n : RustM Bool) = (pure (decide (k > n)) : RustM Bool) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
  have h_k_ge := i64_toInt_ge k
  have h_no_add_k : ¬ Int64.addOverflow k (1 : i64) := by
    intro hov
    rw [Int64.addOverflow_iff, i64_one_toInt, h63_eq] at hov
    rcases hov with hov | hov
    · omega
    · omega
  have h_bv_k : BitVec.saddOverflow k.toBitVec (1 : i64).toBitVec = false := by
    cases hb : BitVec.saddOverflow k.toBitVec (1 : i64).toBitVec with
    | false => rfl
    | true => exact absurd hb h_no_add_k
  have h_k_plus : (k +? (1 : i64) : RustM i64) = pure (k + 1) := by
    show (rust_primitives.ops.arith.Add.add k 1 : RustM i64) = pure (k + 1)
    show (if BitVec.saddOverflow k.toBitVec (1 : i64).toBitVec then
            (.fail .integerOverflow : RustM i64)
          else pure (k + 1)) = pure (k + 1)
    rw [h_bv_k]; rfl
  rw [h_k_plus]
  simp only [pure_bind]
  have h_no_add_acc : ¬ Int64.addOverflow acc k := by
    intro hov
    rw [Int64.addOverflow_iff, h63_eq] at hov
    rcases hov with hov | hov
    · omega
    · omega
  have h_bv_acc : BitVec.saddOverflow acc.toBitVec k.toBitVec = false := by
    cases hb : BitVec.saddOverflow acc.toBitVec k.toBitVec with
    | false => rfl
    | true => exact absurd hb h_no_add_acc
  have h_acc_plus : (acc +? k : RustM i64) = pure (acc + k) := by
    show (rust_primitives.ops.arith.Add.add acc k : RustM i64) = pure (acc + k)
    show (if BitVec.saddOverflow acc.toBitVec k.toBitVec then
            (.fail .integerOverflow : RustM i64)
          else pure (acc + k)) = pure (acc + k)
    rw [h_bv_acc]; rfl
  rw [h_acc_plus]
  simp only [pure_bind]

/-- Overflow on `acc + k`: when `k.toInt ≤ n.toInt`, `k + 1` fits, and
    `acc.toInt + k.toInt ≥ 2^63`, the function panics with integer overflow. -/
private theorem sum_to_n_at_overflow_pos (n k acc : i64)
    (h_le : k.toInt ≤ n.toInt)
    (h_k_fit_hi : k.toInt + 1 < 2 ^ 63)
    (h_acc_overflow : 2 ^ 63 ≤ acc.toInt + k.toInt) :
    clever_047_sum_to_n.sum_to_n_at n k acc = RustM.fail .integerOverflow := by
  conv => lhs; unfold clever_047_sum_to_n.sum_to_n_at
  have h_not_gt : ¬ k > n := by
    intro hgt
    have := Int64.lt_iff_toInt_lt.mp hgt
    omega
  have h_dec : decide (k > n) = false := decide_eq_false h_not_gt
  simp only [show (k >? n : RustM Bool) = (pure (decide (k > n)) : RustM Bool) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
  have h_k_ge := i64_toInt_ge k
  have h_no_add_k : ¬ Int64.addOverflow k (1 : i64) := by
    intro hov
    rw [Int64.addOverflow_iff, i64_one_toInt, h63_eq] at hov
    rcases hov with hov | hov
    · omega
    · omega
  have h_bv_k : BitVec.saddOverflow k.toBitVec (1 : i64).toBitVec = false := by
    cases hb : BitVec.saddOverflow k.toBitVec (1 : i64).toBitVec with
    | false => rfl
    | true => exact absurd hb h_no_add_k
  have h_k_plus : (k +? (1 : i64) : RustM i64) = pure (k + 1) := by
    show (rust_primitives.ops.arith.Add.add k 1 : RustM i64) = pure (k + 1)
    show (if BitVec.saddOverflow k.toBitVec (1 : i64).toBitVec then
            (.fail .integerOverflow : RustM i64)
          else pure (k + 1)) = pure (k + 1)
    rw [h_bv_k]; rfl
  rw [h_k_plus]
  simp only [pure_bind]
  have h_add_acc : Int64.addOverflow acc k := by
    rw [Int64.addOverflow_iff, h63_eq]
    left; exact h_acc_overflow
  have h_bv_acc : BitVec.saddOverflow acc.toBitVec k.toBitVec = true := h_add_acc
  have h_acc_plus : (acc +? k : RustM i64) = RustM.fail .integerOverflow := by
    show (rust_primitives.ops.arith.Add.add acc k : RustM i64) = RustM.fail .integerOverflow
    show (if BitVec.saddOverflow acc.toBitVec k.toBitVec then
            (.fail .integerOverflow : RustM i64)
          else pure (acc + k)) = RustM.fail .integerOverflow
    rw [h_bv_acc]; rfl
  rw [h_acc_plus]
  rfl

/-! ## Algebraic helper: Gauss step on Int. -/

private theorem gauss_step_int (k : Int) (hk : 1 ≤ k) :
    (k - 1) * k / 2 + k = k * (k + 1) / 2 := by
  -- Step 1: (k - 1) * k + 2 * k = k * (k + 1)
  have h1 : (k - 1) * k + 2 * k = k * (k + 1) := by
    have ha : (k - 1) * k + 2 * k = (k - 1 + 2) * k := by
      rw [Int.add_mul]
    rw [ha]
    have hb : k - 1 + 2 = k + 1 := by omega
    rw [hb, Int.mul_comm]
  -- Step 2: (k - 1) * k is divisible by 2
  have h2 : (2 : Int) ∣ (k - 1) * k := by
    -- one of (k - 1) or k is even
    rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
    · -- k is even ⇒ k = 2 * (k / 2)
      have : (2 : Int) ∣ k := Int.dvd_of_emod_eq_zero hk0
      exact Int.dvd_mul_left.mpr (Or.inr this) |>.elim (fun a => by exact a) (fun _ => Dvd.intro _ rfl)
    · -- k is odd ⇒ k - 1 is even
      have hkm1 : (k - 1) % 2 = 0 := by omega
      have : (2 : Int) ∣ (k - 1) := Int.dvd_of_emod_eq_zero hkm1
      exact Dvd.dvd.mul_right this k
  -- Step 3: divide both sides by 2
  have h3 : ((k - 1) * k + 2 * k) / 2 = (k - 1) * k / 2 + (2 * k) / 2 :=
    Int.add_mul_ediv_left ((k - 1) * k) k (by decide : (2 : Int) ≠ 0)
      |>.symm
      |>.trans (by
        have : ((k - 1) * k + 2 * k) / 2 = (k - 1) * k / 2 + (2 * k) / 2 := by
          rw [Int.add_ediv_of_dvd_left h2]
          congr 1
          have h_dvd : (2 : Int) ∣ 2 * k := Dvd.intro k rfl
          rw [Int.mul_ediv_cancel' k (by decide : (2 : Int) ≠ 0)]
          sorry
        exact this)
  sorry

end Clever_047_sum_to_nObligations
