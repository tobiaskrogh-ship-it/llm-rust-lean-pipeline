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

/-! ## Non-positive boundary clause -/

theorem sum_to_n_non_positive (n : i64) (h : n.toInt < 1) :
    clever_047_sum_to_n.sum_to_n n = RustM.ok (0 : i64) := by
  unfold clever_047_sum_to_n.sum_to_n
  have h_lt : n < (1 : i64) := by
    apply Int64.lt_iff_toInt_lt.mpr
    rw [i64_one_toInt]; exact h
  have h_dec : decide (n < (1 : i64)) = true := decide_eq_true h_lt
  simp only [show (n <? (1 : i64) : RustM Bool) =
                 (pure (decide (n < (1 : i64))) : RustM Bool) from rfl,
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

/-! ## Algebraic helpers: Gauss step on Int. -/

private theorem gauss_step_int (k : Int) (hk : 1 ≤ k) :
    (k - 1) * k / 2 + k = k * (k + 1) / 2 := by
  -- (k - 1) * k + 2 * k = k * (k + 1)
  have e1 : (k - 1) * k + 2 * k = k * (k + 1) := by
    have ha : (k - 1) * k + 2 * k = (k - 1 + 2) * k := by rw [Int.add_mul]
    rw [ha]
    have hb : k - 1 + 2 = k + 1 := by omega
    rw [hb, Int.mul_comm]
  -- Divide both sides by 2 via `Int.add_mul_ediv_left`.
  have e2 : ((k - 1) * k + 2 * k) / 2 = (k - 1) * k / 2 + k :=
    @Int.add_mul_ediv_left ((k - 1) * k) 2 k (by decide)
  -- Goal: (k - 1) * k / 2 + k = k * (k + 1) / 2
  rw [← e2, e1]

/-! ## Bound on `k` from the accumulator invariant. -/

private theorem k_bound_of_acc_inv (k : Int) (hk_lo : 1 ≤ k)
    (hk_acc_lt : (k - 1) * k / 2 < 2 ^ 63) :
    k ≤ 2 ^ 32 := by
  by_contra h
  have h_gt : (2 : Int) ^ 32 < k := by
    have : (2 : Int) ^ 32 ≤ k - 1 ∨ k - 1 < 2 ^ 32 := le_or_lt (2 ^ 32) (k - 1)
    rcases this with h1 | h1
    · omega
    · exfalso; apply h; omega
  have h_k_ge : (2 : Int) ^ 32 + 1 ≤ k := by omega
  have h_km1_ge : (2 : Int) ^ 32 ≤ k - 1 := by omega
  have h_prod : (2 : Int) ^ 32 * (2 ^ 32 + 1) ≤ (k - 1) * k :=
    Int.mul_le_mul h_km1_ge h_k_ge (by decide) (by omega)
  have h_pow : (2 ^ 32 : Int) * (2 ^ 32 + 1) = 2 ^ 64 + 2 ^ 32 := by decide
  rw [h_pow] at h_prod
  have h_div : (2 ^ 64 + 2 ^ 32 : Int) / 2 ≤ (k - 1) * k / 2 :=
    Int.ediv_le_ediv (by decide) h_prod
  have h_half : ((2 ^ 64 + 2 ^ 32 : Int)) / 2 = 2 ^ 63 + 2 ^ 31 := by decide
  rw [h_half] at h_div
  have h_pow_lt : (2 ^ 63 : Int) ≤ 2 ^ 63 + 2 ^ 31 := by decide
  omega

/-! ## Main characterization lemma

Strong induction on `(n.toInt + 1 - k.toInt).toNat`. -/

private theorem sum_to_n_at_correct (n : i64) (hn_pos : 1 ≤ n.toInt) :
    ∀ (m : Nat) (k acc : i64),
      1 ≤ k.toInt → k.toInt ≤ n.toInt + 1 →
      acc.toInt = (k.toInt - 1) * k.toInt / 2 →
      (n.toInt + 1 - k.toInt).toNat = m →
      (if n.toInt * (n.toInt + 1) / 2 < 2 ^ 63 then
        ∃ r : i64,
          clever_047_sum_to_n.sum_to_n_at n k acc = RustM.ok r ∧
          r.toInt = n.toInt * (n.toInt + 1) / 2
       else
        clever_047_sum_to_n.sum_to_n_at n k acc = RustM.fail .integerOverflow) := by
  intro m
  induction m with
  | zero =>
    intro k acc hk_lo hk_hi hacc hm
    -- Force k = n+1 from `(n+1 - k).toNat = 0` and `k ≤ n+1`
    have h_diff_nn : (0 : Int) ≤ n.toInt + 1 - k.toInt := by omega
    have h_int_eq : ((n.toInt + 1 - k.toInt).toNat : Int) = n.toInt + 1 - k.toInt :=
      Int.toNat_of_nonneg h_diff_nn
    have hm_int : (n.toInt + 1 - k.toInt) = ((0 : Nat) : Int) := by
      rw [← hm]; exact h_int_eq.symm
    have hk_eq : k.toInt = n.toInt + 1 := by simp at hm_int; omega
    have h_gt : k.toInt > n.toInt := by omega
    -- acc.toInt = n*(n+1)/2 follows from substitution.
    have h_acc_at_end : acc.toInt = n.toInt * (n.toInt + 1) / 2 := by
      rw [hacc, hk_eq]
      have : n.toInt + 1 - 1 = n.toInt := by omega
      rw [this]
    by_cases hfit : n.toInt * (n.toInt + 1) / 2 < 2 ^ 63
    · rw [if_pos hfit]
      refine ⟨acc, sum_to_n_at_base n k acc h_gt, h_acc_at_end⟩
    · rw [if_neg hfit]
      exfalso
      have h_acc_lt := i64_toInt_lt acc
      rw [h_acc_at_end] at h_acc_lt
      omega
  | succ m ih =>
    intro k acc hk_lo hk_hi hacc hm
    -- m+1 ≥ 1 forces n+1 - k ≥ 1, i.e., k ≤ n.
    have h_diff_nn : (0 : Int) ≤ n.toInt + 1 - k.toInt := by omega
    have h_int_eq : ((n.toInt + 1 - k.toInt).toNat : Int) = n.toInt + 1 - k.toInt :=
      Int.toNat_of_nonneg h_diff_nn
    have h_succ : (n.toInt + 1 - k.toInt) = ((m + 1 : Nat) : Int) := by
      rw [← hm]; exact h_int_eq.symm
    have h_pos : (m + 1 : Int) ≥ 1 := by simp
    have h_diff_pos : 1 ≤ n.toInt + 1 - k.toInt := by
      have := h_succ
      push_cast at this
      omega
    have hk_le_n : k.toInt ≤ n.toInt := by omega
    -- Bound on k from invariant
    have h_acc_lt := i64_toInt_lt acc
    rw [hacc] at h_acc_lt
    have hk_bound_32 : k.toInt ≤ 2 ^ 32 := k_bound_of_acc_inv k.toInt hk_lo h_acc_lt
    have hk_fit_hi : k.toInt + 1 < 2 ^ 63 := by
      have : (2 ^ 32 : Int) + 1 < 2 ^ 63 := by decide
      omega
    -- acc + k = k*(k+1)/2 via Gauss step
    have h_acc_plus_k : acc.toInt + k.toInt = k.toInt * (k.toInt + 1) / 2 := by
      rw [hacc]; exact gauss_step_int k.toInt hk_lo
    -- Case-split on overflow at this step
    by_cases hov_step : 2 ^ 63 ≤ acc.toInt + k.toInt
    · -- This step overflows
      have hf : ¬ k.toInt * (k.toInt + 1) / 2 < 2 ^ 63 := by
        rw [← h_acc_plus_k]; omega
      have h_total_overflow : 2 ^ 63 ≤ n.toInt * (n.toInt + 1) / 2 := by
        have h_mul_le : k.toInt * (k.toInt + 1) ≤ n.toInt * (n.toInt + 1) :=
          Int.mul_le_mul hk_le_n (by omega) (by omega) (by omega)
        have h_div_le : k.toInt * (k.toInt + 1) / 2 ≤ n.toInt * (n.toInt + 1) / 2 :=
          Int.ediv_le_ediv (by decide) h_mul_le
        omega
      have h_not_fit : ¬ n.toInt * (n.toInt + 1) / 2 < 2 ^ 63 := by omega
      rw [if_neg h_not_fit]
      exact sum_to_n_at_overflow_pos n k acc hk_le_n hk_fit_hi hov_step
    · -- This step does not overflow
      have hov_step' : acc.toInt + k.toInt < 2 ^ 63 := by omega
      have h_acc_plus_nn : 0 ≤ acc.toInt + k.toInt := by
        rw [h_acc_plus_k]
        apply Int.ediv_nonneg
        · apply Int.mul_nonneg <;> omega
        · decide
      have h_acc_fit_lo : -(2 ^ 63 : Int) ≤ acc.toInt + k.toInt := by
        have : -(2 ^ 63 : Int) ≤ 0 := by decide
        omega
      -- Apply recurse step
      rw [sum_to_n_at_recurse n k acc hk_le_n hk_fit_hi h_acc_fit_lo hov_step']
      -- Apply IH with k' = k + 1, acc' = acc + k
      have h_no_add_k : ¬ Int64.addOverflow k (1 : i64) := by
        intro hov
        rw [Int64.addOverflow_iff, i64_one_toInt, h63_eq] at hov
        have h_k_ge := i64_toInt_ge k
        rcases hov with hov | hov
        · omega
        · omega
      have h_new_k_toInt : (k + (1 : i64)).toInt = k.toInt + 1 := by
        rw [Int64.toInt_add_of_not_addOverflow h_no_add_k, i64_one_toInt]
      have h_no_add_acc : ¬ Int64.addOverflow acc k := by
        intro hov
        rw [Int64.addOverflow_iff, h63_eq] at hov
        rcases hov with hov | hov
        · omega
        · omega
      have h_new_acc_toInt : (acc + k).toInt = acc.toInt + k.toInt :=
        Int64.toInt_add_of_not_addOverflow h_no_add_acc
      have h_new_acc_eq : (acc + k).toInt =
          ((k + 1).toInt - 1) * (k + 1).toInt / 2 := by
        rw [h_new_acc_toInt, h_new_k_toInt, h_acc_plus_k]
        have h_sub : (k.toInt + 1) - 1 = k.toInt := by omega
        rw [h_sub]
      have h_new_k_lo : 1 ≤ (k + (1 : i64)).toInt := by
        rw [h_new_k_toInt]; omega
      have h_new_k_hi : (k + (1 : i64)).toInt ≤ n.toInt + 1 := by
        rw [h_new_k_toInt]; omega
      have h_new_m : (n.toInt + 1 - (k + (1 : i64)).toInt).toNat = m := by
        rw [h_new_k_toInt]
        have h_eq : n.toInt + 1 - (k.toInt + 1) = n.toInt + 1 - k.toInt - 1 := by omega
        rw [h_eq]
        have h_diff_eq : n.toInt + 1 - k.toInt = (m + 1 : Int) := by
          have := h_succ
          push_cast at this
          omega
        rw [h_diff_eq]
        simp
      exact ih (k + 1) (acc + k) h_new_k_lo h_new_k_hi h_new_acc_eq h_new_m

/-! ## Top-level theorems -/

theorem sum_to_n_closed_form (n : i64)
    (hpos : 1 ≤ n.toInt)
    (hfit : n.toInt * (n.toInt + 1) / 2 < 2 ^ 63) :
    ∃ r : i64,
      clever_047_sum_to_n.sum_to_n n = RustM.ok r ∧
      r.toInt = n.toInt * (n.toInt + 1) / 2 := by
  unfold clever_047_sum_to_n.sum_to_n
  have h_not_lt : ¬ n < (1 : i64) := by
    intro h
    have := Int64.lt_iff_toInt_lt.mp h
    rw [i64_one_toInt] at this
    omega
  have h_dec : decide (n < (1 : i64)) = false := decide_eq_false h_not_lt
  simp only [show (n <? (1 : i64) : RustM Bool) =
                 (pure (decide (n < (1 : i64))) : RustM Bool) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
  -- Apply the characterization at k = 1, acc = 0
  have h_inv : (0 : i64).toInt = ((1 : i64).toInt - 1) * (1 : i64).toInt / 2 := by
    rw [i64_zero_toInt, i64_one_toInt]; decide
  have h_k_lo : 1 ≤ (1 : i64).toInt := by rw [i64_one_toInt]
  have h_k_hi : (1 : i64).toInt ≤ n.toInt + 1 := by rw [i64_one_toInt]; omega
  have h_char := sum_to_n_at_correct n hpos
                    (n.toInt + 1 - (1 : i64).toInt).toNat
                    (1 : i64) (0 : i64) h_k_lo h_k_hi h_inv rfl
  rw [if_pos hfit] at h_char
  exact h_char

theorem sum_to_n_overflow (n : i64)
    (hpos : 1 ≤ n.toInt)
    (hov  : 2 ^ 63 ≤ n.toInt * (n.toInt + 1) / 2) :
    clever_047_sum_to_n.sum_to_n n = RustM.fail .integerOverflow := by
  unfold clever_047_sum_to_n.sum_to_n
  have h_not_lt : ¬ n < (1 : i64) := by
    intro h
    have := Int64.lt_iff_toInt_lt.mp h
    rw [i64_one_toInt] at this
    omega
  have h_dec : decide (n < (1 : i64)) = false := decide_eq_false h_not_lt
  simp only [show (n <? (1 : i64) : RustM Bool) =
                 (pure (decide (n < (1 : i64))) : RustM Bool) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
  have h_inv : (0 : i64).toInt = ((1 : i64).toInt - 1) * (1 : i64).toInt / 2 := by
    rw [i64_zero_toInt, i64_one_toInt]; decide
  have h_k_lo : 1 ≤ (1 : i64).toInt := by rw [i64_one_toInt]
  have h_k_hi : (1 : i64).toInt ≤ n.toInt + 1 := by rw [i64_one_toInt]; omega
  have h_char := sum_to_n_at_correct n hpos
                    (n.toInt + 1 - (1 : i64).toInt).toNat
                    (1 : i64) (0 : i64) h_k_lo h_k_hi h_inv rfl
  have h_not_fit : ¬ n.toInt * (n.toInt + 1) / 2 < 2 ^ 63 := by omega
  rw [if_neg h_not_fit] at h_char
  exact h_char

end Clever_047_sum_to_nObligations
