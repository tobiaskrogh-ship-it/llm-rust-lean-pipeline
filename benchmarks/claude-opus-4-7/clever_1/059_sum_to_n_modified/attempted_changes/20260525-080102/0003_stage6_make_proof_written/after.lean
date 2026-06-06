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

/-! ## Helper: a non-positive `i64` value forces `n < 1` -/

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

/-! ## Algebraic helper: Gauss step on Int -/

private theorem gauss_step_int (k : Int) (hk : 1 ≤ k) :
    (k - 1) * k / 2 + k = k * (k + 1) / 2 := by
  have h1 : (k - 1) * k + 2 * k = k * (k + 1) := by ring
  have h2 : (k - 1) * k % 2 = 0 := by
    -- (k-1) * k is always even
    have : ((k - 1) * k) % 2 = ((k - 1) % 2) * (k % 2) % 2 := by
      rw [Int.mul_emod]
    -- one of (k-1) or k is even
    have heven : (k - 1) % 2 = 0 ∨ k % 2 = 0 := by
      rcases Int.emod_two_eq_zero_or_one k with hk' | hk'
      · right; exact hk'
      · left; omega
    rcases heven with he | he
    · rw [this, he]; simp
    · rw [this, he]; simp
  have h3 : (2 * k) % 2 = 0 := by
    rw [Int.mul_emod_left]
  have h4 : ((k - 1) * k + 2 * k) / 2 = (k - 1) * k / 2 + (2 * k) / 2 :=
    Int.add_ediv_of_dvd_left (Int.dvd_of_emod_eq_zero h2)
  have h5 : (2 * k) / 2 = k := by
    rw [Int.mul_ediv_cancel_left]; decide
  rw [← h1, h4, h5]

/-! ## Bound on `k` from the accumulator invariant.

If `acc.toInt = (k-1)*k/2` and `acc` fits in `i64`, then `k ≤ 2^32`.
This is the key bound that lets us conclude `k + 1` never overflows on
`+? 1` inside the recursion. -/

private theorem k_bound_of_acc_inv (k : Int) (hk_lo : 1 ≤ k)
    (hk_acc_lt : (k - 1) * k / 2 < 2 ^ 63) :
    k ≤ 2 ^ 32 := by
  by_contra h
  push_neg at h
  -- h : 2^32 < k, so 2^32 + 1 ≤ k
  have h1 : 2 ^ 32 + 1 ≤ k := h
  have h2 : 2 ^ 32 ≤ k - 1 := by omega
  -- (k-1) * k ≥ 2^32 * (2^32 + 1)
  have h3 : 2 ^ 32 * (2 ^ 32 + 1) ≤ (k - 1) * k := by
    have hp1 : (0 : Int) ≤ 2 ^ 32 := by decide
    have hp2 : (0 : Int) ≤ 2 ^ 32 + 1 := by decide
    exact Int.mul_le_mul h2 h1 hp2 (by omega)
  -- 2^32 * (2^32 + 1) = 2^64 + 2^32
  have h4 : (2 ^ 32 : Int) * (2 ^ 32 + 1) = 2 ^ 64 + 2 ^ 32 := by norm_num
  rw [h4] at h3
  -- (k-1)*k / 2 ≥ (2^64 + 2^32) / 2 = 2^63 + 2^31
  have h5 : (2 ^ 64 + 2 ^ 32 : Int) / 2 ≤ (k - 1) * k / 2 := by
    exact Int.ediv_le_ediv (by decide) h3
  have h6 : ((2 ^ 64 + 2 ^ 32 : Int)) / 2 = 2 ^ 63 + 2 ^ 31 := by norm_num
  rw [h6] at h5
  -- Contradicts hk_acc_lt
  have h7 : (2 ^ 63 : Int) ≤ (k - 1) * k / 2 := by
    have : (2 ^ 63 : Int) ≤ 2 ^ 63 + 2 ^ 31 := by norm_num
    omega
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
    -- (n+1 - k).toNat = 0 ∧ k ≤ n+1 ⇒ k = n+1
    have hk_eq : k.toInt = n.toInt + 1 := by
      have h_diff_nn : (0 : Int) ≤ n.toInt + 1 - k.toInt := by omega
      have h_diff_zero : n.toInt + 1 - k.toInt = 0 := by
        rcases Int.lt_or_le (n.toInt + 1 - k.toInt) 1 with hlt | hge
        · omega
        · exfalso
          have : ((n.toInt + 1 - k.toInt).toNat : Int) ≥ 1 := by
            rw [Int.toNat_of_nonneg h_diff_nn]; omega
          rw [hm] at this
          simp at this
      omega
    have h_gt : k.toInt > n.toInt := by omega
    have h_acc_at_end : acc.toInt = n.toInt * (n.toInt + 1) / 2 := by
      rw [hacc, hk_eq]
      ring_nf
    -- Branch on the if
    split_ifs with hfit
    · refine ⟨acc, sum_to_n_at_base n k acc h_gt, h_acc_at_end⟩
    · -- Overflow case: contradiction via i64 bound on acc
      exfalso
      have h_acc_lt := i64_toInt_lt acc
      rw [h_acc_at_end] at h_acc_lt
      push_neg at hfit
      omega
  | succ m ih =>
    intro k acc hk_lo hk_hi hacc hm
    -- m+1 ≥ 1 means n+1 - k ≥ 1, i.e., k ≤ n
    have h_diff_pos : 1 ≤ n.toInt + 1 - k.toInt := by
      have h_diff_nn : (0 : Int) ≤ n.toInt + 1 - k.toInt := by omega
      have h_to_int : ((n.toInt + 1 - k.toInt).toNat : Int) = n.toInt + 1 - k.toInt :=
        Int.toNat_of_nonneg h_diff_nn
      have : ((m + 1 : Nat) : Int) ≥ 1 := by simp
      rw [← hm] at this
      rw [← h_to_int]; exact this
    have hk_le_n : k.toInt ≤ n.toInt := by omega
    -- Derive bound on k via the invariant
    have h_acc_lt := i64_toInt_lt acc
    have h_acc_ge := i64_toInt_ge acc
    rw [hacc] at h_acc_lt
    have hk_bound_32 : k.toInt ≤ 2 ^ 32 := k_bound_of_acc_inv k.toInt hk_lo h_acc_lt
    have hk_fit_hi : k.toInt + 1 < 2 ^ 63 := by
      have : (2 ^ 32 : Int) + 1 < 2 ^ 63 := by decide
      omega
    -- Compute acc + k via the gauss step
    have h_acc_plus_k : acc.toInt + k.toInt = k.toInt * (k.toInt + 1) / 2 := by
      rw [hacc]; exact gauss_step_int k.toInt hk_lo
    -- Split on whether acc + k overflows
    by_cases hov_step : 2 ^ 63 ≤ acc.toInt + k.toInt
    · -- This step overflows: function fails.
      have hf : ¬ k.toInt * (k.toInt + 1) / 2 < 2 ^ 63 := by
        rw [← h_acc_plus_k]; omega
      have h_total_overflow : 2 ^ 63 ≤ n.toInt * (n.toInt + 1) / 2 := by
        -- k*(k+1)/2 ≤ n*(n+1)/2 since k ≤ n.
        have h_mul_le : k.toInt * (k.toInt + 1) ≤ n.toInt * (n.toInt + 1) := by
          apply Int.mul_le_mul hk_le_n (by omega) (by omega) (by omega)
        have h_div_le : k.toInt * (k.toInt + 1) / 2 ≤ n.toInt * (n.toInt + 1) / 2 :=
          Int.ediv_le_ediv (by decide) h_mul_le
        omega
      split_ifs with hfit
      · exfalso; omega
      · exact sum_to_n_at_overflow_pos n k acc hk_le_n hk_fit_hi hov_step
    · -- This step does not overflow on the positive side
      push_neg at hov_step
      -- Show it doesn't overflow on the negative side either: acc + k ≥ 0
      have h_acc_plus_nn : 0 ≤ acc.toInt + k.toInt := by
        rw [h_acc_plus_k]
        apply Int.ediv_nonneg
        · apply Int.mul_nonneg <;> omega
        · norm_num
      have h_acc_fit_lo : -(2 ^ 63 : Int) ≤ acc.toInt + k.toInt := by
        have : -(2 ^ 63 : Int) ≤ 0 := by decide
        omega
      -- Apply the recurse step
      rw [sum_to_n_at_recurse n k acc hk_le_n hk_fit_hi h_acc_fit_lo hov_step]
      -- Apply IH with k' = k + 1, acc' = acc + k
      have h_new_k_toInt : (k + (1 : i64)).toInt = k.toInt + 1 := by
        have h_no : ¬ Int64.addOverflow k (1 : i64) := by
          intro hov
          rw [Int64.addOverflow_iff, i64_one_toInt, h63_eq] at hov
          have h_k_ge := i64_toInt_ge k
          rcases hov with hov | hov
          · omega
          · omega
        rw [Int64.toInt_add_of_not_addOverflow h_no, i64_one_toInt]
      have h_new_acc_toInt : (acc + k).toInt = acc.toInt + k.toInt := by
        have h_no : ¬ Int64.addOverflow acc k := by
          intro hov
          rw [Int64.addOverflow_iff, h63_eq] at hov
          rcases hov with hov | hov
          · omega
          · omega
        exact Int64.toInt_add_of_not_addOverflow h_no
      have h_new_acc_eq : (acc + k).toInt =
          ((k + 1).toInt - 1) * (k + 1).toInt / 2 := by
        rw [h_new_acc_toInt, h_new_k_toInt, h_acc_plus_k]
        congr 1; congr 1; omega
      have h_new_k_lo : 1 ≤ (k + (1 : i64)).toInt := by
        rw [h_new_k_toInt]; omega
      have h_new_k_hi : (k + (1 : i64)).toInt ≤ n.toInt + 1 := by
        rw [h_new_k_toInt]; omega
      have h_new_m : (n.toInt + 1 - (k + (1 : i64)).toInt).toNat = m := by
        rw [h_new_k_toInt]
        have h_eq : n.toInt + 1 - (k.toInt + 1) = n.toInt + 1 - k.toInt - 1 := by ring
        rw [h_eq]
        have h_diff_eq : (n.toInt + 1 - k.toInt) = m + 1 := by
          have h_diff_nn : (0 : Int) ≤ n.toInt + 1 - k.toInt := by omega
          have := Int.toNat_of_nonneg h_diff_nn
          rw [hm] at this
          omega
        rw [h_diff_eq]
        omega
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
  simp only [show (n <? (1 : i64) : RustM Bool) = (pure (decide (n < (1 : i64))) : RustM Bool) from rfl,
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
  simp only [show (n <? (1 : i64) : RustM Bool) = (pure (decide (n < (1 : i64))) : RustM Bool) from rfl,
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
