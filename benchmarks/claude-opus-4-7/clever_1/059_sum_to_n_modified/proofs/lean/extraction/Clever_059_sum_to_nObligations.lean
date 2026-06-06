-- Companion obligations file for the `clever_059_sum_to_n` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_059_sum_to_n

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_059_sum_to_nObligations

/-! ## u64 ⇄ Nat bridge helpers -/

private theorem u64_zero_toNat : ((0 : u64).toNat) = 0 := rfl
private theorem u64_one_toNat  : ((1 : u64).toNat) = 1 := rfl

/-- Bridge `UInt64.ofNat x` toNat for `x < 2^64`. -/
private theorem u64_ofNat_toNat_of_lt (x : Nat) (h : x < 2 ^ 64) :
    (UInt64.ofNat x).toNat = x := by
  simp [UInt64.toNat, UInt64.ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-! ## Zero boundary -/

theorem sum_to_n_zero :
    clever_059_sum_to_n.sum_to_n 0 = RustM.ok 0 := by
  unfold clever_059_sum_to_n.sum_to_n
  simp only [show ((0 : u64) ==? (0 : u64)) =
                 (pure (decide ((0 : u64) = (0 : u64))) : RustM Bool) from rfl,
             pure_bind, decide_true, ↓reduceIte]
  rfl

/-! ## Branch lemmas for `sum_to_n_at` -/

/-- Base branch: when `k.toNat > n.toNat`, the function returns `pure acc`. -/
private theorem sum_to_n_at_base (n k acc : u64) (h : k.toNat > n.toNat) :
    clever_059_sum_to_n.sum_to_n_at n k acc = RustM.ok acc := by
  unfold clever_059_sum_to_n.sum_to_n_at
  have h_gt : k > n := UInt64.lt_iff_toNat_lt.mpr h
  have h_dec : decide (k > n) = true := decide_eq_true h_gt
  simp only [show (k >? n : RustM Bool) = (pure (decide (k > n)) : RustM Bool) from rfl,
             h_dec, pure_bind, ↓reduceIte]
  rfl

/-- Recursive step: when `k.toNat ≤ n.toNat`, `k + 1` fits, and `acc + k` fits,
    the function delegates to the recursive call with the updated arguments. -/
private theorem sum_to_n_at_recurse (n k acc : u64)
    (h_le : k.toNat ≤ n.toNat)
    (h_k_fit_hi : k.toNat + 1 < 2 ^ 64)
    (h_acc_fit_hi : acc.toNat + k.toNat < 2 ^ 64) :
    clever_059_sum_to_n.sum_to_n_at n k acc =
      clever_059_sum_to_n.sum_to_n_at n (k + 1) (acc + k) := by
  conv => lhs; unfold clever_059_sum_to_n.sum_to_n_at
  have h_not_gt : ¬ k > n := by
    intro hgt
    have := UInt64.lt_iff_toNat_lt.mp hgt
    omega
  have h_dec : decide (k > n) = false := decide_eq_false h_not_gt
  simp only [show (k >? n : RustM Bool) = (pure (decide (k > n)) : RustM Bool) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
  -- Reduce k +? 1.
  have h_no_add_k : ¬ UInt64.addOverflow k (1 : u64) := by
    rw [UInt64.addOverflow_iff, u64_one_toNat]; omega
  have h_bv_k : BitVec.uaddOverflow k.toBitVec (1 : u64).toBitVec = false := by
    cases hb : BitVec.uaddOverflow k.toBitVec (1 : u64).toBitVec with
    | false => rfl
    | true => exact absurd hb h_no_add_k
  have h_k_plus : (k +? (1 : u64) : RustM u64) = pure (k + 1) := by
    show (rust_primitives.ops.arith.Add.add k 1 : RustM u64) = pure (k + 1)
    show (if BitVec.uaddOverflow k.toBitVec (1 : u64).toBitVec then
            (.fail .integerOverflow : RustM u64)
          else pure (k + 1)) = pure (k + 1)
    rw [h_bv_k]; rfl
  rw [h_k_plus]
  simp only [pure_bind]
  -- Reduce acc +? k.
  have h_no_add_acc : ¬ UInt64.addOverflow acc k := by
    rw [UInt64.addOverflow_iff]; omega
  have h_bv_acc : BitVec.uaddOverflow acc.toBitVec k.toBitVec = false := by
    cases hb : BitVec.uaddOverflow acc.toBitVec k.toBitVec with
    | false => rfl
    | true => exact absurd hb h_no_add_acc
  have h_acc_plus : (acc +? k : RustM u64) = pure (acc + k) := by
    show (rust_primitives.ops.arith.Add.add acc k : RustM u64) = pure (acc + k)
    show (if BitVec.uaddOverflow acc.toBitVec k.toBitVec then
            (.fail .integerOverflow : RustM u64)
          else pure (acc + k)) = pure (acc + k)
    rw [h_bv_acc]; rfl
  rw [h_acc_plus]
  simp only [pure_bind]

/-- Overflow on `acc + k`: when `k.toNat ≤ n.toNat`, `k + 1` fits, and
    `acc.toNat + k.toNat ≥ 2^64`, the function panics with integer overflow. -/
private theorem sum_to_n_at_overflow_pos (n k acc : u64)
    (h_le : k.toNat ≤ n.toNat)
    (h_k_fit_hi : k.toNat + 1 < 2 ^ 64)
    (h_acc_overflow : 2 ^ 64 ≤ acc.toNat + k.toNat) :
    clever_059_sum_to_n.sum_to_n_at n k acc = RustM.fail .integerOverflow := by
  conv => lhs; unfold clever_059_sum_to_n.sum_to_n_at
  have h_not_gt : ¬ k > n := by
    intro hgt
    have := UInt64.lt_iff_toNat_lt.mp hgt
    omega
  have h_dec : decide (k > n) = false := decide_eq_false h_not_gt
  simp only [show (k >? n : RustM Bool) = (pure (decide (k > n)) : RustM Bool) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
  -- Reduce k +? 1.
  have h_no_add_k : ¬ UInt64.addOverflow k (1 : u64) := by
    rw [UInt64.addOverflow_iff, u64_one_toNat]; omega
  have h_bv_k : BitVec.uaddOverflow k.toBitVec (1 : u64).toBitVec = false := by
    cases hb : BitVec.uaddOverflow k.toBitVec (1 : u64).toBitVec with
    | false => rfl
    | true => exact absurd hb h_no_add_k
  have h_k_plus : (k +? (1 : u64) : RustM u64) = pure (k + 1) := by
    show (rust_primitives.ops.arith.Add.add k 1 : RustM u64) = pure (k + 1)
    show (if BitVec.uaddOverflow k.toBitVec (1 : u64).toBitVec then
            (.fail .integerOverflow : RustM u64)
          else pure (k + 1)) = pure (k + 1)
    rw [h_bv_k]; rfl
  rw [h_k_plus]
  simp only [pure_bind]
  -- Overflow on acc +? k.
  have h_add_acc : UInt64.addOverflow acc k := by
    rw [UInt64.addOverflow_iff]; exact h_acc_overflow
  have h_bv_acc : BitVec.uaddOverflow acc.toBitVec k.toBitVec = true := h_add_acc
  have h_acc_plus : (acc +? k : RustM u64) = RustM.fail .integerOverflow := by
    show (rust_primitives.ops.arith.Add.add acc k : RustM u64) = RustM.fail .integerOverflow
    show (if BitVec.uaddOverflow acc.toBitVec k.toBitVec then
            (.fail .integerOverflow : RustM u64)
          else pure (acc + k)) = RustM.fail .integerOverflow
    rw [h_bv_acc]; rfl
  rw [h_acc_plus]
  rfl

/-! ## Algebraic helpers: Gauss step on Nat. -/

private theorem gauss_step_nat (k : Nat) (hk : 1 ≤ k) :
    (k - 1) * k / 2 + k = k * (k + 1) / 2 := by
  have e1 : (k - 1) * k + 2 * k = k * (k + 1) := by
    rw [← Nat.add_mul]
    have hsucc : k - 1 + 2 = k + 1 := by omega
    rw [hsucc, Nat.mul_comm]
  have e2 : ((k - 1) * k + 2 * k) / 2 = (k - 1) * k / 2 + k :=
    Nat.add_mul_div_left ((k - 1) * k) k (by decide : 0 < 2)
  rw [← e1, e2]

/-! ## Bound on `k` from the accumulator invariant. -/

/-- If `(k-1)*k/2 < 2^64` and `1 ≤ k`, then `k ≤ 2^33` — small enough that
    `k + 1 < 2^64` cannot overflow. -/
private theorem k_bound_of_acc_inv (k : Nat) (hk_lo : 1 ≤ k)
    (hk_acc_lt : (k - 1) * k / 2 < 2 ^ 64) :
    k ≤ 2 ^ 33 := by
  rcases Nat.lt_or_ge (2 ^ 33) k with h | h
  · exfalso
    have h_k_ge : (2 : Nat) ^ 33 + 1 ≤ k := h
    have h_km1_ge : (2 : Nat) ^ 33 ≤ k - 1 := by omega
    have h_prod : (2 : Nat) ^ 33 * (2 ^ 33 + 1) ≤ (k - 1) * k :=
      Nat.mul_le_mul h_km1_ge h_k_ge
    have h_pow : (2 ^ 33 : Nat) * (2 ^ 33 + 1) = 2 ^ 66 + 2 ^ 33 := by decide
    rw [h_pow] at h_prod
    have h_div : (2 ^ 66 + 2 ^ 33 : Nat) / 2 ≤ (k - 1) * k / 2 :=
      Nat.div_le_div_right h_prod
    have h_half : ((2 ^ 66 + 2 ^ 33 : Nat)) / 2 = 2 ^ 65 + 2 ^ 32 := by decide
    rw [h_half] at h_div
    have h_pow_lt : (2 ^ 64 : Nat) ≤ 2 ^ 65 + 2 ^ 32 := by decide
    omega
  · exact h

/-! ## Main characterization lemma

Strong induction on `(n.toNat + 1 - k.toNat)`. -/

private theorem sum_to_n_at_correct (n : u64) (hn_pos : 1 ≤ n.toNat) :
    ∀ (m : Nat) (k acc : u64),
      1 ≤ k.toNat → k.toNat ≤ n.toNat + 1 →
      acc.toNat = (k.toNat - 1) * k.toNat / 2 →
      n.toNat + 1 - k.toNat = m →
      (if n.toNat * (n.toNat + 1) / 2 < 2 ^ 64 then
        clever_059_sum_to_n.sum_to_n_at n k acc
          = RustM.ok (UInt64.ofNat (n.toNat * (n.toNat + 1) / 2))
       else
        clever_059_sum_to_n.sum_to_n_at n k acc = RustM.fail .integerOverflow) := by
  intro m
  induction m with
  | zero =>
    intro k acc hk_lo hk_hi hacc hm
    -- Force k = n+1 from `(n+1 - k) = 0` and `k ≤ n+1`
    have hk_eq : k.toNat = n.toNat + 1 := by omega
    have h_gt : k.toNat > n.toNat := by omega
    -- acc.toNat = n*(n+1)/2 follows from substitution.
    have h_acc_at_end : acc.toNat = n.toNat * (n.toNat + 1) / 2 := by
      rw [hacc, hk_eq]
      have : n.toNat + 1 - 1 = n.toNat := by omega
      rw [this]
    by_cases hfit : n.toNat * (n.toNat + 1) / 2 < 2 ^ 64
    · rw [if_pos hfit]
      rw [sum_to_n_at_base n k acc h_gt]
      congr 1
      apply UInt64.toNat_inj.mp
      rw [u64_ofNat_toNat_of_lt _ hfit]
      exact h_acc_at_end
    · rw [if_neg hfit]
      exfalso
      have h_acc_lt : acc.toNat < 2 ^ 64 := acc.toNat_lt
      rw [h_acc_at_end] at h_acc_lt
      omega
  | succ m ih =>
    intro k acc hk_lo hk_hi hacc hm
    -- m+1 ≥ 1 forces n+1 - k ≥ 1, i.e., k ≤ n.
    have hk_le_n : k.toNat ≤ n.toNat := by omega
    -- Bound on k from invariant
    have h_acc_lt : acc.toNat < 2 ^ 64 := acc.toNat_lt
    rw [hacc] at h_acc_lt
    have hk_bound_33 : k.toNat ≤ 2 ^ 33 := k_bound_of_acc_inv k.toNat hk_lo h_acc_lt
    have hk_fit_hi : k.toNat + 1 < 2 ^ 64 := by
      have : (2 ^ 33 : Nat) + 1 < 2 ^ 64 := by decide
      omega
    -- acc + k = k*(k+1)/2 via Gauss step
    have h_acc_plus_k : acc.toNat + k.toNat = k.toNat * (k.toNat + 1) / 2 := by
      rw [hacc]; exact gauss_step_nat k.toNat hk_lo
    -- Case-split on overflow at this step
    by_cases hov_step : 2 ^ 64 ≤ acc.toNat + k.toNat
    · -- This step overflows
      have h_total_overflow : 2 ^ 64 ≤ n.toNat * (n.toNat + 1) / 2 := by
        have h_mul_le : k.toNat * (k.toNat + 1) ≤ n.toNat * (n.toNat + 1) :=
          Nat.mul_le_mul hk_le_n (by omega)
        have h_div_le : k.toNat * (k.toNat + 1) / 2 ≤ n.toNat * (n.toNat + 1) / 2 :=
          Nat.div_le_div_right h_mul_le
        omega
      have h_not_fit : ¬ n.toNat * (n.toNat + 1) / 2 < 2 ^ 64 := by omega
      rw [if_neg h_not_fit]
      exact sum_to_n_at_overflow_pos n k acc hk_le_n hk_fit_hi hov_step
    · -- This step does not overflow
      have hov_step' : acc.toNat + k.toNat < 2 ^ 64 := by omega
      -- Apply recurse step
      rw [sum_to_n_at_recurse n k acc hk_le_n hk_fit_hi hov_step']
      -- Apply IH with k' = k + 1, acc' = acc + k
      have h_new_k_toNat : (k + (1 : u64)).toNat = k.toNat + 1 := by
        rw [UInt64.toNat_add_of_lt (by rw [u64_one_toNat]; exact hk_fit_hi), u64_one_toNat]
      have h_new_acc_toNat : (acc + k).toNat = acc.toNat + k.toNat :=
        UInt64.toNat_add_of_lt hov_step'
      have h_new_acc_eq : (acc + k).toNat =
          ((k + 1).toNat - 1) * (k + 1).toNat / 2 := by
        rw [h_new_acc_toNat, h_new_k_toNat, h_acc_plus_k,
            Nat.add_sub_cancel]
      have h_new_k_lo : 1 ≤ (k + (1 : u64)).toNat := by
        rw [h_new_k_toNat]; omega
      have h_new_k_hi : (k + (1 : u64)).toNat ≤ n.toNat + 1 := by
        rw [h_new_k_toNat]; omega
      have h_new_m : n.toNat + 1 - (k + (1 : u64)).toNat = m := by
        rw [h_new_k_toNat]
        omega
      exact ih (k + 1) (acc + k) h_new_k_lo h_new_k_hi h_new_acc_eq h_new_m

/-! ## Top-level theorems -/

theorem sum_to_n_closed_form (n : u64)
    (h : n.toNat * (n.toNat + 1) / 2 < 2 ^ 64) :
    clever_059_sum_to_n.sum_to_n n
      = RustM.ok (UInt64.ofNat (n.toNat * (n.toNat + 1) / 2)) := by
  by_cases hn0 : n.toNat = 0
  · -- n = 0 case: result is 0; closed form is also 0.
    have hn_eq : n = 0 := UInt64.toNat_inj.mp (by rw [hn0]; rfl)
    subst hn_eq
    rw [sum_to_n_zero]
    rfl
  · -- n > 0 case: dispatch to the helper.
    have hn_pos : 1 ≤ n.toNat := Nat.one_le_iff_ne_zero.mpr hn0
    unfold clever_059_sum_to_n.sum_to_n
    have h_ne : ¬ n = 0 := by
      intro hh; apply hn0
      have : n.toNat = (0 : u64).toNat := by rw [hh]
      rw [u64_zero_toNat] at this; exact this
    have h_dec : decide (n = (0 : u64)) = false := decide_eq_false h_ne
    simp only [show (n ==? (0 : u64)) =
                   (pure (decide (n = (0 : u64))) : RustM Bool) from rfl,
               h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
    -- Apply the characterization at k = 1, acc = 0.
    have h_inv : (0 : u64).toNat = ((1 : u64).toNat - 1) * (1 : u64).toNat / 2 := by
      rw [u64_zero_toNat, u64_one_toNat]
    have h_k_lo : 1 ≤ (1 : u64).toNat := by rw [u64_one_toNat]; decide
    have h_k_hi : (1 : u64).toNat ≤ n.toNat + 1 := by rw [u64_one_toNat]; omega
    have h_char := sum_to_n_at_correct n hn_pos
                      (n.toNat + 1 - (1 : u64).toNat)
                      (1 : u64) (0 : u64) h_k_lo h_k_hi h_inv rfl
    rw [if_pos h] at h_char
    exact h_char

theorem sum_to_n_overflow (n : u64)
    (h : 2 ^ 64 ≤ n.toNat * (n.toNat + 1) / 2) :
    clever_059_sum_to_n.sum_to_n n = RustM.fail .integerOverflow := by
  -- n must be positive: if n = 0 then closed form is 0 < 2^64, contradicting h.
  have hn_pos : 1 ≤ n.toNat := by
    rcases Nat.eq_zero_or_pos n.toNat with h0 | h0
    · rw [h0] at h; simp at h
    · exact h0
  unfold clever_059_sum_to_n.sum_to_n
  have h_ne : ¬ n = 0 := by
    intro hh
    have : n.toNat = (0 : u64).toNat := by rw [hh]
    rw [u64_zero_toNat] at this; omega
  have h_dec : decide (n = (0 : u64)) = false := decide_eq_false h_ne
  simp only [show (n ==? (0 : u64)) =
                 (pure (decide (n = (0 : u64))) : RustM Bool) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
  -- Apply the characterization at k = 1, acc = 0.
  have h_inv : (0 : u64).toNat = ((1 : u64).toNat - 1) * (1 : u64).toNat / 2 := by
    rw [u64_zero_toNat, u64_one_toNat]
  have h_k_lo : 1 ≤ (1 : u64).toNat := by rw [u64_one_toNat]; decide
  have h_k_hi : (1 : u64).toNat ≤ n.toNat + 1 := by rw [u64_one_toNat]; omega
  have h_char := sum_to_n_at_correct n hn_pos
                    (n.toNat + 1 - (1 : u64).toNat)
                    (1 : u64) (0 : u64) h_k_lo h_k_hi h_inv rfl
  have h_not_fit : ¬ n.toNat * (n.toNat + 1) / 2 < 2 ^ 64 := by omega
  rw [if_neg h_not_fit] at h_char
  exact h_char

end Clever_059_sum_to_nObligations
