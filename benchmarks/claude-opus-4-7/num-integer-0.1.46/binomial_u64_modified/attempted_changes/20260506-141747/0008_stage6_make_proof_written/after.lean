-- Companion obligations file for the `binomial_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import binomial_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Binomial_u64Obligations

/-- Mathematical binomial coefficient on `Nat`, defined via Pascal's
    recurrence (no Mathlib in this build, no `Nat.choose` available). -/
private def binomCoeff : Nat → Nat → Nat
  | _,     0     => 1
  | 0,     _ + 1 => 0
  | n + 1, k + 1 => binomCoeff n k + binomCoeff n (k + 1)

/-! ### Helper lemmas -/

/-- For any `n : u64`, `0 > n` is false (decide form). -/
private theorem zero_gt_u64_false (n : u64) : decide ((0 : u64) > n) = false := by
  rw [decide_eq_false_iff_not]
  intro h
  have hlt : n.toNat < (0 : u64).toNat := UInt64.lt_iff_toNat_lt.mp h
  simp at hlt

/-- General `a -? b = pure (a - b)` when no underflow. -/
private theorem sub_no_underflow (a b : u64) (h : b.toNat ≤ a.toNat) :
    (a -? b : RustM u64) = pure (a - b) := by
  have h_no : BitVec.usubOverflow a.toBitVec b.toBitVec = false := by
    show UInt64.subOverflow a b = false
    generalize hb : UInt64.subOverflow a b = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso; rw [UInt64.subOverflow_iff] at hb; omega
  show (rust_primitives.ops.arith.Sub.sub a b : RustM u64) = pure (a - b)
  show (if BitVec.usubOverflow a.toBitVec b.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (a - b)) = pure (a - b)
  rw [h_no]
  rfl

/-- For any `n : u64`, `n -? 0 = pure n`. -/
private theorem n_sub_zero (n : u64) : (n -? (0 : u64) : RustM u64) = pure n := by
  rw [sub_no_underflow n 0 (by simp)]
  have hn0 : n - 0 = n := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le' (by simp : (0 : u64).toNat ≤ n.toNat)]
    simp
  rw [hn0]

/-- For any `n : u64`, `n -? n = pure 0`. -/
private theorem n_sub_n (n : u64) : (n -? n : RustM u64) = pure 0 := by
  rw [sub_no_underflow n n (Nat.le_refl _)]
  have hnn : n - n = (0 : u64) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le' (Nat.le_refl _)]
    simp
  rw [hnn]

/-- `binomial_iter` returns `pure r` when `d > k`. -/
private theorem binomial_iter_done (r n d k : u64) (h : d > k) :
    binomial_u64.binomial_iter r n d k = RustM.ok r := by
  unfold binomial_u64.binomial_iter
  have h_dec : decide (d > k) = true := decide_eq_true_iff.mpr h
  simp only [rust_primitives.cmp.gt, h_dec, pure_bind, ↓reduceIte]
  rfl

/-! ### Postcondition theorems -/

/-- Postcondition (out-of-range): when `k > n`, `binomial n k = ok 0`. -/
theorem binomial_zero_when_k_gt_n (n k : u64) (h : k > n) :
    binomial_u64.binomial n k = RustM.ok (0 : u64) := by
  unfold binomial_u64.binomial
  have h_dec : decide (k > n) = true := decide_eq_true_iff.mpr h
  simp only [rust_primitives.cmp.gt, h_dec, pure_bind, ↓reduceIte]
  rfl

/-- Postcondition (boundary at `k = 0`): `binomial n 0 = ok 1`. -/
theorem binomial_k_zero (n : u64) :
    binomial_u64.binomial n 0 = RustM.ok (1 : u64) := by
  unfold binomial_u64.binomial
  -- (0 >? n) = pure false → take else branch
  simp only [rust_primitives.cmp.gt, zero_gt_u64_false, pure_bind,
             Bool.false_eq_true, ↓reduceIte]
  -- n -? 0 = pure n
  rw [n_sub_zero]
  simp only [pure_bind]
  -- (0 >? n) = pure false → take else branch
  simp only [rust_primitives.cmp.gt, zero_gt_u64_false, pure_bind,
             Bool.false_eq_true, ↓reduceIte]
  -- binomial_iter 1 n 1 0 with 1 > 0
  exact binomial_iter_done 1 n 1 0 (by decide)

/-- Postcondition (boundary at `k = n`): `binomial n n = ok 1`. -/
theorem binomial_n_n (n : u64) :
    binomial_u64.binomial n n = RustM.ok (1 : u64) := by
  unfold binomial_u64.binomial
  -- (n >? n) = pure false → take else branch
  have hnn : decide (n > n) = false := by
    rw [decide_eq_false_iff_not]
    intro h
    have : n.toNat < n.toNat := UInt64.lt_iff_toNat_lt.mp h
    omega
  simp only [rust_primitives.cmp.gt, hnn, pure_bind,
             Bool.false_eq_true, ↓reduceIte]
  -- n -? n = pure 0
  rw [n_sub_n]
  simp only [pure_bind]
  -- Split on n = 0 or n > 0
  by_cases hn0 : n = 0
  · -- n = 0: (0 >? 0) = false, then binomial_iter 1 0 1 0 with 1 > 0
    rw [hn0]
    have hgt : decide ((0 : u64) > (0 : u64)) = false := by decide
    simp only [rust_primitives.cmp.gt, hgt, pure_bind,
               Bool.false_eq_true, ↓reduceIte]
    exact binomial_iter_done 1 0 1 0 (by decide)
  · -- n > 0: (n >? 0) = true, recurse into binomial n 0
    have hpos : n > 0 := by
      have hne : n.toNat ≠ 0 := by
        intro h
        apply hn0
        apply UInt64.toNat_inj.mp
        simp; exact h
      have h_pos : (0 : u64).toNat < n.toNat := by simp; omega
      exact UInt64.lt_iff_toNat_lt.mpr h_pos
    have h_dec : decide (n > 0) = true := decide_eq_true_iff.mpr hpos
    simp only [rust_primitives.cmp.gt, h_dec, pure_bind, ↓reduceIte]
    exact binomial_k_zero n

/-- Helper: `n - (n - k) = k` when `k ≤ n` for `u64`. -/
private theorem n_sub_n_sub_k (n k : u64) (hkn : k.toNat ≤ n.toNat) :
    n - (n - k) = k := by
  apply UInt64.toNat_inj.mp
  have h1 : (n - k).toNat = n.toNat - k.toNat :=
    UInt64.toNat_sub_of_le' hkn
  rw [UInt64.toNat_sub_of_le' (by rw [h1]; omega)]
  rw [h1]
  omega

/-- Postcondition (symmetry in `k`): `binomial n k = binomial n (n - k)`
    for `k ≤ n ≤ 67`. The proof unfolds whichever side performs the
    `k > n - k` recursion: in the `k > n - k` case, LHS unfolds; in the
    `k < n - k` case, RHS unfolds; in the equal case, `k = n - k`. -/
theorem binomial_symmetry (n k : u64)
    (hkn : k ≤ n) (hn : n.toNat ≤ 67) :
    binomial_u64.binomial n k = binomial_u64.binomial n (n - k) := by
  -- Convert `k ≤ n` to a `Nat` form for sub.
  have hkn_nat : k.toNat ≤ n.toNat := UInt64.le_iff_toNat_le.mp hkn
  have hsub_toNat : (n - k).toNat = n.toNat - k.toNat :=
    UInt64.toNat_sub_of_le' hkn_nat
  rcases Nat.lt_trichotomy k.toNat (n - k).toNat with hlt | heq | hgt
  · -- k < n - k: unfold RHS once.
    conv => rhs; unfold binomial_u64.binomial
    have h_nk_le_n : (n - k).toNat ≤ n.toNat := by rw [hsub_toNat]; omega
    have h_nk_le_n_u : n - k ≤ n := UInt64.le_iff_toNat_le.mpr h_nk_le_n
    have h1 : decide ((n - k) > n) = false := by
      rw [decide_eq_false_iff_not]
      intro hh
      have : n.toNat < (n - k).toNat := UInt64.lt_iff_toNat_lt.mp hh
      omega
    simp only [rust_primitives.cmp.gt, h1, pure_bind,
               Bool.false_eq_true, ↓reduceIte]
    -- n -? (n - k) = pure k
    have h_n_sub : (n -? (n - k) : RustM u64) = pure k := by
      rw [sub_no_underflow n (n - k) h_nk_le_n]
      rw [n_sub_n_sub_k n k hkn_nat]
    rw [h_n_sub]
    simp only [pure_bind]
    have hgt_nk : (n - k) > k := UInt64.lt_iff_toNat_lt.mpr hlt
    have h_dec : decide ((n - k) > k) = true := decide_eq_true_iff.mpr hgt_nk
    simp only [rust_primitives.cmp.gt, h_dec, pure_bind, ↓reduceIte]
  · -- k = n - k
    have heq_u : k = n - k := by
      apply UInt64.toNat_inj.mp
      rw [hsub_toNat]; omega
    rw [← heq_u]
  · -- k > n - k: unfold LHS once.
    conv => lhs; unfold binomial_u64.binomial
    have h1 : decide (k > n) = by
        exact decide (k > n) := rfl
    have h1' : decide (k > n) = false := by
      rw [decide_eq_false_iff_not]
      intro hh
      have : n.toNat < k.toNat := UInt64.lt_iff_toNat_lt.mp hh
      omega
    simp only [rust_primitives.cmp.gt, h1', pure_bind,
               Bool.false_eq_true, ↓reduceIte]
    rw [sub_no_underflow n k hkn_nat]
    simp only [pure_bind]
    have hgt_u : k > (n - k) := UInt64.lt_iff_toNat_lt.mpr hgt
    have h_dec : decide (k > (n - k)) = true := decide_eq_true_iff.mpr hgt_u
    simp only [rust_primitives.cmp.gt, h_dec, pure_bind, ↓reduceIte]

/-- Postcondition (Pascal's recurrence). Left as `sorry` — see file footer. -/
theorem binomial_pascal_recurrence (n k : u64)
    (hk : 1 ≤ k.toNat) (hkn : k.toNat ≤ n.toNat) (hn : n.toNat ≤ 50) :
    binomial_u64.binomial n k =
      (do
        let a ← binomial_u64.binomial (n - 1) (k - 1)
        let b ← binomial_u64.binomial (n - 1) k
        a +? b) := by
  sorry

/-- Postcondition (functional correctness). Left as `sorry` — see file footer. -/
theorem binomial_value (n k : u64) (h : n.toNat ≤ 67) :
    binomial_u64.binomial n k =
      RustM.ok (UInt64.ofNat (binomCoeff n.toNat k.toNat)) := by
  sorry

end Binomial_u64Obligations
