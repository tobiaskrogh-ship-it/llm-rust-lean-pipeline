-- Companion obligations file for the `clever_105_f` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_105_f

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_105_fObligations

/-! ## Specification helpers

Standard mathematical factorial used as the oracle for even positions. -/
private def factorial_nat : Nat → Nat
  | 0     => 1
  | k + 1 => (k + 1) * factorial_nat k

private theorem factorial_nat_one : factorial_nat 1 = 1 := rfl
private theorem factorial_nat_two : factorial_nat 2 = 2 := rfl

/-! ## Numeric helpers (u64 ⇄ Nat bridges, port from `clever_095_count_up_to`). -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem u64_zero_toNat : (0 : u64).toNat = 0 := rfl
private theorem u64_one_toNat : (1 : u64).toNat = 1 := rfl
private theorem u64_two_toNat : (2 : u64).toNat = 2 := rfl

private theorem usize_size_eq_2_64 : USize64.size = 2 ^ 64 := by decide
private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide

/-- `d *? d' = pure (d * d')` when `d.toNat * d'.toNat` fits in `u64`. -/
private theorem mul_pure (d d' : u64) (h : d.toNat * d'.toNat < 2 ^ 64) :
    (d *? d' : RustM u64) = pure (d * d') := by
  show (rust_primitives.ops.arith.Mul.mul d d' : RustM u64) = pure (d * d')
  show (if BitVec.umulOverflow d.toBitVec d'.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (d * d')) = _
  have h_no : ¬ UInt64.mulOverflow d d' := by
    rw [UInt64.mulOverflow_iff]; omega
  have h_bv : BitVec.umulOverflow d.toBitVec d'.toBitVec = false := by
    simpa [UInt64.mulOverflow] using h_no
  rw [h_bv]; rfl

/-- `d +? d' = pure (d + d')` when `d.toNat + d'.toNat` fits in `u64`. -/
private theorem add_pure (d d' : u64) (h : d.toNat + d'.toNat < 2 ^ 64) :
    (d +? d' : RustM u64) = pure (d + d') := by
  show (rust_primitives.ops.arith.Add.add d d' : RustM u64) = pure (d + d')
  show (if BitVec.uaddOverflow d.toBitVec d'.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (d + d')) = _
  have h_no : ¬ UInt64.addOverflow d d' := by
    rw [UInt64.addOverflow_iff]; omega
  have h_bv : BitVec.uaddOverflow d.toBitVec d'.toBitVec = false := by
    simpa [UInt64.addOverflow] using h_no
  rw [h_bv]; rfl

/-- `n %? d = pure (n % d)` when `d ≠ 0`. -/
private theorem mod_pure (n d : u64) (h : d ≠ 0) :
    (n %? d : RustM u64) = pure (n % d) := by
  show (rust_primitives.ops.arith.Rem.rem n d : RustM u64) = pure (n % d)
  show (if d = 0 then (.fail .divisionByZero : RustM u64) else pure (n % d)) = _
  rw [if_neg h]

/-- `(d + 1).toNat = d.toNat + 1` when the sum fits. -/
private theorem succ_toNat (d : u64) (h : d.toNat + 1 < 2 ^ 64) :
    (d + 1).toNat = d.toNat + 1 := by
  rw [UInt64.toNat_add_of_lt (by rw [u64_one_toNat]; exact h), u64_one_toNat]

/-- `(d * d').toNat = d.toNat * d'.toNat` when the product fits. -/
private theorem mul_toNat (d d' : u64) (h : d.toNat * d'.toNat < 2 ^ 64) :
    (d * d').toNat = d.toNat * d'.toNat :=
  UInt64.toNat_mul_of_lt h

/-! ## Pure Nat-level upper bounds for factorial and triangular sums.

The proptest bound `n ≤ 20` ensures every intermediate value fits in `u64`. -/

/-- Monotonicity. -/
private theorem factorial_nat_mono : ∀ (a b : Nat), a ≤ b → factorial_nat a ≤ factorial_nat b
  | a, 0, h => by
    have h_a_zero : a = 0 := by omega
    subst h_a_zero
    exact Nat.le_refl _
  | a, b + 1, h => by
    by_cases hab : a ≤ b
    · have ih := factorial_nat_mono a b hab
      show factorial_nat a ≤ (b + 1) * factorial_nat b
      have h1 : factorial_nat b ≤ (b + 1) * factorial_nat b := Nat.le_mul_of_pos_left _ (by omega)
      omega
    · have h_eq : a = b + 1 := by omega
      subst h_eq
      exact Nat.le_refl _

/-- `factorial_nat 20 < 2 ^ 63`. -/
private theorem factorial_nat_20_lt : factorial_nat 20 < 2 ^ 63 := by decide

/-- For `k ≤ 20`, `factorial_nat k < 2 ^ 64`. -/
private theorem factorial_nat_lt_2_64 (k : Nat) (h : k ≤ 20) : factorial_nat k < 2 ^ 64 := by
  have hmono := factorial_nat_mono k 20 h
  have h20 : factorial_nat 20 < 2 ^ 64 := by
    have h63 : factorial_nat 20 < 2 ^ 63 := factorial_nat_20_lt
    have : (2 : Nat) ^ 63 < 2 ^ 64 := by decide
    omega
  omega

/-- Triangular sums `k*(k+1)/2` for `k ≤ 21` are tiny. -/
private theorem triangular_lt_2_64 (k : Nat) (h : k ≤ 21) : k * (k + 1) / 2 < 2 ^ 64 := by
  have h1 : k * (k + 1) ≤ 21 * 22 := Nat.mul_le_mul h (by omega)
  have h2 : k * (k + 1) / 2 ≤ 21 * 22 / 2 :=
    Nat.div_le_div_right h1
  have : (21 * 22 : Nat) / 2 < 2 ^ 64 := by decide
  omega

/-! ## Branch lemmas for `factorial_at`. -/

/-- Base branch: `cur > k` ⇒ returns `acc`. -/
private theorem factorial_at_base (k cur acc : u64) (h : cur.toNat > k.toNat) :
    clever_105_f.factorial_at k cur acc = RustM.ok acc := by
  unfold clever_105_f.factorial_at
  have h_gt : cur > k := UInt64.lt_iff_toNat_lt.mpr h
  have h_dec : decide (cur > k) = true := decide_eq_true h_gt
  simp only [show (cur >? k : RustM Bool) = pure (decide (cur > k)) from rfl,
             h_dec, pure_bind, ↓reduceIte]
  rfl

/-- Recurse step: `cur ≤ k` and arithmetic fits ⇒ unfold one step. -/
private theorem factorial_at_recurse (k cur acc : u64)
    (h_le : cur.toNat ≤ k.toNat)
    (h_cur_fits : cur.toNat + 1 < 2 ^ 64)
    (h_mul_fits : acc.toNat * cur.toNat < 2 ^ 64) :
    clever_105_f.factorial_at k cur acc =
      clever_105_f.factorial_at k (cur + 1) (acc * cur) := by
  conv => lhs; unfold clever_105_f.factorial_at
  have h_not_gt : ¬ cur > k := by
    intro hgt
    have := UInt64.lt_iff_toNat_lt.mp hgt
    omega
  have h_dec : decide (cur > k) = false := decide_eq_false h_not_gt
  have h_cur_plus : (cur +? (1 : u64) : RustM u64) = pure (cur + 1) :=
    add_pure cur 1 (by rw [u64_one_toNat]; exact h_cur_fits)
  have h_mul : (acc *? cur : RustM u64) = pure (acc * cur) := mul_pure acc cur h_mul_fits
  simp only [show (cur >? k : RustM Bool) = pure (decide (cur > k)) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte,
             h_cur_plus, h_mul]

/-! ## Branch lemmas for `sum_at`. -/

/-- Base branch: `cur > k` ⇒ returns `acc`. -/
private theorem sum_at_base (k cur acc : u64) (h : cur.toNat > k.toNat) :
    clever_105_f.sum_at k cur acc = RustM.ok acc := by
  unfold clever_105_f.sum_at
  have h_gt : cur > k := UInt64.lt_iff_toNat_lt.mpr h
  have h_dec : decide (cur > k) = true := decide_eq_true h_gt
  simp only [show (cur >? k : RustM Bool) = pure (decide (cur > k)) from rfl,
             h_dec, pure_bind, ↓reduceIte]
  rfl

/-- Recurse step. -/
private theorem sum_at_recurse (k cur acc : u64)
    (h_le : cur.toNat ≤ k.toNat)
    (h_cur_fits : cur.toNat + 1 < 2 ^ 64)
    (h_add_fits : acc.toNat + cur.toNat < 2 ^ 64) :
    clever_105_f.sum_at k cur acc =
      clever_105_f.sum_at k (cur + 1) (acc + cur) := by
  conv => lhs; unfold clever_105_f.sum_at
  have h_not_gt : ¬ cur > k := by
    intro hgt
    have := UInt64.lt_iff_toNat_lt.mp hgt
    omega
  have h_dec : decide (cur > k) = false := decide_eq_false h_not_gt
  have h_cur_plus : (cur +? (1 : u64) : RustM u64) = pure (cur + 1) :=
    add_pure cur 1 (by rw [u64_one_toNat]; exact h_cur_fits)
  have h_add : (acc +? cur : RustM u64) = pure (acc + cur) := add_pure acc cur h_add_fits
  simp only [show (cur >? k : RustM Bool) = pure (decide (cur > k)) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte,
             h_cur_plus, h_add]

/-! ## Inner-loop correctness: `factorial_at`. -/

/-- Strong induction on the measure `K + 1 - cur.toNat`. -/
private theorem factorial_at_correct (K : Nat) (hK : K ≤ 20) (k : u64) (hk : k.toNat = K) :
    ∀ (m : Nat) (cur acc : u64),
      1 ≤ cur.toNat →
      cur.toNat ≤ K + 1 →
      acc.toNat = factorial_nat (cur.toNat - 1) →
      K + 1 - cur.toNat ≤ m →
      clever_105_f.factorial_at k cur acc = RustM.ok (UInt64.ofNat (factorial_nat K)) := by
  intro m
  induction m with
  | zero =>
    intro cur acc hcur_lo hcur_hi hacc hm
    -- m = 0 forces cur = K + 1, so cur.toNat > k.toNat.
    have hcur_eq : cur.toNat = K + 1 := by omega
    have hcur_gt : cur.toNat > k.toNat := by rw [hk]; omega
    rw [factorial_at_base k cur acc hcur_gt]
    -- acc.toNat = factorial_nat K
    have hacc_eq : acc.toNat = factorial_nat K := by
      rw [hacc, hcur_eq]
      have h_sub : K + 1 - 1 = K := by omega
      rw [h_sub]
    have h_fit : factorial_nat K < 2 ^ 64 := factorial_nat_lt_2_64 K hK
    congr 1
    apply UInt64.toNat_inj.mp
    rw [hacc_eq, UInt64.toNat_ofNat_of_lt' h_fit]
  | succ m ih =>
    intro cur acc hcur_lo hcur_hi hacc hm
    by_cases hcur_top : cur.toNat = K + 1
    · -- Terminal: same as zero-case.
      have hcur_gt : cur.toNat > k.toNat := by rw [hk]; omega
      rw [factorial_at_base k cur acc hcur_gt]
      have hacc_eq : acc.toNat = factorial_nat K := by
        rw [hacc, hcur_top]
        have h_sub : K + 1 - 1 = K := by omega
        rw [h_sub]
      have h_fit : factorial_nat K < 2 ^ 64 := factorial_nat_lt_2_64 K hK
      congr 1
      apply UInt64.toNat_inj.mp
      rw [hacc_eq, UInt64.toNat_ofNat_of_lt' h_fit]
    · -- Recurse step.
      have hcur_le_K : cur.toNat ≤ K := by omega
      have hcur_le_k : cur.toNat ≤ k.toNat := by rw [hk]; exact hcur_le_K
      have hcur_fits : cur.toNat + 1 < 2 ^ 64 := by
        have : K + 1 < 2 ^ 64 := by omega
        omega
      -- acc * cur fits: acc = factorial_nat (cur - 1), cur ≤ K ≤ 20.
      -- acc * cur ≤ factorial_nat (cur - 1) * cur = factorial_nat cur ≤ factorial_nat 20 < 2^64.
      have h_acc_mul_eq : acc.toNat * cur.toNat = factorial_nat cur.toNat := by
        rw [hacc]
        -- factorial_nat (cur - 1) * cur = factorial_nat cur.
        -- Need cur ≥ 1 so cur = (cur-1) + 1.
        obtain ⟨j, hj⟩ : ∃ j, cur.toNat = j + 1 := ⟨cur.toNat - 1, by omega⟩
        rw [hj]
        show factorial_nat (j + 1 - 1) * (j + 1) = factorial_nat (j + 1)
        have hj_sub : j + 1 - 1 = j := by omega
        rw [hj_sub]
        show factorial_nat j * (j + 1) = (j + 1) * factorial_nat j
        exact Nat.mul_comm _ _
      have h_mul_fits : acc.toNat * cur.toNat < 2 ^ 64 := by
        rw [h_acc_mul_eq]
        have h_cur_le_20 : cur.toNat ≤ 20 := by omega
        exact factorial_nat_lt_2_64 _ h_cur_le_20
      rw [factorial_at_recurse k cur acc hcur_le_k hcur_fits h_mul_fits]
      -- Now apply IH with cur' = cur + 1, acc' = acc * cur.
      have h_cur'_toNat : (cur + 1).toNat = cur.toNat + 1 := succ_toNat cur hcur_fits
      have h_acc'_toNat : (acc * cur).toNat = acc.toNat * cur.toNat := mul_toNat acc cur h_mul_fits
      have h_cur'_lo : 1 ≤ (cur + 1).toNat := by rw [h_cur'_toNat]; omega
      have h_cur'_hi : (cur + 1).toNat ≤ K + 1 := by rw [h_cur'_toNat]; omega
      have h_acc'_eq : (acc * cur).toNat = factorial_nat ((cur + 1).toNat - 1) := by
        rw [h_acc'_toNat, h_acc_mul_eq, h_cur'_toNat]
        have h_sub : cur.toNat + 1 - 1 = cur.toNat := by omega
        rw [h_sub]
      have h_meas : K + 1 - (cur + 1).toNat ≤ m := by rw [h_cur'_toNat]; omega
      exact ih (cur + 1) (acc * cur) h_cur'_lo h_cur'_hi h_acc'_eq h_meas

/-- Top-level wrapper. -/
private theorem factorial_at_one_one (k : u64) (hk : k.toNat ≤ 20) :
    clever_105_f.factorial_at k 1 1 = RustM.ok (UInt64.ofNat (factorial_nat k.toNat)) := by
  apply factorial_at_correct k.toNat hk k rfl (k.toNat + 1 - (1 : u64).toNat) 1 1
  · rw [u64_one_toNat]; exact Nat.le_refl _
  · rw [u64_one_toNat]; omega
  · show (1 : u64).toNat = factorial_nat ((1 : u64).toNat - 1)
    rw [u64_one_toNat]; rfl
  · exact Nat.le_refl _

/-! ## Inner-loop correctness: `sum_at`. -/

/-- Triangular invariant: `(cur - 1) * cur / 2 + cur = cur * (cur + 1) / 2`. -/
private theorem triangular_step (c : Nat) (hc : 1 ≤ c) :
    (c - 1) * c / 2 + c = c * (c + 1) / 2 := by
  obtain ⟨j, hj⟩ : ∃ j, c = j + 1 := ⟨c - 1, by omega⟩
  subst hj
  show (j + 1 - 1) * (j + 1) / 2 + (j + 1) = (j + 1) * (j + 1 + 1) / 2
  have h_sub : j + 1 - 1 = j := by omega
  rw [h_sub]
  -- j * (j + 1) / 2 + (j + 1) = (j + 1) * (j + 2) / 2
  -- (j + 1) * (j + 2) = j * (j + 1) + 2 * (j + 1)
  have he : (j + 1) * (j + 2) = j * (j + 1) + 2 * (j + 1) := by
    have : (j + 1) * (j + 2) = (j + 1) * j + (j + 1) * 2 := Nat.mul_add _ _ _
    rw [this]
    rw [Nat.mul_comm (j + 1) j, Nat.mul_comm (j + 1) 2]
  rw [he]
  -- (j * (j + 1) + 2 * (j + 1)) / 2 = j * (j + 1) / 2 + (j + 1)
  rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2)]

private theorem sum_at_correct (K : Nat) (hK : K ≤ 21) (k : u64) (hk : k.toNat = K) :
    ∀ (m : Nat) (cur acc : u64),
      1 ≤ cur.toNat →
      cur.toNat ≤ K + 1 →
      acc.toNat = (cur.toNat - 1) * cur.toNat / 2 →
      K + 1 - cur.toNat ≤ m →
      clever_105_f.sum_at k cur acc = RustM.ok (UInt64.ofNat (K * (K + 1) / 2)) := by
  intro m
  induction m with
  | zero =>
    intro cur acc hcur_lo hcur_hi hacc hm
    have hcur_eq : cur.toNat = K + 1 := by omega
    have hcur_gt : cur.toNat > k.toNat := by rw [hk]; omega
    rw [sum_at_base k cur acc hcur_gt]
    have hacc_eq : acc.toNat = K * (K + 1) / 2 := by
      rw [hacc, hcur_eq]
      have h_sub : K + 1 - 1 = K := by omega
      rw [h_sub]
    have h_fit : K * (K + 1) / 2 < 2 ^ 64 := triangular_lt_2_64 K hK
    congr 1
    apply UInt64.toNat_inj.mp
    rw [hacc_eq, UInt64.toNat_ofNat_of_lt' h_fit]
  | succ m ih =>
    intro cur acc hcur_lo hcur_hi hacc hm
    by_cases hcur_top : cur.toNat = K + 1
    · have hcur_gt : cur.toNat > k.toNat := by rw [hk]; omega
      rw [sum_at_base k cur acc hcur_gt]
      have hacc_eq : acc.toNat = K * (K + 1) / 2 := by
        rw [hacc, hcur_top]
        have h_sub : K + 1 - 1 = K := by omega
        rw [h_sub]
      have h_fit : K * (K + 1) / 2 < 2 ^ 64 := triangular_lt_2_64 K hK
      congr 1
      apply UInt64.toNat_inj.mp
      rw [hacc_eq, UInt64.toNat_ofNat_of_lt' h_fit]
    · have hcur_le_K : cur.toNat ≤ K := by omega
      have hcur_le_k : cur.toNat ≤ k.toNat := by rw [hk]; exact hcur_le_K
      have hcur_fits : cur.toNat + 1 < 2 ^ 64 := by
        have : K + 1 < 2 ^ 64 := by omega
        omega
      -- acc + cur fits: acc + cur = cur * (cur + 1) / 2 ≤ 21*22/2 = 231 < 2^64.
      have h_acc_add_eq : acc.toNat + cur.toNat = cur.toNat * (cur.toNat + 1) / 2 := by
        rw [hacc]
        exact triangular_step cur.toNat hcur_lo
      have h_add_fits : acc.toNat + cur.toNat < 2 ^ 64 := by
        rw [h_acc_add_eq]
        have h_cur_le_21 : cur.toNat ≤ 21 := by omega
        exact triangular_lt_2_64 _ h_cur_le_21
      rw [sum_at_recurse k cur acc hcur_le_k hcur_fits h_add_fits]
      have h_cur'_toNat : (cur + 1).toNat = cur.toNat + 1 := succ_toNat cur hcur_fits
      have h_acc'_toNat : (acc + cur).toNat = acc.toNat + cur.toNat :=
        UInt64.toNat_add_of_lt h_add_fits
      have h_cur'_lo : 1 ≤ (cur + 1).toNat := by rw [h_cur'_toNat]; omega
      have h_cur'_hi : (cur + 1).toNat ≤ K + 1 := by rw [h_cur'_toNat]; omega
      have h_acc'_eq : (acc + cur).toNat = ((cur + 1).toNat - 1) * (cur + 1).toNat / 2 := by
        rw [h_acc'_toNat, h_acc_add_eq, h_cur'_toNat]
        have h_sub : cur.toNat + 1 - 1 = cur.toNat := by omega
        rw [h_sub]
      have h_meas : K + 1 - (cur + 1).toNat ≤ m := by rw [h_cur'_toNat]; omega
      exact ih (cur + 1) (acc + cur) h_cur'_lo h_cur'_hi h_acc'_eq h_meas

/-- Top-level wrapper. -/
private theorem sum_at_one_zero (k : u64) (hk : k.toNat ≤ 21) :
    clever_105_f.sum_at k 1 0 = RustM.ok (UInt64.ofNat (k.toNat * (k.toNat + 1) / 2)) := by
  apply sum_at_correct k.toNat hk k rfl (k.toNat + 1 - (1 : u64).toNat) 1 0
  · rw [u64_one_toNat]; exact Nat.le_refl _
  · rw [u64_one_toNat]; omega
  · show (0 : u64).toNat = ((1 : u64).toNat - 1) * (1 : u64).toNat / 2
    rw [u64_zero_toNat, u64_one_toNat]
  · exact Nat.le_refl _

/-! ## Push helper for `Vec` (`extend_from_slice` of a 1-element chunk). -/

private def push_one (acc : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec u64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

private theorem push_one_size (acc : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (h : acc.val.size + 1 < USize64.size) :
    (push_one acc x h).val.size = acc.val.size + 1 := by
  show (acc.val ++ #[x]).size = acc.val.size + 1
  rw [Array.size_append]; rfl

/-! ## One-step reductions for `build_at`. -/

/-- OOB: `k > n` ⇒ returns `acc`. -/
private theorem build_at_oob (n k : u64) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (h : n.toNat < k.toNat) :
    clever_105_f.build_at n k acc = RustM.ok acc := by
  conv => lhs; unfold clever_105_f.build_at
  have h_gt : k > n := UInt64.lt_iff_toNat_lt.mpr h
  have h_dec : decide (k > n) = true := decide_eq_true h_gt
  simp only [show (k >? n : RustM Bool) = pure (decide (k > n)) from rfl,
             h_dec, pure_bind, ↓reduceIte]
  rfl

private theorem k_add_one_eq (k : u64) (h : k.toNat + 1 < 2 ^ 64) :
    (k +? (1 : u64) : RustM u64) = RustM.ok (k + 1) := by
  apply add_pure k 1
  rw [u64_one_toNat]; exact h

/-- Even step: `k ≤ n`, `k ≤ 20`, `k.toNat % 2 = 0`, `acc` has room. -/
private theorem build_at_step_even (n k : u64) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hk : k.toNat ≤ n.toNat) (hk20 : k.toNat ≤ 20) (h_even : k.toNat % 2 = 0)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_105_f.build_at n k acc =
      clever_105_f.build_at n (k + 1)
        (push_one acc (UInt64.ofNat (factorial_nat k.toNat)) h_acc) := by
  conv => lhs; unfold clever_105_f.build_at
  have h_not_gt : ¬ k > n := by
    intro hgt
    have := UInt64.lt_iff_toNat_lt.mp hgt
    omega
  have h_dec : decide (k > n) = false := decide_eq_false h_not_gt
  -- Reduce k %? 2.
  have h_mod : (k %? (2 : u64) : RustM u64) = pure (k % 2) := by
    apply mod_pure
    intro h_eq
    have h_zero : (2 : u64).toNat = 0 := by rw [h_eq]; rfl
    rw [u64_two_toNat] at h_zero
    exact absurd h_zero (by decide)
  have h_eq_def : ((k % 2) ==? (0 : u64) : RustM Bool) =
      pure (decide ((k % 2) = (0 : u64))) := rfl
  have h_mod_zero : (k % 2 : u64) = 0 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_mod, u64_two_toNat, u64_zero_toNat]
    exact h_even
  have h_dec_even : decide ((k % 2) = (0 : u64)) = true := decide_eq_true h_mod_zero
  have h_factorial : clever_105_f.factorial_at k 1 1 =
                       RustM.ok (UInt64.ofNat (factorial_nat k.toNat)) :=
    factorial_at_one_one k hk20
  have h_add_k : (k +? (1 : u64) : RustM u64) = RustM.ok (k + 1) :=
    k_add_one_eq k (by have := n.toNat_lt; omega)
  simp only [show (k >? n : RustM Bool) = pure (decide (k > n)) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte,
             h_mod, h_eq_def, h_dec_even, h_factorial, RustM_ok_bind]
  -- Reduce unsize + extend_from_slice + add.
  rw [show (rust_primitives.unsize
            (RustArray.ofVec #v[UInt64.ofNat (factorial_nat k.toNat)] : RustArray u64 1)
            : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[UInt64.ofNat (factorial_nat k.toNat)], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size :
      acc.val.size + (#[UInt64.ofNat (factorial_nat k.toNat)] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size
    exact h_acc
  rw [show (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
              ⟨#[UInt64.ofNat (factorial_nat k.toNat)], one_lt_usize_size⟩
            : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
        = RustM.ok (push_one acc (UInt64.ofNat (factorial_nat k.toNat)) h_acc) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  simp only [RustM_ok_bind, h_add_k]

/-- Odd step: same as even but uses sum_at. -/
private theorem build_at_step_odd (n k : u64) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hk : k.toNat ≤ n.toNat) (hk21 : k.toNat ≤ 21) (h_odd : k.toNat % 2 = 1)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_105_f.build_at n k acc =
      clever_105_f.build_at n (k + 1)
        (push_one acc (UInt64.ofNat (k.toNat * (k.toNat + 1) / 2)) h_acc) := by
  conv => lhs; unfold clever_105_f.build_at
  have h_not_gt : ¬ k > n := by
    intro hgt
    have := UInt64.lt_iff_toNat_lt.mp hgt
    omega
  have h_dec : decide (k > n) = false := decide_eq_false h_not_gt
  have h_mod : (k %? (2 : u64) : RustM u64) = pure (k % 2) := by
    apply mod_pure
    intro h_eq
    have h_zero : (2 : u64).toNat = 0 := by rw [h_eq]; rfl
    rw [u64_two_toNat] at h_zero
    exact absurd h_zero (by decide)
  have h_eq_def : ((k % 2) ==? (0 : u64) : RustM Bool) =
      pure (decide ((k % 2) = (0 : u64))) := rfl
  have h_mod_ne : (k % 2 : u64) ≠ 0 := by
    intro h_eq
    have h_toNat : (k % 2 : u64).toNat = (0 : u64).toNat := by rw [h_eq]
    rw [UInt64.toNat_mod, u64_two_toNat, u64_zero_toNat] at h_toNat
    omega
  have h_dec_odd : decide ((k % 2) = (0 : u64)) = false := decide_eq_false h_mod_ne
  have h_sum : clever_105_f.sum_at k 1 0 =
                 RustM.ok (UInt64.ofNat (k.toNat * (k.toNat + 1) / 2)) :=
    sum_at_one_zero k hk21
  have h_add_k : (k +? (1 : u64) : RustM u64) = RustM.ok (k + 1) :=
    k_add_one_eq k (by have := n.toNat_lt; omega)
  simp only [show (k >? n : RustM Bool) = pure (decide (k > n)) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte,
             h_mod, h_eq_def, h_dec_odd, h_sum, RustM_ok_bind]
  rw [show (rust_primitives.unsize
            (RustArray.ofVec #v[UInt64.ofNat (k.toNat * (k.toNat + 1) / 2)] : RustArray u64 1)
            : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[UInt64.ofNat (k.toNat * (k.toNat + 1) / 2)], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size :
      acc.val.size +
        (#[UInt64.ofNat (k.toNat * (k.toNat + 1) / 2)] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size
    exact h_acc
  rw [show (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
              ⟨#[UInt64.ofNat (k.toNat * (k.toNat + 1) / 2)], one_lt_usize_size⟩
            : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
        = RustM.ok (push_one acc (UInt64.ofNat (k.toNat * (k.toNat + 1) / 2)) h_acc) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  simp only [RustM_ok_bind, h_add_k]

/-! ## Expected-value oracle and strong-induction over `build_at`. -/

/-- The value at 1-indexed position `i`. -/
private def expected (i : Nat) : Nat :=
  if i % 2 = 0 then factorial_nat i else i * (i + 1) / 2

private theorem build_at_correct (n : u64) (hn : n.toNat ≤ 21) :
    ∀ (m : Nat) (k : u64) (acc : alloc.vec.Vec u64 alloc.alloc.Global),
      n.toNat + 1 - k.toNat ≤ m →
      1 ≤ k.toNat → k.toNat ≤ n.toNat + 1 →
      acc.val.size = k.toNat - 1 →
      (∀ (j : Nat) (hj : j < acc.val.size),
          (acc.val[j]'hj).toNat = expected (j + 1)) →
      ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
        clever_105_f.build_at n k acc = RustM.ok v ∧
        v.val.size = n.toNat ∧
        (∀ (j : Nat) (hj : j < v.val.size),
            (v.val[j]'hj).toNat = expected (j + 1)) := by
  intro m
  induction m with
  | zero =>
    intro k acc hm hk_lo hk_hi h_acc_size h_acc_inv
    -- m = 0 forces k = n + 1.
    have hk_eq : k.toNat = n.toNat + 1 := by omega
    have h_n_lt_k : n.toNat < k.toNat := by omega
    refine ⟨acc, build_at_oob n k acc h_n_lt_k, ?_, ?_⟩
    · rw [h_acc_size, hk_eq]; omega
    · intro j hj
      apply h_acc_inv
  | succ m ih =>
    intro k acc hm hk_lo hk_hi h_acc_size h_acc_inv
    by_cases hk_top : k.toNat = n.toNat + 1
    · have h_n_lt_k : n.toNat < k.toNat := by omega
      refine ⟨acc, build_at_oob n k acc h_n_lt_k, ?_, ?_⟩
      · rw [h_acc_size, hk_top]; omega
      · intro j hj; apply h_acc_inv
    · have hk_le_n : k.toNat ≤ n.toNat := by omega
      have hk_le_21 : k.toNat ≤ 21 := by omega
      have h_acc_succ : acc.val.size + 1 < USize64.size := by
        rw [h_acc_size, usize_size_eq_2_64]
        have : n.toNat < 2 ^ 64 := n.toNat_lt
        omega
      have h_k1_toNat : (k + 1).toNat = k.toNat + 1 := by
        apply succ_toNat
        have hn : n.toNat < 2 ^ 64 := n.toNat_lt
        omega
      have h_k1_lo : 1 ≤ (k + 1).toNat := by rw [h_k1_toNat]; omega
      have h_k1_hi : (k + 1).toNat ≤ n.toNat + 1 := by rw [h_k1_toNat]; omega
      have h_meas : n.toNat + 1 - (k + 1).toNat ≤ m := by rw [h_k1_toNat]; omega
      -- Case-split on parity of k.toNat.
      rcases Nat.mod_two_eq_zero_or_one k.toNat with h_par | h_par
      · -- Even branch.
        have hk_le_20 : k.toNat ≤ 20 := by omega
        have h_step := build_at_step_even n k acc hk_le_n hk_le_20 h_par h_acc_succ
        rw [h_step]
        have h_v_pushed_fits : factorial_nat k.toNat < 2 ^ 64 := factorial_nat_lt_2_64 _ hk_le_20
        have h_v_pushed_toNat :
            (UInt64.ofNat (factorial_nat k.toNat)).toNat = factorial_nat k.toNat :=
          UInt64.toNat_ofNat_of_lt' h_v_pushed_fits
        have h_acc'_size :
            (push_one acc (UInt64.ofNat (factorial_nat k.toNat)) h_acc_succ).val.size
              = (k + 1).toNat - 1 := by
          rw [push_one_size, h_acc_size, h_k1_toNat]
          omega
        have h_acc'_inv : ∀ (j : Nat)
            (hj : j < (push_one acc (UInt64.ofNat (factorial_nat k.toNat)) h_acc_succ).val.size),
            ((push_one acc (UInt64.ofNat (factorial_nat k.toNat)) h_acc_succ).val[j]'hj).toNat
              = expected (j + 1) := by
          intro j hj
          show ((acc.val ++ #[UInt64.ofNat (factorial_nat k.toNat)])[j]'hj).toNat
                = expected (j + 1)
          by_cases hjlt : j < acc.val.size
          · rw [Array.getElem_append_left hjlt]
            exact h_acc_inv j hjlt
          · have h_size_app :
                (acc.val ++ #[UInt64.ofNat (factorial_nat k.toNat)]).size = acc.val.size + 1 := by
              rw [Array.size_append]; rfl
            have hj_in : j < acc.val.size + 1 := by
              have hj' : j < (push_one acc (UInt64.ofNat (factorial_nat k.toNat))
                                h_acc_succ).val.size := hj
              rw [push_one_size] at hj'
              exact hj'
            have hj_eq : j = acc.val.size := by omega
            subst hj_eq
            rw [Array.getElem_append_right (Nat.le_refl _)]
            simp only [Nat.sub_self]
            show ((#[UInt64.ofNat (factorial_nat k.toNat)] : Array u64)[0]).toNat
                  = expected (acc.val.size + 1)
            rw [h_acc_size]
            have h_kk : k.toNat - 1 + 1 = k.toNat := by omega
            rw [h_kk]
            unfold expected
            rw [if_pos h_par]
            exact h_v_pushed_toNat
        exact ih (k + 1) _ h_meas h_k1_lo h_k1_hi h_acc'_size h_acc'_inv
      · -- Odd branch.
        have h_step := build_at_step_odd n k acc hk_le_n hk_le_21 h_par h_acc_succ
        rw [h_step]
        have h_v_pushed_fits : k.toNat * (k.toNat + 1) / 2 < 2 ^ 64 :=
          triangular_lt_2_64 _ hk_le_21
        have h_v_pushed_toNat :
            (UInt64.ofNat (k.toNat * (k.toNat + 1) / 2)).toNat = k.toNat * (k.toNat + 1) / 2 :=
          UInt64.toNat_ofNat_of_lt' h_v_pushed_fits
        have h_acc'_size :
            (push_one acc (UInt64.ofNat (k.toNat * (k.toNat + 1) / 2)) h_acc_succ).val.size
              = (k + 1).toNat - 1 := by
          rw [push_one_size, h_acc_size, h_k1_toNat]
          omega
        have h_acc'_inv : ∀ (j : Nat)
            (hj : j < (push_one acc (UInt64.ofNat (k.toNat * (k.toNat + 1) / 2))
                          h_acc_succ).val.size),
            ((push_one acc (UInt64.ofNat (k.toNat * (k.toNat + 1) / 2))
                h_acc_succ).val[j]'hj).toNat = expected (j + 1) := by
          intro j hj
          show ((acc.val ++ #[UInt64.ofNat (k.toNat * (k.toNat + 1) / 2)])[j]'hj).toNat
                = expected (j + 1)
          by_cases hjlt : j < acc.val.size
          · rw [Array.getElem_append_left hjlt]
            exact h_acc_inv j hjlt
          · have h_size_app :
                (acc.val ++ #[UInt64.ofNat (k.toNat * (k.toNat + 1) / 2)]).size
                  = acc.val.size + 1 := by
              rw [Array.size_append]; rfl
            have hj_in : j < acc.val.size + 1 := by
              have hj' : j < (push_one acc (UInt64.ofNat (k.toNat * (k.toNat + 1) / 2))
                                h_acc_succ).val.size := hj
              rw [push_one_size] at hj'
              exact hj'
            have hj_eq : j = acc.val.size := by omega
            subst hj_eq
            rw [Array.getElem_append_right (Nat.le_refl _)]
            simp only [Nat.sub_self]
            show ((#[UInt64.ofNat (k.toNat * (k.toNat + 1) / 2)] : Array u64)[0]).toNat
                  = expected (acc.val.size + 1)
            rw [h_acc_size]
            have h_kk : k.toNat - 1 + 1 = k.toNat := by omega
            rw [h_kk]
            unfold expected
            have h_odd_neq : k.toNat % 2 ≠ 0 := by omega
            rw [if_neg h_odd_neq]
            exact h_v_pushed_toNat
        exact ih (k + 1) _ h_meas h_k1_lo h_k1_hi h_acc'_size h_acc'_inv

/-! ## Top-level wrapper: `f`. -/

private theorem f_correct (n : u64) (hn : n.toNat ≤ 21) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_105_f.f n = RustM.ok v ∧
      v.val.size = n.toNat ∧
      (∀ (j : Nat) (hj : j < v.val.size),
          (v.val[j]'hj).toNat = expected (j + 1)) := by
  unfold clever_105_f.f
  by_cases hn0 : n.toNat = 0
  · -- n = 0 case.
    have h_n_zero_u : n = (0 : u64) := UInt64.toNat_inj.mp hn0
    have h_eq : ((n ==? (0 : u64)) : RustM Bool) = pure true := by
      show pure (decide (n = (0 : u64))) = pure true
      rw [decide_eq_true h_n_zero_u]
    simp only [h_eq, pure_bind, ↓reduceIte]
    have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                    RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                  RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
    rw [h_new]
    refine ⟨⟨(List.nil).toArray, by grind⟩, rfl, ?_, ?_⟩
    · show (List.nil : List u64).toArray.size = n.toNat
      rw [hn0]; rfl
    · intro j hj
      exfalso
      exact absurd hj (Nat.not_lt_zero j)
  · -- n ≥ 1 case.
    have h_n_ne_zero_u : n ≠ (0 : u64) := by
      intro h
      have : n.toNat = (0 : u64).toNat := by rw [h]
      rw [u64_zero_toNat] at this; omega
    have h_eq : ((n ==? (0 : u64)) : RustM Bool) = pure false := by
      show pure (decide (n = (0 : u64))) = pure false
      rw [decide_eq_false h_n_ne_zero_u]
    simp only [h_eq, pure_bind, Bool.false_eq_true, ↓reduceIte]
    have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                    RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                  RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
    rw [h_new, RustM_ok_bind]
    -- Apply build_at_correct.
    have h_acc0_size : (⟨(List.nil : List u64).toArray, by grind⟩ :
                          alloc.vec.Vec u64 alloc.alloc.Global).val.size = (1 : u64).toNat - 1 := by
      show (List.nil : List u64).toArray.size = (1 : u64).toNat - 1
      rw [u64_one_toNat]; rfl
    have h_acc0_inv :
        ∀ (j : Nat) (hj : j < (⟨(List.nil : List u64).toArray, by grind⟩ :
                                  alloc.vec.Vec u64 alloc.alloc.Global).val.size),
          ((⟨(List.nil : List u64).toArray, by grind⟩ :
              alloc.vec.Vec u64 alloc.alloc.Global).val[j]'hj).toNat = expected (j + 1) := by
      intro j hj
      exfalso
      exact absurd hj (Nat.not_lt_zero j)
    have h_k_lo : 1 ≤ (1 : u64).toNat := by rw [u64_one_toNat]; exact Nat.le_refl _
    have h_k_hi : (1 : u64).toNat ≤ n.toNat + 1 := by rw [u64_one_toNat]; omega
    have h_meas : n.toNat + 1 - (1 : u64).toNat ≤ n.toNat + 1 - (1 : u64).toNat := Nat.le_refl _
    exact build_at_correct n hn (n.toNat + 1 - (1 : u64).toNat) (1 : u64)
            ⟨(List.nil).toArray, by grind⟩ h_meas h_k_lo h_k_hi h_acc0_size h_acc0_inv

/-! ## Boundary clause -/

/-- `f 0` returns the empty `Vec`. -/
theorem f_zero_empty :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_105_f.f (0 : u64) = RustM.ok v ∧ v.val.size = 0 := by
  refine ⟨⟨(List.nil : List u64).toArray, by grind⟩, ?_, rfl⟩
  unfold clever_105_f.f
  have h_eq : (((0 : u64) ==? (0 : u64)) : RustM Bool) = pure true := rfl
  simp only [h_eq, pure_bind, ↓reduceIte]
  rfl

/-! ## Totality. -/

theorem f_total (n : u64) (h : n.toNat ≤ 20) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_105_f.f n = RustM.ok v := by
  obtain ⟨v, hres, _, _⟩ := f_correct n (by omega)
  exact ⟨v, hres⟩

/-! ## Failure infrastructure for `n ≥ 22`.

`f n` fails for `n.toNat ≥ 22` because the iteration reaches `k = 22`
(an even index), where `factorial_at 22 1 1` overflows: it accumulates
`acc = 20!` by `cur = 21`, and then `20! *? 21 = 21! > 2^64` fails.

We use this only to discharge the `f n = ok v` hypothesis in `f_length` /
`f_odd_position_triangular` / `f_even_position_factorial` for `n ≥ 22`. -/

/-- `d *? d' = .fail .integerOverflow` when the product overflows. -/
private theorem mul_fail (d d' : u64) (h : 2 ^ 64 ≤ d.toNat * d'.toNat) :
    (d *? d' : RustM u64) = .fail .integerOverflow := by
  show (rust_primitives.ops.arith.Mul.mul d d' : RustM u64) = .fail .integerOverflow
  show (if BitVec.umulOverflow d.toBitVec d'.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (d * d')) = _
  have h_ov : UInt64.mulOverflow d d' := by
    rw [UInt64.mulOverflow_iff]; exact h
  have h_bv : BitVec.umulOverflow d.toBitVec d'.toBitVec = true := by
    simpa [UInt64.mulOverflow] using h_ov
  rw [h_bv]; rfl

/-- Helper: starting at `(cur=1, acc=1)`, factorial_at iterates and after
    `K` iterations reaches state `(cur=K+1, acc=factorial_nat K)`. -/
private theorem factorial_at_reaches (k : u64) :
    ∀ K : Nat, K ≤ 20 → K + 1 ≤ k.toNat →
    clever_105_f.factorial_at k 1 1 =
      clever_105_f.factorial_at k (UInt64.ofNat (K + 1)) (UInt64.ofNat (factorial_nat K)) := by
  intro K
  induction K with
  | zero =>
    intro _ _
    -- ofNat 1 = 1 and factorial_nat 0 = 1, definitionally.
    rfl
  | succ K ih =>
    intro hK hk_le
    -- IH at K needs K + 1 ≤ k.toNat. We have K + 2 ≤ k.toNat.
    have hK' : K ≤ 20 := by omega
    have hk_le' : K + 1 ≤ k.toNat := by omega
    rw [ih hK' hk_le']
    -- Now show factorial_at k (ofNat (K+1)) (ofNat (factorial_nat K))
    --     = factorial_at k (ofNat (K+2)) (ofNat (factorial_nat (K+1))).
    have h_cur_toNat : (UInt64.ofNat (K + 1) : u64).toNat = K + 1 := by
      apply UInt64.toNat_ofNat_of_lt'
      have h1 : K + 1 ≤ 21 := by omega
      have h2 : (21 : Nat) < 2 ^ 64 := by decide
      have h3 : UInt64.size = 2 ^ 64 := by decide
      omega
    have h_acc_toNat : (UInt64.ofNat (factorial_nat K) : u64).toNat = factorial_nat K := by
      apply UInt64.toNat_ofNat_of_lt'
      exact factorial_nat_lt_2_64 K hK'
    have h_cur_le_k : (UInt64.ofNat (K + 1) : u64).toNat ≤ k.toNat := by
      rw [h_cur_toNat]; omega
    have h_cur_fits : (UInt64.ofNat (K + 1) : u64).toNat + 1 < 2 ^ 64 := by
      rw [h_cur_toNat]
      have : K + 2 < 2 ^ 64 := by
        have : K + 2 ≤ 22 := by omega
        have : (22 : Nat) < 2 ^ 64 := by decide
        omega
      exact this
    have h_mul_fits :
        (UInt64.ofNat (factorial_nat K) : u64).toNat *
          (UInt64.ofNat (K + 1) : u64).toNat < 2 ^ 64 := by
      rw [h_acc_toNat, h_cur_toNat]
      show factorial_nat K * (K + 1) < 2 ^ 64
      have h_eq : factorial_nat K * (K + 1) = factorial_nat (K + 1) := by
        show factorial_nat K * (K + 1) = (K + 1) * factorial_nat K
        exact Nat.mul_comm _ _
      rw [h_eq]
      exact factorial_nat_lt_2_64 (K + 1) hK
    rw [factorial_at_recurse k _ _ h_cur_le_k h_cur_fits h_mul_fits]
    -- Now show: factorial_at k (ofNat(K+1) + 1) (ofNat(factorial_nat K) * ofNat(K+1))
    --        = factorial_at k (ofNat(K+2)) (ofNat(factorial_nat (K+1))).
    have h_cur_succ_eq :
        (UInt64.ofNat (K + 1) : u64) + 1 = UInt64.ofNat (K + 2) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add_of_lt (by rw [u64_one_toNat]; exact h_cur_fits),
          h_cur_toNat, u64_one_toNat]
      have h_22 : (UInt64.ofNat (K + 2) : u64).toNat = K + 2 := by
        apply UInt64.toNat_ofNat_of_lt'
        have h1 : K + 2 ≤ 22 := by omega
        have h2 : (22 : Nat) < 2 ^ 64 := by decide
        have h3 : UInt64.size = 2 ^ 64 := by decide
        omega
      rw [h_22]
    have h_acc_succ_eq :
        (UInt64.ofNat (factorial_nat K) : u64) * (UInt64.ofNat (K + 1) : u64) =
          UInt64.ofNat (factorial_nat (K + 1)) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_mul_of_lt h_mul_fits, h_acc_toNat, h_cur_toNat]
      have h_kp1 : (UInt64.ofNat (factorial_nat (K + 1)) : u64).toNat = factorial_nat (K + 1) := by
        apply UInt64.toNat_ofNat_of_lt'
        exact factorial_nat_lt_2_64 (K + 1) hK
      rw [h_kp1]
      show factorial_nat K * (K + 1) = factorial_nat (K + 1)
      show factorial_nat K * (K + 1) = (K + 1) * factorial_nat K
      exact Nat.mul_comm _ _
    rw [h_cur_succ_eq, h_acc_succ_eq]

/-- At `(cur = 21, acc = factorial_nat 20)` with `k.toNat ≥ 21`, the next
    multiplication `acc * cur = 20! * 21 = 21!` overflows. -/
private theorem factorial_at_21_fails (k : u64) (h : 21 ≤ k.toNat) :
    clever_105_f.factorial_at k (UInt64.ofNat 21) (UInt64.ofNat (factorial_nat 20))
      = .fail .integerOverflow := by
  conv => lhs; unfold clever_105_f.factorial_at
  have h_cur_toNat : (UInt64.ofNat 21 : u64).toNat = 21 := by
    apply UInt64.toNat_ofNat_of_lt'; decide
  have h_acc_toNat : (UInt64.ofNat (factorial_nat 20) : u64).toNat = factorial_nat 20 := by
    apply UInt64.toNat_ofNat_of_lt'
    have h63 : factorial_nat 20 < 2 ^ 63 := factorial_nat_20_lt
    have h64 : (2 : Nat) ^ 63 < 2 ^ 64 := by decide
    have h_size : UInt64.size = 2 ^ 64 := by decide
    omega
  have h_not_gt : ¬ (UInt64.ofNat 21 : u64) > k := by
    intro hgt
    have := UInt64.lt_iff_toNat_lt.mp hgt
    rw [h_cur_toNat] at this
    omega
  have h_dec : decide ((UInt64.ofNat 21 : u64) > k) = false := decide_eq_false h_not_gt
  have h_cur_plus : ((UInt64.ofNat 21 : u64) +? (1 : u64) : RustM u64) =
      RustM.ok (UInt64.ofNat 21 + 1) := by
    apply add_pure
    rw [u64_one_toNat, h_cur_toNat]; decide
  have h_mul_overflow :
      2 ^ 64 ≤ (UInt64.ofNat (factorial_nat 20) : u64).toNat *
                (UInt64.ofNat 21 : u64).toNat := by
    rw [h_acc_toNat, h_cur_toNat]
    show 2 ^ 64 ≤ factorial_nat 20 * 21
    have h_eq : factorial_nat 20 * 21 = 51090942171709440000 := by decide
    rw [h_eq]; decide
  have h_mul_fail :
      ((UInt64.ofNat (factorial_nat 20) : u64) *? (UInt64.ofNat 21 : u64) : RustM u64)
        = .fail .integerOverflow :=
    mul_fail _ _ h_mul_overflow
  simp only [show ((UInt64.ofNat 21 : u64) >? k : RustM Bool)
                = pure (decide ((UInt64.ofNat 21 : u64) > k)) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte,
             h_cur_plus, RustM_ok_bind, h_mul_fail]
  rfl

/-- `factorial_at k 1 1 = fail` whenever `k.toNat ≥ 21`. -/
private theorem factorial_at_one_one_fails (k : u64) (h : 21 ≤ k.toNat) :
    clever_105_f.factorial_at k 1 1 = .fail .integerOverflow := by
  rw [factorial_at_reaches k 20 (Nat.le_refl _) h]
  -- factorial_at k (ofNat 21) (ofNat (factorial_nat 20)) = fail
  exact factorial_at_21_fails k h

/-! ## Build_at fails when n ≥ 22.

We strengthen `build_at_correct` to a "succeed-or-no" variant that, given
the same accumulator invariant, characterises whether `build_at` succeeds
based on whether `k` ever exceeds 21 before reaching the OOB. For
`n.toNat ≥ 22`, the iteration must visit `k = 22` (the first failing
even index), at which factorial_at fails. -/

/-- `build_at n k acc` fails when `k.toNat = 22` and `k.toNat ≤ n.toNat`,
    because `factorial_at 22 1 1 = fail`. -/
private theorem build_at_step_even_fails (n k : u64) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hk_eq : k.toNat = 22) (hk_le : k.toNat ≤ n.toNat) :
    clever_105_f.build_at n k acc = .fail .integerOverflow := by
  conv => lhs; unfold clever_105_f.build_at
  have h_not_gt : ¬ k > n := by
    intro hgt
    have := UInt64.lt_iff_toNat_lt.mp hgt
    omega
  have h_dec : decide (k > n) = false := decide_eq_false h_not_gt
  -- k % 2 = 0
  have h_mod : (k %? (2 : u64) : RustM u64) = pure (k % 2) := by
    apply mod_pure
    intro h_eq
    have h_zero : (2 : u64).toNat = 0 := by rw [h_eq]; rfl
    rw [u64_two_toNat] at h_zero
    exact absurd h_zero (by decide)
  have h_eq_def : ((k % 2) ==? (0 : u64) : RustM Bool) =
      pure (decide ((k % 2) = (0 : u64))) := rfl
  have h_mod_zero : (k % 2 : u64) = 0 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_mod, u64_two_toNat, u64_zero_toNat]
    rw [hk_eq]
  have h_dec_even : decide ((k % 2) = (0 : u64)) = true := decide_eq_true h_mod_zero
  have h_factorial_fails : clever_105_f.factorial_at k 1 1 = .fail .integerOverflow :=
    factorial_at_one_one_fails k (by rw [hk_eq]; decide)
  simp only [show (k >? n : RustM Bool) = pure (decide (k > n)) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte,
             h_mod, h_eq_def, h_dec_even, h_factorial_fails]
  rfl

/-- Reach `k = 22` from `k = 1` when `n.toNat ≥ 22`. We iterate through
    `k = 1, 2, ..., 21` (all of which succeed by the `≤ 21` correctness)
    and at each step build_at recurses with the right invariant. The
    accumulator state at `k = 22` has size 21, but we don't need its
    contents — only that the recursion reaches that point. -/
private theorem build_at_fails_for_n_ge_22 (n : u64) (hn : 22 ≤ n.toNat) :
    ∀ (m : Nat) (k : u64) (acc : alloc.vec.Vec u64 alloc.alloc.Global),
      n.toNat + 1 - k.toNat ≤ m →
      1 ≤ k.toNat → k.toNat ≤ 22 →
      acc.val.size = k.toNat - 1 →
      (∀ (j : Nat) (hj : j < acc.val.size),
          (acc.val[j]'hj).toNat = expected (j + 1)) →
      ∃ e, clever_105_f.build_at n k acc = .fail e := by
  intro m
  induction m with
  | zero =>
    intro k acc hm hk_lo hk_hi h_acc_size h_acc_inv
    -- m = 0: forced k.toNat = n.toNat + 1. But hk_hi ≤ 22 ≤ n.toNat = k.toNat - 1.
    -- Contradiction: 22 ≤ n.toNat and k.toNat ≤ 22 and k.toNat = n.toNat + 1 ≥ 23.
    exfalso
    omega
  | succ m ih =>
    intro k acc hm hk_lo hk_hi h_acc_size h_acc_inv
    by_cases hk22 : k.toNat = 22
    · -- Terminal: at k=22, build_at fails immediately.
      have hk_le_n : k.toNat ≤ n.toNat := by omega
      exact ⟨.integerOverflow, build_at_step_even_fails n k acc hk22 hk_le_n⟩
    · -- k < 22: step once and recurse.
      have hk_lt_22 : k.toNat < 22 := by omega
      have hk_le_n : k.toNat ≤ n.toNat := by omega
      have hk_le_21 : k.toNat ≤ 21 := by omega
      have h_acc_succ : acc.val.size + 1 < USize64.size := by
        rw [h_acc_size, usize_size_eq_2_64]
        have : n.toNat < 2 ^ 64 := n.toNat_lt
        omega
      have h_k1_toNat : (k + 1).toNat = k.toNat + 1 := by
        apply succ_toNat
        have hn' : n.toNat < 2 ^ 64 := n.toNat_lt
        omega
      have h_k1_lo : 1 ≤ (k + 1).toNat := by rw [h_k1_toNat]; omega
      have h_k1_hi : (k + 1).toNat ≤ 22 := by rw [h_k1_toNat]; omega
      have h_meas : n.toNat + 1 - (k + 1).toNat ≤ m := by rw [h_k1_toNat]; omega
      rcases Nat.mod_two_eq_zero_or_one k.toNat with h_par | h_par
      · -- Even branch with k ≤ 20 (since k ≤ 21 and even).
        have hk_le_20 : k.toNat ≤ 20 := by omega
        have h_step := build_at_step_even n k acc hk_le_n hk_le_20 h_par h_acc_succ
        rw [h_step]
        have h_acc'_size :
            (push_one acc (UInt64.ofNat (factorial_nat k.toNat)) h_acc_succ).val.size
              = (k + 1).toNat - 1 := by
          rw [push_one_size, h_acc_size, h_k1_toNat]; omega
        have h_v_pushed_fits : factorial_nat k.toNat < 2 ^ 64 := factorial_nat_lt_2_64 _ hk_le_20
        have h_v_pushed_toNat :
            (UInt64.ofNat (factorial_nat k.toNat)).toNat = factorial_nat k.toNat :=
          UInt64.toNat_ofNat_of_lt' h_v_pushed_fits
        have h_acc'_inv : ∀ (j : Nat)
            (hj : j < (push_one acc (UInt64.ofNat (factorial_nat k.toNat)) h_acc_succ).val.size),
            ((push_one acc (UInt64.ofNat (factorial_nat k.toNat)) h_acc_succ).val[j]'hj).toNat
              = expected (j + 1) := by
          intro j hj
          show ((acc.val ++ #[UInt64.ofNat (factorial_nat k.toNat)])[j]'hj).toNat
                = expected (j + 1)
          by_cases hjlt : j < acc.val.size
          · rw [Array.getElem_append_left hjlt]
            exact h_acc_inv j hjlt
          · have hj_in : j < acc.val.size + 1 := by
              have hj' : j < (push_one acc (UInt64.ofNat (factorial_nat k.toNat))
                                h_acc_succ).val.size := hj
              rw [push_one_size] at hj'
              exact hj'
            have hj_eq : j = acc.val.size := by omega
            subst hj_eq
            rw [Array.getElem_append_right (Nat.le_refl _)]
            simp only [Nat.sub_self]
            show ((#[UInt64.ofNat (factorial_nat k.toNat)] : Array u64)[0]).toNat
                  = expected (acc.val.size + 1)
            rw [h_acc_size]
            have h_kk : k.toNat - 1 + 1 = k.toNat := by omega
            rw [h_kk]
            unfold expected
            rw [if_pos h_par]
            exact h_v_pushed_toNat
        exact ih (k + 1) _ h_meas h_k1_lo h_k1_hi h_acc'_size h_acc'_inv
      · -- Odd branch.
        have h_step := build_at_step_odd n k acc hk_le_n hk_le_21 h_par h_acc_succ
        rw [h_step]
        have h_v_pushed_fits : k.toNat * (k.toNat + 1) / 2 < 2 ^ 64 :=
          triangular_lt_2_64 _ hk_le_21
        have h_v_pushed_toNat :
            (UInt64.ofNat (k.toNat * (k.toNat + 1) / 2)).toNat = k.toNat * (k.toNat + 1) / 2 :=
          UInt64.toNat_ofNat_of_lt' h_v_pushed_fits
        have h_acc'_size :
            (push_one acc (UInt64.ofNat (k.toNat * (k.toNat + 1) / 2)) h_acc_succ).val.size
              = (k + 1).toNat - 1 := by
          rw [push_one_size, h_acc_size, h_k1_toNat]; omega
        have h_acc'_inv : ∀ (j : Nat)
            (hj : j < (push_one acc (UInt64.ofNat (k.toNat * (k.toNat + 1) / 2))
                          h_acc_succ).val.size),
            ((push_one acc (UInt64.ofNat (k.toNat * (k.toNat + 1) / 2))
                h_acc_succ).val[j]'hj).toNat = expected (j + 1) := by
          intro j hj
          show ((acc.val ++ #[UInt64.ofNat (k.toNat * (k.toNat + 1) / 2)])[j]'hj).toNat
                = expected (j + 1)
          by_cases hjlt : j < acc.val.size
          · rw [Array.getElem_append_left hjlt]
            exact h_acc_inv j hjlt
          · have hj_in : j < acc.val.size + 1 := by
              have hj' : j < (push_one acc (UInt64.ofNat (k.toNat * (k.toNat + 1) / 2))
                                h_acc_succ).val.size := hj
              rw [push_one_size] at hj'
              exact hj'
            have hj_eq : j = acc.val.size := by omega
            subst hj_eq
            rw [Array.getElem_append_right (Nat.le_refl _)]
            simp only [Nat.sub_self]
            show ((#[UInt64.ofNat (k.toNat * (k.toNat + 1) / 2)] : Array u64)[0]).toNat
                  = expected (acc.val.size + 1)
            rw [h_acc_size]
            have h_kk : k.toNat - 1 + 1 = k.toNat := by omega
            rw [h_kk]
            unfold expected
            have h_odd_neq : k.toNat % 2 ≠ 0 := by omega
            rw [if_neg h_odd_neq]
            exact h_v_pushed_toNat
        exact ih (k + 1) _ h_meas h_k1_lo h_k1_hi h_acc'_size h_acc'_inv

/-- Top-level: `f n` fails when `n.toNat ≥ 22`. -/
private theorem f_fails_above_21 (n : u64) (hn : 22 ≤ n.toNat) :
    ∀ v : alloc.vec.Vec u64 alloc.alloc.Global, clever_105_f.f n ≠ RustM.ok v := by
  intro v h_eq
  -- Reduce `f n` to `build_at n 1 []`.
  have h_n_ne_zero_u : n ≠ (0 : u64) := by
    intro h
    have : n.toNat = (0 : u64).toNat := by rw [h]
    rw [u64_zero_toNat] at this; omega
  have h_test : ((n ==? (0 : u64)) : RustM Bool) = pure false := by
    show pure (decide (n = (0 : u64))) = pure false
    rw [decide_eq_false h_n_ne_zero_u]
  have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  have h_f_eq : clever_105_f.f n =
      clever_105_f.build_at n 1 ⟨(List.nil).toArray, by grind⟩ := by
    unfold clever_105_f.f
    simp only [h_test, pure_bind, Bool.false_eq_true, ↓reduceIte]
    rw [h_new, RustM_ok_bind]
  rw [h_f_eq] at h_eq
  -- Now use build_at_fails_for_n_ge_22.
  have h_acc0_size : (⟨(List.nil : List u64).toArray, by grind⟩ :
                        alloc.vec.Vec u64 alloc.alloc.Global).val.size = (1 : u64).toNat - 1 := by
    show (List.nil : List u64).toArray.size = (1 : u64).toNat - 1
    rw [u64_one_toNat]; rfl
  have h_acc0_inv :
      ∀ (j : Nat) (hj : j < (⟨(List.nil : List u64).toArray, by grind⟩ :
                                alloc.vec.Vec u64 alloc.alloc.Global).val.size),
        ((⟨(List.nil : List u64).toArray, by grind⟩ :
            alloc.vec.Vec u64 alloc.alloc.Global).val[j]'hj).toNat = expected (j + 1) := by
    intro j hj
    exact absurd hj (Nat.not_lt_zero j)
  have h_k_lo : 1 ≤ (1 : u64).toNat := by rw [u64_one_toNat]; exact Nat.le_refl _
  have h_k_hi : (1 : u64).toNat ≤ 22 := by rw [u64_one_toNat]; omega
  have h_meas : n.toNat + 1 - (1 : u64).toNat ≤ n.toNat + 1 := by omega
  obtain ⟨e, hfail⟩ := build_at_fails_for_n_ge_22 n hn (n.toNat + 1) (1 : u64)
                        ⟨(List.nil).toArray, by grind⟩ h_meas h_k_lo h_k_hi
                        h_acc0_size h_acc0_inv
  rw [hfail] at h_eq
  cases h_eq

theorem f_length
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_105_f.f n = RustM.ok v) :
    v.val.size = n.toNat := by
  by_cases hn : n.toNat ≤ 21
  · obtain ⟨v', hres', hlen, _⟩ := f_correct n hn
    rw [hres'] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    exact hlen
  · exfalso
    have hn' : 22 ≤ n.toNat := by omega
    exact f_fails_above_21 n hn' v hres

theorem f_odd_position_triangular
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_105_f.f n = RustM.ok v)
    (i : Nat) (h_pos : 1 ≤ i) (h_le : i ≤ n.toNat) (h_odd : i % 2 = 1)
    (hi : i - 1 < v.val.size) :
    (v.val[i - 1]'hi).toNat = i * (i + 1) / 2 := by
  by_cases hn : n.toNat ≤ 21
  · obtain ⟨v', hres', _, hinv⟩ := f_correct n hn
    rw [hres'] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    have hinv_at := hinv (i - 1) hi
    have h_succ : i - 1 + 1 = i := by omega
    rw [h_succ] at hinv_at
    rw [hinv_at]
    unfold expected
    have h_odd_neq : i % 2 ≠ 0 := by omega
    rw [if_neg h_odd_neq]
  · exfalso
    have hn' : 22 ≤ n.toNat := by omega
    exact f_fails_above_21 n hn' v hres

theorem f_even_position_factorial
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_105_f.f n = RustM.ok v)
    (i : Nat) (h_pos : 1 ≤ i) (h_le : i ≤ n.toNat) (h_even : i % 2 = 0)
    (hi : i - 1 < v.val.size) :
    (v.val[i - 1]'hi).toNat = factorial_nat i := by
  by_cases hn : n.toNat ≤ 21
  · obtain ⟨v', hres', _, hinv⟩ := f_correct n hn
    rw [hres'] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    have hinv_at := hinv (i - 1) hi
    have h_succ : i - 1 + 1 = i := by omega
    rw [h_succ] at hinv_at
    rw [hinv_at]
    unfold expected
    rw [if_pos h_even]
  · exfalso
    have hn' : 22 ≤ n.toNat := by omega
    exact f_fails_above_21 n hn' v hres

end Clever_105_fObligations
