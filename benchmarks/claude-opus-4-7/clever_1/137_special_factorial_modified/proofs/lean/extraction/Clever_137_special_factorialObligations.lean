-- Companion obligations file for the `clever_137_special_factorial` extraction.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_137_special_factorial

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_137_special_factorialObligations

/-! ## Specification helpers -/

/-- Mathematical factorial on `Nat`, defined locally because core Lean 4
    does not ship a `Nat.factorial` and we have no Mathlib in this build. -/
private def factorial_nat : Nat → Nat
  | 0     => 1
  | k + 1 => (k + 1) * factorial_nat k

/-- Brazilian (`special`) factorial on `Nat`: the running product
    `1! * 2! * ... * n!` with the empty-product convention
    `special_factorial_nat 0 = 1`. Mirrors the Rust test oracle. -/
private def special_factorial_nat : Nat → Nat
  | 0     => 1
  | n + 1 => special_factorial_nat n * factorial_nat (n + 1)

/-! ## Numeric helpers (u64 ⇄ Nat bridges; ported from `clever_105_f`). -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem u64_zero_toNat : (0 : u64).toNat = 0 := rfl
private theorem u64_one_toNat : (1 : u64).toNat = 1 := rfl

/-- Bridges `UInt64.size` with `2 ^ 64` so omega can close numeric fits. -/
private theorem usize_eq_2_64 : UInt64.size = 2 ^ 64 := by decide

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

private theorem succ_toNat (d : u64) (h : d.toNat + 1 < 2 ^ 64) :
    (d + 1).toNat = d.toNat + 1 := by
  rw [UInt64.toNat_add_of_lt (by rw [u64_one_toNat]; exact h), u64_one_toNat]

private theorem mul_toNat (d d' : u64) (h : d.toNat * d'.toNat < 2 ^ 64) :
    (d * d').toNat = d.toNat * d'.toNat :=
  UInt64.toNat_mul_of_lt h

/-! ## Pure Nat-level upper bounds (proved by `decide` since the range is small). -/

private theorem factorial_nat_lt_2_64 : ∀ k, k ≤ 20 → factorial_nat k < 2 ^ 64 := by decide

private theorem sf_nat_lt_2_64 : ∀ n, n ≤ 8 → special_factorial_nat n < 2 ^ 64 := by decide

/-- A single key concrete value: `sf_nat 8 < 2^64`, used in the failure path. -/
private theorem sf_nat_8_lt : special_factorial_nat 8 < 2 ^ 64 := sf_nat_lt_2_64 8 (by decide)

/-! ## Branch lemmas for `factorial_at`. -/

private theorem factorial_at_base (k cur acc : u64) (h : cur.toNat > k.toNat) :
    clever_137_special_factorial.factorial_at k cur acc = RustM.ok acc := by
  unfold clever_137_special_factorial.factorial_at
  have h_gt : cur > k := UInt64.lt_iff_toNat_lt.mpr h
  have h_dec : decide (cur > k) = true := decide_eq_true h_gt
  simp only [show (cur >? k : RustM Bool) = pure (decide (cur > k)) from rfl,
             h_dec, pure_bind, ↓reduceIte]
  rfl

private theorem factorial_at_recurse (k cur acc : u64)
    (h_le : cur.toNat ≤ k.toNat)
    (h_cur_fits : cur.toNat + 1 < 2 ^ 64)
    (h_mul_fits : acc.toNat * cur.toNat < 2 ^ 64) :
    clever_137_special_factorial.factorial_at k cur acc =
      clever_137_special_factorial.factorial_at k (cur + 1) (acc * cur) := by
  conv => lhs; unfold clever_137_special_factorial.factorial_at
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

/-! ## Inner-loop correctness: `factorial_at`. -/

private theorem factorial_at_correct (K : Nat) (hK : K ≤ 20) (k : u64) (hk : k.toNat = K) :
    ∀ (m : Nat) (cur acc : u64),
      1 ≤ cur.toNat →
      cur.toNat ≤ K + 1 →
      acc.toNat = factorial_nat (cur.toNat - 1) →
      K + 1 - cur.toNat ≤ m →
      clever_137_special_factorial.factorial_at k cur acc
        = RustM.ok (UInt64.ofNat (factorial_nat K)) := by
  intro m
  induction m with
  | zero =>
    intro cur acc hcur_lo hcur_hi hacc hm
    have hcur_eq : cur.toNat = K + 1 := by omega
    have hcur_gt : cur.toNat > k.toNat := by rw [hk]; omega
    rw [factorial_at_base k cur acc hcur_gt]
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
    · have hcur_gt : cur.toNat > k.toNat := by rw [hk]; omega
      rw [factorial_at_base k cur acc hcur_gt]
      have hacc_eq : acc.toNat = factorial_nat K := by
        rw [hacc, hcur_top]
        have h_sub : K + 1 - 1 = K := by omega
        rw [h_sub]
      have h_fit : factorial_nat K < 2 ^ 64 := factorial_nat_lt_2_64 K hK
      congr 1
      apply UInt64.toNat_inj.mp
      rw [hacc_eq, UInt64.toNat_ofNat_of_lt' h_fit]
    · have hcur_le_K : cur.toNat ≤ K := by omega
      have hcur_le_k : cur.toNat ≤ k.toNat := by rw [hk]; exact hcur_le_K
      have hcur_fits : cur.toNat + 1 < 2 ^ 64 := by
        have : K + 1 < 2 ^ 64 := by omega
        omega
      have h_acc_mul_eq : acc.toNat * cur.toNat = factorial_nat cur.toNat := by
        rw [hacc]
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
      have h_cur'_toNat : (cur + 1).toNat = cur.toNat + 1 := succ_toNat cur hcur_fits
      have h_acc'_toNat : (acc * cur).toNat = acc.toNat * cur.toNat :=
        mul_toNat acc cur h_mul_fits
      have h_cur'_lo : 1 ≤ (cur + 1).toNat := by rw [h_cur'_toNat]; omega
      have h_cur'_hi : (cur + 1).toNat ≤ K + 1 := by rw [h_cur'_toNat]; omega
      have h_acc'_eq : (acc * cur).toNat = factorial_nat ((cur + 1).toNat - 1) := by
        rw [h_acc'_toNat, h_acc_mul_eq, h_cur'_toNat]
        have h_sub : cur.toNat + 1 - 1 = cur.toNat := by omega
        rw [h_sub]
      have h_meas : K + 1 - (cur + 1).toNat ≤ m := by rw [h_cur'_toNat]; omega
      exact ih (cur + 1) (acc * cur) h_cur'_lo h_cur'_hi h_acc'_eq h_meas

/-- Top-level wrapper: `factorial_at k 1 1 = k!`. -/
private theorem factorial_at_one_one (k : u64) (hk : k.toNat ≤ 20) :
    clever_137_special_factorial.factorial_at k 1 1
      = RustM.ok (UInt64.ofNat (factorial_nat k.toNat)) := by
  apply factorial_at_correct k.toNat hk k rfl (k.toNat + 1 - (1 : u64).toNat) 1 1
  · rw [u64_one_toNat]; exact Nat.le_refl _
  · rw [u64_one_toNat]; omega
  · show (1 : u64).toNat = factorial_nat ((1 : u64).toNat - 1)
    rw [u64_one_toNat]; rfl
  · exact Nat.le_refl _

/-! ## Branch lemmas for `build_at`. -/

private theorem build_at_base (n k acc : u64) (h : k.toNat > n.toNat) :
    clever_137_special_factorial.build_at n k acc = RustM.ok acc := by
  unfold clever_137_special_factorial.build_at
  have h_gt : k > n := UInt64.lt_iff_toNat_lt.mpr h
  have h_dec : decide (k > n) = true := decide_eq_true h_gt
  simp only [show (k >? n : RustM Bool) = pure (decide (k > n)) from rfl,
             h_dec, pure_bind, ↓reduceIte]
  rfl

/-- Recurse step. The acc is multiplied by `UInt64.ofNat (factorial_nat k.toNat)`. -/
private theorem build_at_recurse (n k acc : u64)
    (h_le : k.toNat ≤ n.toNat)
    (h_k20 : k.toNat ≤ 20)
    (h_k_fits : k.toNat + 1 < 2 ^ 64)
    (h_mul_fits : acc.toNat * factorial_nat k.toNat < 2 ^ 64) :
    clever_137_special_factorial.build_at n k acc =
      clever_137_special_factorial.build_at n
        (k + 1)
        (acc * UInt64.ofNat (factorial_nat k.toNat)) := by
  conv => lhs; unfold clever_137_special_factorial.build_at
  have h_not_gt : ¬ k > n := by
    intro hgt
    have := UInt64.lt_iff_toNat_lt.mp hgt
    omega
  have h_dec : decide (k > n) = false := decide_eq_false h_not_gt
  have h_factorial : clever_137_special_factorial.factorial_at k 1 1 =
                       RustM.ok (UInt64.ofNat (factorial_nat k.toNat)) :=
    factorial_at_one_one k h_k20
  have h_fact_fits : factorial_nat k.toNat < 2 ^ 64 := factorial_nat_lt_2_64 _ h_k20
  have h_fact_toNat :
      (UInt64.ofNat (factorial_nat k.toNat) : u64).toNat = factorial_nat k.toNat :=
    UInt64.toNat_ofNat_of_lt' h_fact_fits
  have h_acc_mul : (acc *? UInt64.ofNat (factorial_nat k.toNat) : RustM u64)
      = pure (acc * UInt64.ofNat (factorial_nat k.toNat)) := by
    apply mul_pure
    rw [h_fact_toNat]; exact h_mul_fits
  have h_k_plus : (k +? (1 : u64) : RustM u64) = pure (k + 1) :=
    add_pure k 1 (by rw [u64_one_toNat]; exact h_k_fits)
  simp only [show (k >? n : RustM Bool) = pure (decide (k > n)) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte,
             h_factorial, RustM_ok_bind, h_acc_mul, h_k_plus]

/-! ## Outer-loop correctness: `build_at` (for n ≤ 8). -/

private theorem build_at_correct (N : Nat) (hN : N ≤ 8) (n : u64) (hn : n.toNat = N) :
    ∀ (m : Nat) (k acc : u64),
      1 ≤ k.toNat →
      k.toNat ≤ N + 1 →
      acc.toNat = special_factorial_nat (k.toNat - 1) →
      N + 1 - k.toNat ≤ m →
      clever_137_special_factorial.build_at n k acc
        = RustM.ok (UInt64.ofNat (special_factorial_nat N)) := by
  intro m
  induction m with
  | zero =>
    intro k acc hk_lo hk_hi hacc hm
    have hk_eq : k.toNat = N + 1 := by omega
    have hk_gt : k.toNat > n.toNat := by rw [hn]; omega
    rw [build_at_base n k acc hk_gt]
    have hacc_eq : acc.toNat = special_factorial_nat N := by
      rw [hacc, hk_eq]
      have h_sub : N + 1 - 1 = N := by omega
      rw [h_sub]
    have h_fit : special_factorial_nat N < 2 ^ 64 := sf_nat_lt_2_64 N hN
    congr 1
    apply UInt64.toNat_inj.mp
    rw [hacc_eq, UInt64.toNat_ofNat_of_lt' h_fit]
  | succ m ih =>
    intro k acc hk_lo hk_hi hacc hm
    by_cases hk_top : k.toNat = N + 1
    · have hk_gt : k.toNat > n.toNat := by rw [hn]; omega
      rw [build_at_base n k acc hk_gt]
      have hacc_eq : acc.toNat = special_factorial_nat N := by
        rw [hacc, hk_top]
        have h_sub : N + 1 - 1 = N := by omega
        rw [h_sub]
      have h_fit : special_factorial_nat N < 2 ^ 64 := sf_nat_lt_2_64 N hN
      congr 1
      apply UInt64.toNat_inj.mp
      rw [hacc_eq, UInt64.toNat_ofNat_of_lt' h_fit]
    · have hk_le_N : k.toNat ≤ N := by omega
      have hk_le_n : k.toNat ≤ n.toNat := by rw [hn]; exact hk_le_N
      have hk_le_8 : k.toNat ≤ 8 := by omega
      have hk_le_20 : k.toNat ≤ 20 := by omega
      have hk_fits : k.toNat + 1 < 2 ^ 64 := by
        have : N + 1 < 2 ^ 64 := by omega
        omega
      have h_acc_mul_eq : acc.toNat * factorial_nat k.toNat = special_factorial_nat k.toNat := by
        rw [hacc]
        obtain ⟨j, hj⟩ : ∃ j, k.toNat = j + 1 := ⟨k.toNat - 1, by omega⟩
        rw [hj]
        show special_factorial_nat (j + 1 - 1) * factorial_nat (j + 1)
              = special_factorial_nat (j + 1)
        have h_sub : j + 1 - 1 = j := by omega
        rw [h_sub]
        rfl
      have h_mul_fits : acc.toNat * factorial_nat k.toNat < 2 ^ 64 := by
        rw [h_acc_mul_eq]
        exact sf_nat_lt_2_64 _ hk_le_8
      rw [build_at_recurse n k acc hk_le_n hk_le_20 hk_fits h_mul_fits]
      have h_fact_fits : factorial_nat k.toNat < 2 ^ 64 := factorial_nat_lt_2_64 _ hk_le_20
      have h_fact_toNat :
          (UInt64.ofNat (factorial_nat k.toNat) : u64).toNat = factorial_nat k.toNat :=
        UInt64.toNat_ofNat_of_lt' h_fact_fits
      have h_mul_fits_u :
          acc.toNat * (UInt64.ofNat (factorial_nat k.toNat) : u64).toNat < 2 ^ 64 := by
        rw [h_fact_toNat]; exact h_mul_fits
      have h_acc'_toNat :
          (acc * UInt64.ofNat (factorial_nat k.toNat)).toNat
            = acc.toNat * factorial_nat k.toNat := by
        rw [mul_toNat acc _ h_mul_fits_u, h_fact_toNat]
      have h_k'_toNat : (k + 1).toNat = k.toNat + 1 := succ_toNat k hk_fits
      have h_k'_lo : 1 ≤ (k + 1).toNat := by rw [h_k'_toNat]; omega
      have h_k'_hi : (k + 1).toNat ≤ N + 1 := by rw [h_k'_toNat]; omega
      have h_acc'_eq :
          (acc * UInt64.ofNat (factorial_nat k.toNat)).toNat
            = special_factorial_nat ((k + 1).toNat - 1) := by
        rw [h_acc'_toNat, h_acc_mul_eq, h_k'_toNat]
        have h_sub : k.toNat + 1 - 1 = k.toNat := by omega
        rw [h_sub]
      have h_meas : N + 1 - (k + 1).toNat ≤ m := by rw [h_k'_toNat]; omega
      exact ih (k + 1) _ h_k'_lo h_k'_hi h_acc'_eq h_meas

/-! ## Obligation 1: base case. -/

/-- Defining convention: `special_factorial(0) = ok 1`. -/
theorem special_factorial_zero :
    clever_137_special_factorial.special_factorial 0 = RustM.ok 1 := by
  unfold clever_137_special_factorial.special_factorial
  have h_eq : (((0 : u64) ==? (0 : u64)) : RustM Bool) = pure true := rfl
  simp only [h_eq, pure_bind, ↓reduceIte]
  rfl

/-! ## Obligation 2: postcondition on the overflow-free range. -/

/-- For every `n` with `n.toNat ≤ 8`, `special_factorial(n)` equals the
    Brazilian factorial `1! * 2! * ... * n!`. -/
theorem special_factorial_matches_product (n : u64) (hn : n.toNat ≤ 8) :
    clever_137_special_factorial.special_factorial n
      = RustM.ok (UInt64.ofNat (special_factorial_nat n.toNat)) := by
  unfold clever_137_special_factorial.special_factorial
  by_cases hn0 : n.toNat = 0
  · -- n = 0 case.
    have h_n_zero_u : n = (0 : u64) := UInt64.toNat_inj.mp hn0
    have h_eq : ((n ==? (0 : u64)) : RustM Bool) = pure true := by
      show pure (decide (n = (0 : u64))) = pure true
      rw [decide_eq_true h_n_zero_u]
    simp only [h_eq, pure_bind, ↓reduceIte]
    show RustM.ok (1 : u64) = RustM.ok (UInt64.ofNat (special_factorial_nat n.toNat))
    congr 1
    rw [hn0]
    rfl
  · -- n ≥ 1 case.
    have h_n_ne_zero_u : n ≠ (0 : u64) := by
      intro h
      have : n.toNat = (0 : u64).toNat := by rw [h]
      rw [u64_zero_toNat] at this; omega
    have h_eq : ((n ==? (0 : u64)) : RustM Bool) = pure false := by
      show pure (decide (n = (0 : u64))) = pure false
      rw [decide_eq_false h_n_ne_zero_u]
    simp only [h_eq, pure_bind, Bool.false_eq_true, ↓reduceIte]
    apply build_at_correct n.toNat hn n rfl (n.toNat + 1 - (1 : u64).toNat) 1 1
    · rw [u64_one_toNat]; exact Nat.le_refl _
    · rw [u64_one_toNat]; omega
    · show (1 : u64).toNat = special_factorial_nat ((1 : u64).toNat - 1)
      rw [u64_one_toNat]; rfl
    · exact Nat.le_refl _

/-! ## Failure infrastructure for `n ≥ 9`. -/

/-- Reach state `(k = K+1, acc = ofNat (sf_nat K))` from `(k = 1, acc = 1)`. -/
private theorem build_at_reaches (n : u64) :
    ∀ K : Nat, K ≤ 8 → K + 1 ≤ n.toNat →
    clever_137_special_factorial.build_at n 1 1 =
      clever_137_special_factorial.build_at n
        (UInt64.ofNat (K + 1))
        (UInt64.ofNat (special_factorial_nat K)) := by
  intro K
  induction K with
  | zero =>
    intro _ _
    -- ofNat 1 = 1 and sf_nat 0 = 1, definitionally.
    rfl
  | succ K ih =>
    intro hK hk_le
    have hK' : K ≤ 8 := by omega
    have hk_le' : K + 1 ≤ n.toNat := by omega
    rw [ih hK' hk_le']
    -- Show:
    --   build_at n (ofNat (K+1)) (ofNat (sf_nat K))
    -- = build_at n (ofNat (K+2)) (ofNat (sf_nat (K+1))).
    have h_size : UInt64.size = 2 ^ 64 := usize_eq_2_64
    have h_k_toNat : (UInt64.ofNat (K + 1) : u64).toNat = K + 1 := by
      apply UInt64.toNat_ofNat_of_lt'
      have h1 : K + 1 ≤ 9 := by omega
      have h2 : (9 : Nat) < 2 ^ 64 := by decide
      omega
    have h_kp2_toNat : (UInt64.ofNat (K + 2) : u64).toNat = K + 2 := by
      apply UInt64.toNat_ofNat_of_lt'
      have h1 : K + 2 ≤ 10 := by omega
      have h2 : (10 : Nat) < 2 ^ 64 := by decide
      omega
    have h_acc_toNat : (UInt64.ofNat (special_factorial_nat K) : u64).toNat
        = special_factorial_nat K := by
      apply UInt64.toNat_ofNat_of_lt'
      exact sf_nat_lt_2_64 K hK'
    have h_k_le_n : (UInt64.ofNat (K + 1) : u64).toNat ≤ n.toNat := by
      rw [h_k_toNat]; omega
    have h_k_le_8 : (UInt64.ofNat (K + 1) : u64).toNat ≤ 8 := by
      rw [h_k_toNat]; omega
    have h_k_le_20 : (UInt64.ofNat (K + 1) : u64).toNat ≤ 20 := by
      rw [h_k_toNat]; omega
    have h_k_fits : (UInt64.ofNat (K + 1) : u64).toNat + 1 < 2 ^ 64 := by
      rw [h_k_toNat]
      have h1 : K + 2 ≤ 10 := by omega
      have h2 : (10 : Nat) < 2 ^ 64 := by decide
      omega
    -- The product fits because acc * factorial_nat (K+1) = sf_nat (K+1) ≤ sf_nat 8 < 2^64.
    have h_mul_fits :
        (UInt64.ofNat (special_factorial_nat K) : u64).toNat *
          factorial_nat (UInt64.ofNat (K + 1) : u64).toNat < 2 ^ 64 := by
      rw [h_acc_toNat, h_k_toNat]
      show special_factorial_nat K * factorial_nat (K + 1) < 2 ^ 64
      show special_factorial_nat (K + 1) < 2 ^ 64
      exact sf_nat_lt_2_64 (K + 1) hK
    rw [build_at_recurse n _ _ h_k_le_n h_k_le_20 h_k_fits h_mul_fits]
    -- Goal now (after recurse): build_at n (ofNat(K+1) + 1)
    --   (ofNat(sf K) * ofNat (factorial_nat (ofNat(K+1)).toNat))
    -- = build_at n (ofNat (K+2)) (ofNat (sf (K+1))).
    -- Reduce the factorial_nat argument first.
    rw [h_k_toNat]
    -- Now goal: build_at n (ofNat(K+1) + 1)
    --   (ofNat(sf K) * ofNat (factorial_nat (K + 1)))
    -- = build_at n (ofNat (K+2)) (ofNat (sf (K+1))).
    have h_fact_fits : factorial_nat (K + 1) < 2 ^ 64 :=
      factorial_nat_lt_2_64 (K + 1) (by omega)
    have h_fact_toNat : (UInt64.ofNat (factorial_nat (K + 1)) : u64).toNat
        = factorial_nat (K + 1) :=
      UInt64.toNat_ofNat_of_lt' h_fact_fits
    -- First argument equality.
    have h_k_succ_eq :
        (UInt64.ofNat (K + 1) : u64) + 1 = UInt64.ofNat (K + 2) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add_of_lt (by rw [u64_one_toNat]; exact h_k_fits),
          h_k_toNat, u64_one_toNat, h_kp2_toNat]
    -- Second argument equality.
    have h_mul_fits_u :
        (UInt64.ofNat (special_factorial_nat K) : u64).toNat *
          (UInt64.ofNat (factorial_nat (K + 1)) : u64).toNat < 2 ^ 64 := by
      rw [h_acc_toNat, h_fact_toNat]
      show special_factorial_nat K * factorial_nat (K + 1) < 2 ^ 64
      show special_factorial_nat (K + 1) < 2 ^ 64
      exact sf_nat_lt_2_64 (K + 1) hK
    have h_acc_succ_eq :
        (UInt64.ofNat (special_factorial_nat K) : u64) *
          UInt64.ofNat (factorial_nat (K + 1)) =
            UInt64.ofNat (special_factorial_nat (K + 1)) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_mul_of_lt h_mul_fits_u, h_acc_toNat, h_fact_toNat]
      have h_sf_K1 : (UInt64.ofNat (special_factorial_nat (K + 1)) : u64).toNat
          = special_factorial_nat (K + 1) :=
        UInt64.toNat_ofNat_of_lt' (sf_nat_lt_2_64 (K + 1) hK)
      rw [h_sf_K1]
      rfl
    rw [h_k_succ_eq, h_acc_succ_eq]

/-- At `(k = 9, acc = ofNat (sf_nat 8))` with `n.toNat ≥ 9`, the outer
    multiplication overflows because `sf_nat 8 * 9! = sf_nat 9 > 2^64`. -/
private theorem build_at_9_fails (n : u64) (h : 9 ≤ n.toNat) :
    clever_137_special_factorial.build_at n
        (UInt64.ofNat 9)
        (UInt64.ofNat (special_factorial_nat 8))
      = .fail .integerOverflow := by
  conv => lhs; unfold clever_137_special_factorial.build_at
  have h_k_toNat : (UInt64.ofNat 9 : u64).toNat = 9 := by
    apply UInt64.toNat_ofNat_of_lt'; decide
  have h_acc_toNat : (UInt64.ofNat (special_factorial_nat 8) : u64).toNat
      = special_factorial_nat 8 :=
    UInt64.toNat_ofNat_of_lt' sf_nat_8_lt
  have h_not_gt : ¬ (UInt64.ofNat 9 : u64) > n := by
    intro hgt
    have := UInt64.lt_iff_toNat_lt.mp hgt
    rw [h_k_toNat] at this
    omega
  have h_dec : decide ((UInt64.ofNat 9 : u64) > n) = false := decide_eq_false h_not_gt
  -- factorial_at 9 1 1 = ok 9!  (9! = 362880 < 2^64).
  have h_factorial : clever_137_special_factorial.factorial_at (UInt64.ofNat 9) 1 1 =
      RustM.ok (UInt64.ofNat (factorial_nat 9)) := by
    have h9_le_20 : (UInt64.ofNat 9 : u64).toNat ≤ 20 := by rw [h_k_toNat]; decide
    have hfa := factorial_at_one_one (UInt64.ofNat 9) h9_le_20
    rw [hfa, h_k_toNat]
  -- The outer mul overflows.
  have h_mul_overflow :
      2 ^ 64 ≤
        (UInt64.ofNat (special_factorial_nat 8) : u64).toNat *
          (UInt64.ofNat (factorial_nat 9) : u64).toNat := by
    rw [h_acc_toNat]
    have h_fact9_fits : factorial_nat 9 < 2 ^ 64 := factorial_nat_lt_2_64 9 (by decide)
    have h_fact9_toNat : (UInt64.ofNat (factorial_nat 9) : u64).toNat = factorial_nat 9 :=
      UInt64.toNat_ofNat_of_lt' h_fact9_fits
    rw [h_fact9_toNat]
    show 2 ^ 64 ≤ special_factorial_nat 8 * factorial_nat 9
    -- Concrete: 5_056_584_744_960_000 * 362_880 = 1_834_933_472_251_084_800_000 > 2^64.
    have h_eq : special_factorial_nat 8 * factorial_nat 9 = 1834933472251084800000 := by decide
    rw [h_eq]; decide
  have h_mul_fail :
      ((UInt64.ofNat (special_factorial_nat 8) : u64) *? UInt64.ofNat (factorial_nat 9)
          : RustM u64) = .fail .integerOverflow :=
    mul_fail _ _ h_mul_overflow
  simp only [show ((UInt64.ofNat 9 : u64) >? n : RustM Bool)
                = pure (decide ((UInt64.ofNat 9 : u64) > n)) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte,
             h_factorial, RustM_ok_bind, h_mul_fail]
  rfl

/-- `build_at n 1 1 = fail` when `n.toNat ≥ 9`. -/
private theorem build_at_one_one_fails (n : u64) (h : 9 ≤ n.toNat) :
    clever_137_special_factorial.build_at n 1 1 = .fail .integerOverflow := by
  rw [build_at_reaches n 8 (Nat.le_refl _) h]
  show clever_137_special_factorial.build_at n
        (UInt64.ofNat 9)
        (UInt64.ofNat (special_factorial_nat 8)) = .fail .integerOverflow
  exact build_at_9_fails n h

/-! ## Obligation 3: failure boundary. -/

theorem special_factorial_overflow (n : u64) (h : 9 ≤ n.toNat) :
    clever_137_special_factorial.special_factorial n
      = RustM.fail .integerOverflow := by
  unfold clever_137_special_factorial.special_factorial
  have h_n_ne_zero_u : n ≠ (0 : u64) := by
    intro hh
    have : n.toNat = (0 : u64).toNat := by rw [hh]
    rw [u64_zero_toNat] at this; omega
  have h_eq : ((n ==? (0 : u64)) : RustM Bool) = pure false := by
    show pure (decide (n = (0 : u64))) = pure false
    rw [decide_eq_false h_n_ne_zero_u]
  simp only [h_eq, pure_bind, Bool.false_eq_true, ↓reduceIte]
  exact build_at_one_one_fails n h

end Clever_137_special_factorialObligations
