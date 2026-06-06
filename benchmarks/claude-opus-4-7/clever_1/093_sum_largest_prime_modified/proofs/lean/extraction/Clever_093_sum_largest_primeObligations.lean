-- Companion obligations file for the `clever_093_sum_largest_prime` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_093_sum_largest_prime

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_093_sum_largest_primeObligations

/-! ## Spec-side oracle definitions -/

/-- Mathematical primality on `Nat`. -/
private def is_prime_nat (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ k : Nat, 2 ≤ k → k < p → ¬ k ∣ p

/-- Sum of decimal digits of `n`. -/
private def digit_sum_nat (n : Nat) : Nat :=
  if h : 0 < n then n % 10 + digit_sum_nat (n / 10)
  else 0
termination_by n
decreasing_by exact Nat.div_lt_self h (by decide)

/-! ## Numeric helper lemmas (u64 ⇄ Nat bridges) -/

private theorem u64_two_toNat : (2 : u64).toNat = 2 := rfl
private theorem u64_one_toNat : (1 : u64).toNat = 1 := rfl
private theorem u64_zero_toNat : (0 : u64).toNat = 0 := rfl
private theorem u64_ten_toNat : (10 : u64).toNat = 10 := rfl
private theorem usize_zero_toNat : (0 : usize).toNat = 0 := rfl
private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

private theorem two32_sq : (2 : Nat) ^ 32 * 2 ^ 32 = 2 ^ 64 := by decide
private theorem two17_sq_lt_2_64 : (2 : Nat) ^ 17 * 2 ^ 17 < 2 ^ 64 := by decide
private theorem two17_sq_gt_2_32 : (2 : Nat) ^ 32 < (2 : Nat) ^ 17 * 2 ^ 17 := by decide

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

/-- `d *? d = pure (d * d)` when `d.toNat * d.toNat` fits in `u64`. -/
private theorem mul_self_pure (d : u64) (h : d.toNat * d.toNat < 2 ^ 64) :
    (d *? d : RustM u64) = pure (d * d) := by
  show (rust_primitives.ops.arith.Mul.mul d d : RustM u64) = pure (d * d)
  show (if BitVec.umulOverflow d.toBitVec d.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (d * d)) = _
  have h_no : ¬ UInt64.mulOverflow d d := by
    rw [UInt64.mulOverflow_iff]; omega
  have h_bv : BitVec.umulOverflow d.toBitVec d.toBitVec = false := by
    simpa [UInt64.mulOverflow] using h_no
  rw [h_bv]; rfl

/-- `n %? d = pure (n % d)` when `d ≠ 0`. -/
private theorem mod_pure (n d : u64) (h : d ≠ 0) :
    (n %? d : RustM u64) = pure (n % d) := by
  show (rust_primitives.ops.arith.Rem.rem n d : RustM u64) = pure (n % d)
  show (if d = 0 then (.fail .divisionByZero : RustM u64) else pure (n % d)) = _
  rw [if_neg h]

/-- `n /? d = pure (n / d)` when `d ≠ 0`. -/
private theorem div_pure (n d : u64) (h : d ≠ 0) :
    (n /? d : RustM u64) = pure (n / d) := by
  show (rust_primitives.ops.arith.Div.div n d : RustM u64) = pure (n / d)
  show (if d = 0 then (.fail .divisionByZero : RustM u64) else pure (n / d)) = _
  rw [if_neg h]

/-- `d +? 1 = pure (d + 1)` when `d.toNat + 1` fits in `u64`. -/
private theorem add_one_pure (d : u64) (h : d.toNat + 1 < 2 ^ 64) :
    (d +? (1 : u64) : RustM u64) = pure (d + 1) := by
  show (rust_primitives.ops.arith.Add.add d 1 : RustM u64) = pure (d + 1)
  show (if BitVec.uaddOverflow d.toBitVec (1 : u64).toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (d + 1)) = _
  have h_no : ¬ UInt64.addOverflow d 1 := by
    rw [UInt64.addOverflow_iff, u64_one_toNat]; omega
  have h_bv : BitVec.uaddOverflow d.toBitVec (1 : u64).toBitVec = false := by
    simpa [UInt64.addOverflow] using h_no
  rw [h_bv]; rfl

/-- `a +? b = pure (a + b)` when `a.toNat + b.toNat` fits in `u64`. -/
private theorem add_pure_u64 (a b : u64) (h : a.toNat + b.toNat < 2 ^ 64) :
    (a +? b : RustM u64) = pure (a + b) := by
  show (rust_primitives.ops.arith.Add.add a b : RustM u64) = pure (a + b)
  show (if BitVec.uaddOverflow a.toBitVec b.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (a + b)) = _
  have h_no : ¬ UInt64.addOverflow a b := by
    rw [UInt64.addOverflow_iff]; omega
  have h_bv : BitVec.uaddOverflow a.toBitVec b.toBitVec = false := by
    simpa [UInt64.addOverflow] using h_no
  rw [h_bv]; rfl

/-- `d ≠ 0` from `d.toNat ≥ 1`. -/
private theorem u64_ne_zero_of_toNat_pos (d : u64) (h : 1 ≤ d.toNat) : d ≠ 0 := by
  intro h_eq
  have h_zero : d.toNat = 0 := by rw [h_eq]; rfl
  omega

/-- `(d + 1).toNat = d.toNat + 1` when the sum fits. -/
private theorem succ_toNat (d : u64) (h : d.toNat + 1 < 2 ^ 64) :
    (d + 1).toNat = d.toNat + 1 := by
  rw [UInt64.toNat_add_of_lt (by rw [u64_one_toNat]; exact h), u64_one_toNat]

/-- If `d.toNat * d.toNat ≤ n.toNat`, then `d.toNat + 1 < 2 ^ 64`. -/
private theorem add_one_fits_of_dd_le_n
    (n d : u64) (h_le : d.toNat * d.toNat ≤ n.toNat) :
    d.toNat + 1 < 2 ^ 64 := by
  have h_n : n.toNat < 2 ^ 64 := n.toNat_lt
  by_cases hd0 : d.toNat = 0
  · rw [hd0]; decide
  · have hd_pos : 1 ≤ d.toNat := Nat.one_le_iff_ne_zero.mpr hd0
    have h_dd_lt : d.toNat * d.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt h_le h_n
    have h_d_lt_32 : d.toNat < 2 ^ 32 := by
      by_cases h : d.toNat < 2 ^ 32
      · exact h
      · exfalso
        have h_ge : (2 : Nat) ^ 32 ≤ d.toNat := Nat.le_of_not_lt h
        have h_mul : (2 ^ 32) * (2 ^ 32) ≤ d.toNat * d.toNat :=
          Nat.mul_le_mul h_ge h_ge
        rw [two32_sq] at h_mul
        omega
    have : (2 : Nat) ^ 32 + 1 ≤ 2 ^ 64 := by decide
    omega

/-! ## One-step unfold of `is_prime_at`

`is_prime_at` is the trial-divisor recursion that returns `true` (no divisor
found in `[d, sqrt n]`) or `false` (some divisor found). The roles of
`true`/`false` are inverted relative to `has_divisor_at` in
`clever_030_is_prime`. -/

private theorem is_prime_at_unfold (n d : u64)
    (h_d_ne : d ≠ 0)
    (h_mul_fits : d.toNat * d.toNat < 2 ^ 64) :
    clever_093_sum_largest_prime.is_prime_at n d =
      (if d.toNat * d.toNat > n.toNat then
        (RustM.ok true : RustM Bool)
       else if n.toNat % d.toNat = 0 then
        (RustM.ok false : RustM Bool)
       else
        clever_093_sum_largest_prime.is_prime_at n (d + 1)) := by
  have h_dd_eq : (d *? d : RustM u64) = pure (d * d) :=
    mul_self_pure d h_mul_fits
  have h_dd_toNat : (d * d).toNat = d.toNat * d.toNat :=
    UInt64.toNat_mul_of_lt h_mul_fits
  have h_mod_eq : (n %? d : RustM u64) = pure (n % d) := mod_pure n d h_d_ne
  have h_mod_toNat : (n % d).toNat = n.toNat % d.toNat := UInt64.toNat_mod n d
  have h_gt_def : ((d * d) >? n : RustM Bool) = pure (decide ((d * d) > n)) := rfl
  have h_eq_def : ((n % d) ==? (0 : u64) : RustM Bool) =
      pure (decide ((n % d) = (0 : u64))) := rfl
  have h_gt_iff : ((d * d) > n) ↔ (d.toNat * d.toNat > n.toNat) := by
    constructor
    · intro h
      have := UInt64.lt_iff_toNat_lt.mp h
      rw [h_dd_toNat] at this; exact this
    · intro h
      apply UInt64.lt_iff_toNat_lt.mpr
      rw [h_dd_toNat]; exact h
  have h_eq_iff : ((n % d) = (0 : u64)) ↔ (n.toNat % d.toNat = 0) := by
    constructor
    · intro h
      have := congrArg UInt64.toNat h
      rw [h_mod_toNat, u64_zero_toNat] at this
      exact this
    · intro h
      apply UInt64.toNat_inj.mp
      rw [h_mod_toNat, u64_zero_toNat]
      exact h
  conv => lhs; unfold clever_093_sum_largest_prime.is_prime_at
  rw [h_dd_eq]
  simp only [pure_bind]
  rw [h_gt_def]
  simp only [pure_bind]
  by_cases h_gt : d.toNat * d.toNat > n.toNat
  · have h_gt_u : (d * d) > n := h_gt_iff.mpr h_gt
    rw [if_pos (decide_eq_true h_gt_u), if_pos h_gt]
    rfl
  · have h_not_gt_u : ¬ (d * d) > n := fun h => h_gt (h_gt_iff.mp h)
    have h_dec_gt : (decide ((d * d) > n)) = false := decide_eq_false h_not_gt_u
    rw [h_dec_gt, if_neg h_gt]
    simp only [Bool.false_eq_true, if_false]
    rw [h_mod_eq]
    simp only [pure_bind]
    rw [h_eq_def]
    simp only [pure_bind]
    by_cases h_mod : n.toNat % d.toNat = 0
    · have h_mod_u : (n % d) = (0 : u64) := h_eq_iff.mpr h_mod
      rw [if_pos (decide_eq_true h_mod_u), if_pos h_mod]
      rfl
    · have h_not_mod_u : ¬ (n % d) = (0 : u64) := fun h => h_mod (h_eq_iff.mp h)
      have h_dec_mod : (decide ((n % d) = (0 : u64))) = false :=
        decide_eq_false h_not_mod_u
      rw [h_dec_mod, if_neg h_mod]
      simp only [Bool.false_eq_true, if_false]
      have h_add_fits : d.toNat + 1 < 2 ^ 64 :=
        add_one_fits_of_dd_le_n n d (Nat.le_of_not_lt h_gt)
      rw [add_one_pure d h_add_fits]
      simp only [pure_bind]

/-! ## Branch lemmas for `is_prime_at`. -/

/-- `is_prime_at` returns `false` if `d ∣ n` and `d * d ≤ n`. -/
private theorem is_prime_at_found (n d : u64)
    (h_d_ge : 2 ≤ d.toNat)
    (h_le : d.toNat * d.toNat ≤ n.toNat)
    (h_dvd : d.toNat ∣ n.toNat) :
    clever_093_sum_largest_prime.is_prime_at n d = RustM.ok false := by
  have h_d_ne : d ≠ 0 := u64_ne_zero_of_toNat_pos d (by omega)
  have h_mul_fits : d.toNat * d.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt h_le n.toNat_lt
  have h_not_gt : ¬ d.toNat * d.toNat > n.toNat := by omega
  have h_mod_zero : n.toNat % d.toNat = 0 := by
    obtain ⟨k, hk⟩ := h_dvd
    rw [hk, Nat.mul_mod_right]
  rw [is_prime_at_unfold n d h_d_ne h_mul_fits, if_neg h_not_gt, if_pos h_mod_zero]

/-- Base case: `is_prime_at` returns `true` if `d * d > n`. -/
private theorem is_prime_at_base (n d : u64)
    (h_d_ne : d ≠ 0)
    (h_mul_fits : d.toNat * d.toNat < 2 ^ 64)
    (h_gt : d.toNat * d.toNat > n.toNat) :
    clever_093_sum_largest_prime.is_prime_at n d = RustM.ok true := by
  rw [is_prime_at_unfold n d h_d_ne h_mul_fits, if_pos h_gt]

/-! ## Finding a witness divisor (soundness). -/

/-- If there exists `d' ≥ d` with `d' * d' ≤ n` and `d' ∣ n`, then
    `is_prime_at n d = ok false`. -/
private theorem is_prime_at_finds_witness (n : u64) :
    ∀ (m : Nat) (d : u64),
      2 ≤ d.toNat →
      (∃ d' : Nat, d.toNat ≤ d' ∧ d' - d.toNat ≤ m
          ∧ d' * d' ≤ n.toNat ∧ d' ∣ n.toNat) →
      clever_093_sum_largest_prime.is_prime_at n d = RustM.ok false := by
  intro m
  induction m with
  | zero =>
    intro d h_d_ge hex
    obtain ⟨d', h_le, h_diff, h_dd, h_dvd⟩ := hex
    have h_eq : d' = d.toNat := by omega
    rw [h_eq] at h_dd h_dvd
    exact is_prime_at_found n d h_d_ge h_dd h_dvd
  | succ m ih =>
    intro d h_d_ge hex
    obtain ⟨d', h_le, h_diff, h_dd, h_dvd⟩ := hex
    have h_d_ne : d ≠ 0 := u64_ne_zero_of_toNat_pos d (by omega)
    have h_dd_le_n : d.toNat * d.toNat ≤ n.toNat := by
      have h_dd_le : d.toNat * d.toNat ≤ d' * d' := Nat.mul_le_mul h_le h_le
      omega
    have h_fits : d.toNat * d.toNat < 2 ^ 64 :=
      Nat.lt_of_le_of_lt h_dd_le_n n.toNat_lt
    have h_not_gt : ¬ d.toNat * d.toNat > n.toNat := by omega
    rw [is_prime_at_unfold n d h_d_ne h_fits, if_neg h_not_gt]
    by_cases h_mod : n.toNat % d.toNat = 0
    · rw [if_pos h_mod]
    · rw [if_neg h_mod]
      have h_add_fits : d.toNat + 1 < 2 ^ 64 :=
        add_one_fits_of_dd_le_n n d h_dd_le_n
      have h_succ_toNat : (d + 1).toNat = d.toNat + 1 := succ_toNat d h_add_fits
      have h_succ_ge : 2 ≤ (d + 1).toNat := by rw [h_succ_toNat]; omega
      have h_d_lt_d' : d.toNat < d' := by
        by_cases h_eq : d.toNat = d'
        · exfalso
          have h_dvd_d : d.toNat ∣ n.toNat := h_eq ▸ h_dvd
          obtain ⟨k, hk⟩ := h_dvd_d
          have h_mz : n.toNat % d.toNat = 0 := by rw [hk]; exact Nat.mul_mod_right _ _
          exact h_mod h_mz
        · omega
      have h_succ_le : (d + 1).toNat ≤ d' := by rw [h_succ_toNat]; omega
      have h_succ_diff : d' - (d + 1).toNat ≤ m := by rw [h_succ_toNat]; omega
      exact ih (d + 1) h_succ_ge ⟨d', h_succ_le, h_succ_diff, h_dd, h_dvd⟩

/-! ## Completeness: no divisor up to sqrt(n) ⇒ returns true. -/

private theorem is_prime_at_complete_aux (n : u64) (h_n_fit : n.toNat < 2 ^ 32) :
    ∀ (m : Nat) (d : u64),
      (2 : Nat) ^ 17 - d.toNat ≤ m →
      2 ≤ d.toNat →
      d.toNat ≤ (2 : Nat) ^ 17 →
      (∀ k : Nat, d.toNat ≤ k → k * k ≤ n.toNat → ¬ k ∣ n.toNat) →
      clever_093_sum_largest_prime.is_prime_at n d = RustM.ok true := by
  intro m
  induction m with
  | zero =>
    intro d h_m h_d_ge h_d_le h_no_dvd
    have h_d_eq : d.toNat = (2 : Nat) ^ 17 := by omega
    have h_dd_eq : d.toNat * d.toNat = (2 : Nat) ^ 17 * 2 ^ 17 := by rw [h_d_eq]
    have h_gt : d.toNat * d.toNat > n.toNat := by
      rw [h_dd_eq]
      have h1 : n.toNat < 2 ^ 32 := h_n_fit
      have h2 : (2 : Nat) ^ 32 < 2 ^ 17 * 2 ^ 17 := two17_sq_gt_2_32
      omega
    have h_dd_fits : d.toNat * d.toNat < 2 ^ 64 := by
      rw [h_dd_eq]; exact two17_sq_lt_2_64
    have h_d_ne : d ≠ 0 := u64_ne_zero_of_toNat_pos d (by omega)
    exact is_prime_at_base n d h_d_ne h_dd_fits h_gt
  | succ m ih =>
    intro d h_m h_d_ge h_d_le h_no_dvd
    by_cases h_at_top : d.toNat = (2 : Nat) ^ 17
    · have h_dd_eq : d.toNat * d.toNat = (2 : Nat) ^ 17 * 2 ^ 17 := by rw [h_at_top]
      have h_gt : d.toNat * d.toNat > n.toNat := by
        rw [h_dd_eq]
        have h2 : (2 : Nat) ^ 32 < 2 ^ 17 * 2 ^ 17 := two17_sq_gt_2_32
        omega
      have h_dd_fits : d.toNat * d.toNat < 2 ^ 64 := by
        rw [h_dd_eq]; exact two17_sq_lt_2_64
      have h_d_ne : d ≠ 0 := u64_ne_zero_of_toNat_pos d (by omega)
      exact is_prime_at_base n d h_d_ne h_dd_fits h_gt
    · have h_d_lt_top : d.toNat < (2 : Nat) ^ 17 := by omega
      have h_dd_lt : d.toNat * d.toNat < (2 : Nat) ^ 17 * 2 ^ 17 := by
        exact Nat.mul_lt_mul_of_lt_of_lt h_d_lt_top h_d_lt_top
      have h_dd_fits : d.toNat * d.toNat < 2 ^ 64 :=
        Nat.lt_trans h_dd_lt two17_sq_lt_2_64
      have h_d_ne : d ≠ 0 := u64_ne_zero_of_toNat_pos d (by omega)
      rw [is_prime_at_unfold n d h_d_ne h_dd_fits]
      by_cases h_gt : d.toNat * d.toNat > n.toNat
      · rw [if_pos h_gt]
      · rw [if_neg h_gt]
        have h_dd_le_n : d.toNat * d.toNat ≤ n.toNat := Nat.le_of_not_lt h_gt
        have h_mod_ne : ¬ n.toNat % d.toNat = 0 := by
          intro h_mod
          have h_dvd : d.toNat ∣ n.toNat := Nat.dvd_of_mod_eq_zero h_mod
          exact h_no_dvd d.toNat (Nat.le_refl _) h_dd_le_n h_dvd
        rw [if_neg h_mod_ne]
        have h_add_fits : d.toNat + 1 < 2 ^ 64 :=
          add_one_fits_of_dd_le_n n d h_dd_le_n
        have h_succ_toNat : (d + 1).toNat = d.toNat + 1 := succ_toNat d h_add_fits
        have h_succ_ge : 2 ≤ (d + 1).toNat := by rw [h_succ_toNat]; omega
        have h_succ_le : (d + 1).toNat ≤ (2 : Nat) ^ 17 := by
          rw [h_succ_toNat]; omega
        have h_succ_m : (2 : Nat) ^ 17 - (d + 1).toNat ≤ m := by
          rw [h_succ_toNat]; omega
        have h_no_dvd_succ : ∀ k : Nat, (d + 1).toNat ≤ k → k * k ≤ n.toNat →
            ¬ k ∣ n.toNat := by
          intro k h_k_ge h_k_dd h_k_dvd
          apply h_no_dvd k _ h_k_dd h_k_dvd
          rw [h_succ_toNat] at h_k_ge; omega
        exact ih (d + 1) h_succ_m h_succ_ge h_succ_le h_no_dvd_succ

/-! ## Bridge: `is_prime` ↔ `is_prime_nat`. -/

/-- If `n.toNat < 2` then `is_prime n = ok false`. -/
private theorem is_prime_lt_two (n : u64) (h : n.toNat < 2) :
    clever_093_sum_largest_prime.is_prime n = RustM.ok false := by
  unfold clever_093_sum_largest_prime.is_prime
  have h_lt : n < (2 : u64) := by
    apply UInt64.lt_iff_toNat_lt.mpr
    rw [u64_two_toNat]; exact h
  rw [show (n <? (2 : u64) : RustM Bool) = pure (decide (n < (2 : u64))) from rfl]
  simp only [pure_bind, decide_eq_true h_lt, if_true]
  rfl

/-- Bridge: `is_prime n = ok true` iff `is_prime_nat n.toNat`, given the
    feasibility bound. -/
private theorem is_prime_true_iff (n : u64) (h_fit : n.toNat < 2 ^ 32) :
    clever_093_sum_largest_prime.is_prime n = RustM.ok true ↔ is_prime_nat n.toNat := by
  constructor
  · -- Soundness direction.
    intro h
    by_cases h_lt : n.toNat < 2
    · exfalso
      rw [is_prime_lt_two n h_lt] at h
      exact absurd h (by decide)
    have hn : 2 ≤ n.toNat := by omega
    have h_at : clever_093_sum_largest_prime.is_prime_at n (2 : u64) = RustM.ok true := by
      unfold clever_093_sum_largest_prime.is_prime at h
      have h_not_lt : ¬ n < (2 : u64) := by
        intro hlt
        have := UInt64.lt_iff_toNat_lt.mp hlt
        rw [u64_two_toNat] at this; omega
      have h_dec_false : decide (n < (2 : u64)) = false := decide_eq_false h_not_lt
      rw [show (n <? (2 : u64) : RustM Bool) = pure (decide (n < (2 : u64))) from rfl,
          h_dec_false] at h
      simp only [pure_bind, Bool.false_eq_true, if_false] at h
      exact h
    refine ⟨hn, ?_⟩
    intro k h_k_ge h_k_lt h_dvd
    -- Use h_at and witness construction to derive contradiction.
    obtain ⟨q, hq⟩ := h_dvd
    have hk_pos : 0 < k := by omega
    have h_q_pos : 0 < q := by
      rcases Nat.eq_zero_or_pos q with hz | hp
      · subst hz; rw [Nat.mul_zero] at hq; omega
      · exact hp
    have h_q_ge_2 : 2 ≤ q := by
      by_cases h_q_eq_1 : q = 1
      · subst h_q_eq_1; rw [Nat.mul_one] at hq; omega
      · omega
    let d_min := min k q
    have h_d_min_ge_2 : 2 ≤ d_min := Nat.le_min.mpr ⟨h_k_ge, h_q_ge_2⟩
    have h_dmin_le_k : d_min ≤ k := Nat.min_le_left k q
    have h_dmin_le_q : d_min ≤ q := Nat.min_le_right k q
    have h_dmin_sq_le_n : d_min * d_min ≤ n.toNat := by
      have h1 : d_min * d_min ≤ k * q := Nat.mul_le_mul h_dmin_le_k h_dmin_le_q
      rw [← hq] at h1; exact h1
    have h_dmin_dvd_n : d_min ∣ n.toNat := by
      rcases Nat.le_total k q with hkq | hkq
      · have h_eq : d_min = k := Nat.min_eq_left hkq
        rw [h_eq, hq]
        exact Nat.dvd_mul_right k q
      · have h_eq : d_min = q := Nat.min_eq_right hkq
        rw [h_eq, hq]
        exact Nat.dvd_mul_left q k
    have h_2_le_dmin : (2 : u64).toNat ≤ d_min := by rw [u64_two_toNat]; exact h_d_min_ge_2
    have h_diff_bound : d_min - (2 : u64).toNat ≤ d_min - 2 := by
      rw [u64_two_toNat]; exact Nat.le_refl _
    have h_finds :
        clever_093_sum_largest_prime.is_prime_at n (2 : u64) = RustM.ok false :=
      is_prime_at_finds_witness n (d_min - 2) (2 : u64)
        (by rw [u64_two_toNat]; exact Nat.le_refl _)
        ⟨d_min, h_2_le_dmin, h_diff_bound, h_dmin_sq_le_n, h_dmin_dvd_n⟩
    rw [h_at] at h_finds
    exact absurd h_finds (by decide)
  · -- Completeness direction.
    rintro ⟨h_n_ge_2, h_no_dvd⟩
    unfold clever_093_sum_largest_prime.is_prime
    have h_not_lt : ¬ n < (2 : u64) := by
      intro hlt
      have := UInt64.lt_iff_toNat_lt.mp hlt
      rw [u64_two_toNat] at this; omega
    have h_dec_false : decide (n < (2 : u64)) = false := decide_eq_false h_not_lt
    rw [show (n <? (2 : u64) : RustM Bool) = pure (decide (n < (2 : u64))) from rfl,
        h_dec_false]
    simp only [pure_bind, Bool.false_eq_true, if_false]
    -- Apply completeness.
    have h_2_ge : 2 ≤ (2 : u64).toNat := by rw [u64_two_toNat]; exact Nat.le_refl _
    have h_2_le_top : (2 : u64).toNat ≤ (2 : Nat) ^ 17 := by
      rw [u64_two_toNat]; decide
    have h_no_dvd' : ∀ k : Nat, (2 : u64).toNat ≤ k → k * k ≤ n.toNat →
        ¬ k ∣ n.toNat := by
      intro k h_k_ge h_k_dd h_k_dvd
      rw [u64_two_toNat] at h_k_ge
      have h_2k_le_kk : 2 * k ≤ k * k := by
        have : 2 * k = k * 2 := Nat.mul_comm 2 k
        rw [this]
        exact Nat.mul_le_mul_left k h_k_ge
      have h_2k_le_n : 2 * k ≤ n.toNat := Nat.le_trans h_2k_le_kk h_k_dd
      have h_k_lt_n : k < n.toNat := by omega
      exact h_no_dvd k h_k_ge h_k_lt_n h_k_dvd
    exact is_prime_at_complete_aux n h_fit
      ((2 : Nat) ^ 17 - (2 : u64).toNat) (2 : u64)
      (Nat.le_refl _) (by rw [u64_two_toNat]; exact Nat.le_refl _) h_2_le_top h_no_dvd'

/-- If `is_prime_nat n.toNat` is false (and `n.toNat < 2^32`), then
    `is_prime n = ok false`. -/
private theorem is_prime_false_iff (n : u64) (h_fit : n.toNat < 2 ^ 32) :
    clever_093_sum_largest_prime.is_prime n = RustM.ok false ↔ ¬ is_prime_nat n.toNat := by
  constructor
  · intro h h_prime
    have h_true : clever_093_sum_largest_prime.is_prime n = RustM.ok true :=
      (is_prime_true_iff n h_fit).mpr h_prime
    rw [h] at h_true
    exact absurd h_true (by decide)
  · intro h_not_prime
    by_cases h_lt : n.toNat < 2
    · exact is_prime_lt_two n h_lt
    have hn : 2 ≤ n.toNat := by omega
    -- ¬ is_prime_nat means ∃ k, 2 ≤ k < n, k ∣ n
    have h_ex : ∃ k : Nat, 2 ≤ k ∧ k < n.toNat ∧ k ∣ n.toNat := by
      rcases Classical.em (∃ k : Nat, 2 ≤ k ∧ k < n.toNat ∧ k ∣ n.toNat) with h | h
      · exact h
      · exfalso
        apply h_not_prime
        refine ⟨hn, ?_⟩
        intro k h_k_ge h_k_lt h_dvd
        exact h ⟨k, h_k_ge, h_k_lt, h_dvd⟩
    obtain ⟨k, h_k_ge, h_k_lt, h_dvd⟩ := h_ex
    obtain ⟨q, hq⟩ := h_dvd
    have hk_pos : 0 < k := by omega
    have h_q_pos : 0 < q := by
      rcases Nat.eq_zero_or_pos q with hz | hp
      · subst hz; rw [Nat.mul_zero] at hq; omega
      · exact hp
    have h_q_ge_2 : 2 ≤ q := by
      by_cases h_q_eq_1 : q = 1
      · subst h_q_eq_1; rw [Nat.mul_one] at hq; omega
      · omega
    let d_min := min k q
    have h_d_min_ge_2 : 2 ≤ d_min := Nat.le_min.mpr ⟨h_k_ge, h_q_ge_2⟩
    have h_dmin_le_k : d_min ≤ k := Nat.min_le_left k q
    have h_dmin_le_q : d_min ≤ q := Nat.min_le_right k q
    have h_dmin_sq_le_n : d_min * d_min ≤ n.toNat := by
      have h1 : d_min * d_min ≤ k * q := Nat.mul_le_mul h_dmin_le_k h_dmin_le_q
      rw [← hq] at h1; exact h1
    have h_dmin_dvd_n : d_min ∣ n.toNat := by
      rcases Nat.le_total k q with hkq | hkq
      · have h_eq : d_min = k := Nat.min_eq_left hkq
        rw [h_eq, hq]
        exact Nat.dvd_mul_right k q
      · have h_eq : d_min = q := Nat.min_eq_right hkq
        rw [h_eq, hq]
        exact Nat.dvd_mul_left q k
    have h_2_le_dmin : (2 : u64).toNat ≤ d_min := by rw [u64_two_toNat]; exact h_d_min_ge_2
    have h_diff_bound : d_min - (2 : u64).toNat ≤ d_min - 2 := by
      rw [u64_two_toNat]; exact Nat.le_refl _
    have h_finds :
        clever_093_sum_largest_prime.is_prime_at n (2 : u64) = RustM.ok false :=
      is_prime_at_finds_witness n (d_min - 2) (2 : u64)
        (by rw [u64_two_toNat]; exact Nat.le_refl _)
        ⟨d_min, h_2_le_dmin, h_diff_bound, h_dmin_sq_le_n, h_dmin_dvd_n⟩
    unfold clever_093_sum_largest_prime.is_prime
    have h_not_lt : ¬ n < (2 : u64) := by
      intro hlt
      have := UInt64.lt_iff_toNat_lt.mp hlt
      rw [u64_two_toNat] at this; omega
    have h_dec_false : decide (n < (2 : u64)) = false := decide_eq_false h_not_lt
    rw [show (n <? (2 : u64) : RustM Bool) = pure (decide (n < (2 : u64))) from rfl,
        h_dec_false]
    simp only [pure_bind, Bool.false_eq_true, if_false]
    exact h_finds

/-! ## Step lemmas for `largest_prime_at`. -/

/-- OOB: returns the running `(best, found)`. -/
private theorem largest_prime_at_oob
    (l : RustSlice u64) (i : usize) (best : u64) (found : Bool)
    (hi : l.val.size ≤ i.toNat) :
    clever_093_sum_largest_prime.largest_prime_at l i best found
      = RustM.ok (rust_primitives.hax.Tuple2.mk best found) := by
  conv => lhs; unfold clever_093_sum_largest_prime.largest_prime_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- Take: in-bounds, `is_prime(l[i]) = ok true`, AND (`¬ found ∨ l[i] > best`).
    Recurses with `(i + 1, l[i], true)`. -/
private theorem largest_prime_at_take
    (l : RustSlice u64) (i : usize) (best : u64) (found : Bool)
    (hi : i.toNat < l.val.size)
    (h_ip : clever_093_sum_largest_prime.is_prime (l.val[i.toNat]'hi) = RustM.ok true)
    (h_take : ¬ found = true ∨ best < (l.val[i.toNat]'hi)) :
    clever_093_sum_largest_prime.largest_prime_at l i best found
      = clever_093_sum_largest_prime.largest_prime_at l (i + 1) (l.val[i.toNat]'hi) true := by
  conv => lhs; unfold clever_093_sum_largest_prime.largest_prime_at
  have h_size : l.val.size < 2^64 := l.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (l[i]_? : RustM u64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
  have h_no_overflow_i : i.toNat + 1 < 2^64 := by omega
  have h_no_bv_i : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hi' := (USize64.uaddOverflow_iff i 1).mp hbo
      rw [usize_one_toNat] at hi'
      omega
  -- Encode the `(!found || decide (best < l[i]))` boolean as `true`.
  have h_or_true : ((!found) || decide (best < (l.val[i.toNat]'hi))) = true := by
    rcases h_take with hnf | hgt
    · have h_false : found = false := by
        cases found
        · rfl
        · exact absurd rfl hnf
      rw [h_false]; rfl
    · have h_dec : decide (best < (l.val[i.toNat]'hi)) = true := by
        rw [decide_eq_true_iff]; exact hgt
      rw [h_dec]; rw [Bool.or_true]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.cmp.gt,
             rust_primitives.hax.logical_op.not, rust_primitives.hax.logical_op.or,
             rust_primitives.hax.logical_op.and,
             h_ip, h_or_true,
             rust_primitives.ops.arith.Add.add, h_no_bv_i,
             Bool.and_self, ↓reduceIte]

/-- Skip (not prime): in-bounds, `is_prime(l[i]) = ok false`.
    Recurses with `(i + 1, best, found)`. -/
private theorem largest_prime_at_skip_not_prime
    (l : RustSlice u64) (i : usize) (best : u64) (found : Bool)
    (hi : i.toNat < l.val.size)
    (h_ip : clever_093_sum_largest_prime.is_prime (l.val[i.toNat]'hi) = RustM.ok false) :
    clever_093_sum_largest_prime.largest_prime_at l i best found
      = clever_093_sum_largest_prime.largest_prime_at l (i + 1) best found := by
  conv => lhs; unfold clever_093_sum_largest_prime.largest_prime_at
  have h_size : l.val.size < 2^64 := l.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (l[i]_? : RustM u64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
  have h_no_overflow_i : i.toNat + 1 < 2^64 := by omega
  have h_no_bv_i : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hi' := (USize64.uaddOverflow_iff i 1).mp hbo
      rw [usize_one_toNat] at hi'
      omega
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.cmp.gt,
             rust_primitives.hax.logical_op.not, rust_primitives.hax.logical_op.or,
             rust_primitives.hax.logical_op.and,
             h_ip,
             rust_primitives.ops.arith.Add.add, h_no_bv_i,
             Bool.false_and, ↓reduceIte]

/-- Skip (not better): in-bounds, `is_prime(l[i]) = ok true`, but `found ∧ l[i] ≤ best`.
    Recurses with `(i + 1, best, found)`. -/
private theorem largest_prime_at_skip_not_better
    (l : RustSlice u64) (i : usize) (best : u64) (found : Bool)
    (hi : i.toNat < l.val.size)
    (h_ip : clever_093_sum_largest_prime.is_prime (l.val[i.toNat]'hi) = RustM.ok true)
    (h_found : found = true)
    (h_le : (l.val[i.toNat]'hi) ≤ best) :
    clever_093_sum_largest_prime.largest_prime_at l i best found
      = clever_093_sum_largest_prime.largest_prime_at l (i + 1) best found := by
  conv => lhs; unfold clever_093_sum_largest_prime.largest_prime_at
  have h_size : l.val.size < 2^64 := l.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (l[i]_? : RustM u64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
  have h_no_overflow_i : i.toNat + 1 < 2^64 := by omega
  have h_no_bv_i : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hi' := (USize64.uaddOverflow_iff i 1).mp hbo
      rw [usize_one_toNat] at hi'
      omega
  have h_or_false : ((!found) || decide (best < (l.val[i.toNat]'hi))) = false := by
    have h_not_found : (!found) = false := by rw [h_found]; rfl
    have h_not_lt : decide (best < (l.val[i.toNat]'hi)) = false := by
      rw [decide_eq_false_iff_not]
      intro h_lt
      have h1 := UInt64.lt_iff_toNat_lt.mp h_lt
      have h2 := UInt64.le_iff_toNat_le.mp h_le
      omega
    rw [h_not_found, h_not_lt]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.cmp.gt,
             rust_primitives.hax.logical_op.not, rust_primitives.hax.logical_op.or,
             rust_primitives.hax.logical_op.and,
             h_ip, h_or_false,
             rust_primitives.ops.arith.Add.add, h_no_bv_i,
             Bool.and_false, ↓reduceIte]

/-! ## Master correctness lemma for `largest_prime_at`.

We track a complete invariant via the running `(best, found)` and a
suffix-existence quantifier over primes:

  rf = true ↔ found = true ∨ ∃ j ∈ [i, size), is_prime_nat l[j].toNat

When `rf = true`, the returned `rv` is either the original `best` (if
no bigger prime found in suffix), or some prime in the suffix.

Maximality: `rv` is the largest prime in `[i, size) ∪ {best if found}`. -/

private theorem largest_prime_at_correct (l : RustSlice u64)
    (h_bound : ∀ (i : Nat) (hi : i < l.val.size),
        (l.val[i]'hi).toNat < 2 ^ 32) :
    ∀ (m : Nat) (i : usize) (best : u64) (found : Bool),
      l.val.size - i.toNat ≤ m →
      i.toNat ≤ l.val.size →
      (found = true → is_prime_nat best.toNat) →
      ∃ (rv : u64) (rf : Bool),
        clever_093_sum_largest_prime.largest_prime_at l i best found
          = RustM.ok (rust_primitives.hax.Tuple2.mk rv rf) ∧
        (rf = true ↔ found = true
          ∨ ∃ (j : Nat) (hj : j < l.val.size),
              i.toNat ≤ j ∧ is_prime_nat (l.val[j]'hj).toNat) ∧
        (rf = true → is_prime_nat rv.toNat) ∧
        (rf = true →
          (found = true ∧ rv = best) ∨
            ∃ (j : Nat) (hj : j < l.val.size), i.toNat ≤ j ∧ rv = (l.val[j]'hj)) ∧
        (rf = true →
          (found = true → best.toNat ≤ rv.toNat) ∧
          ∀ (j : Nat) (hj : j < l.val.size), i.toNat ≤ j →
            is_prime_nat (l.val[j]'hj).toNat → (l.val[j]'hj).toNat ≤ rv.toNat) := by
  intro m
  induction m with
  | zero =>
    intro i best found hm hi_le h_best_prime
    have hi_eq : i.toNat = l.val.size := by omega
    have hi_ge : l.val.size ≤ i.toNat := by omega
    refine ⟨best, found, largest_prime_at_oob l i best found hi_ge, ?_, ?_, ?_, ?_⟩
    · constructor
      · intro hf; left; exact hf
      · rintro (hf | ⟨j, hj, h_jge, _⟩)
        · exact hf
        · rw [hi_eq] at h_jge; omega
    · intro hrf
      exact h_best_prime hrf
    · intro hrf; left; exact ⟨hrf, rfl⟩
    · intro hrf
      refine ⟨fun _ => Nat.le_refl _, ?_⟩
      intro j hj h_jge _
      rw [hi_eq] at h_jge; omega
  | succ m ih =>
    intro i best found hm hi_le h_best_prime
    by_cases hi_ge : l.val.size ≤ i.toNat
    · have hi_eq : i.toNat = l.val.size := by omega
      refine ⟨best, found, largest_prime_at_oob l i best found hi_ge, ?_, ?_, ?_, ?_⟩
      · constructor
        · intro hf; left; exact hf
        · rintro (hf | ⟨j, hj, h_jge, _⟩)
          · exact hf
          · rw [hi_eq] at h_jge; omega
      · intro hrf
        exact h_best_prime hrf
      · intro hrf; left; exact ⟨hrf, rfl⟩
      · intro hrf
        refine ⟨fun _ => Nat.le_refl _, ?_⟩
        intro j hj h_jge _
        rw [hi_eq] at h_jge; omega
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size : l.val.size < 2^64 := l.size_lt_usizeSize
      have h_no_overflow_i : i.toNat + 1 < 2^64 := by omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := by
        have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
          rw [usize_one_toNat]; exact h_no_overflow_i
        rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_m_le : l.val.size - (i + 1).toNat ≤ m := by rw [h_i1]; omega
      have h_li_bound : (l.val[i.toNat]'hi_lt).toNat < 2 ^ 32 := h_bound i.toNat hi_lt
      by_cases h_prime : is_prime_nat (l.val[i.toNat]'hi_lt).toNat
      · -- l[i] is prime.
        have h_ip_true :
            clever_093_sum_largest_prime.is_prime (l.val[i.toNat]'hi_lt) = RustM.ok true :=
          (is_prime_true_iff (l.val[i.toNat]'hi_lt) h_li_bound).mpr h_prime
        by_cases h_take_cond : ¬ found = true ∨ best < (l.val[i.toNat]'hi_lt)
        · -- TAKE
          have h_step := largest_prime_at_take l i best found hi_lt h_ip_true h_take_cond
          have h_li_prime : is_prime_nat (l.val[i.toNat]'hi_lt).toNat := h_prime
          have h_ih_pre : (true = true → is_prime_nat (l.val[i.toNat]'hi_lt).toNat) :=
            fun _ => h_li_prime
          obtain ⟨rv, rf, hres, h_live, h_rv_prime, h_mem, h_min⟩ :=
            ih (i + 1) (l.val[i.toNat]'hi_lt) true h_m_le h_i1_le h_ih_pre
          refine ⟨rv, rf, ?_, ?_, ?_, ?_, ?_⟩
          · rw [h_step]; exact hres
          · constructor
            · intro _; right
              exact ⟨i.toNat, hi_lt, Nat.le_refl _, h_li_prime⟩
            · intro _
              apply h_live.mpr; left; rfl
          · intro hrf; exact h_rv_prime hrf
          · -- membership
            intro hrf
            rcases h_mem hrf with ⟨hf_true, h_rv_eq⟩ | ⟨j, hj, h_jge, h_rv_eq⟩
            · right
              refine ⟨i.toNat, hi_lt, Nat.le_refl _, ?_⟩
              exact h_rv_eq
            · right
              refine ⟨j, hj, ?_, h_rv_eq⟩
              rw [h_i1] at h_jge; omega
          · -- maximality
            intro hrf
            obtain ⟨h_min_best, h_min_suffix⟩ := h_min hrf
            have h_min_li : (l.val[i.toNat]'hi_lt).toNat ≤ rv.toNat := h_min_best rfl
            refine ⟨?_, ?_⟩
            · intro hf
              rcases h_take_cond with hnf | hgt
              · exact absurd hf hnf
              · have h_best_lt : best.toNat < (l.val[i.toNat]'hi_lt).toNat :=
                  UInt64.lt_iff_toNat_lt.mp hgt
                omega
            · intro j hj h_jge h_lj_prime
              by_cases h_jeq : j = i.toNat
              · subst h_jeq; exact h_min_li
              · have h_jge1 : (i + 1).toNat ≤ j := by rw [h_i1]; omega
                exact h_min_suffix j hj h_jge1 h_lj_prime
        · -- SKIP (not better)
          have h_found : found = true := by
            cases found with
            | false => exfalso; apply h_take_cond; left; intro h; cases h
            | true => rfl
          have h_le_best : (l.val[i.toNat]'hi_lt) ≤ best := by
            have h_not_lt : ¬ best < (l.val[i.toNat]'hi_lt) := by
              intro h; apply h_take_cond; right; exact h
            have h_nat : ¬ best.toNat < (l.val[i.toNat]'hi_lt).toNat :=
              fun h => h_not_lt (UInt64.lt_iff_toNat_lt.mpr h)
            apply UInt64.le_iff_toNat_le.mpr; omega
          have h_step :=
            largest_prime_at_skip_not_better l i best found hi_lt h_ip_true h_found h_le_best
          obtain ⟨rv, rf, hres, h_live, h_rv_prime, h_mem, h_min⟩ :=
            ih (i + 1) best found h_m_le h_i1_le h_best_prime
          refine ⟨rv, rf, ?_, ?_, ?_, ?_, ?_⟩
          · rw [h_step]; exact hres
          · constructor
            · intro hrf
              rcases h_live.mp hrf with hf | ⟨j, hj, h_jge, h_lj_prime⟩
              · left; exact hf
              · right
                refine ⟨j, hj, ?_, h_lj_prime⟩
                rw [h_i1] at h_jge; omega
            · rintro (hf | ⟨j, hj, h_jge, h_lj_prime⟩)
              · apply h_live.mpr; left; exact hf
              · apply h_live.mpr
                by_cases h_jeq : j = i.toNat
                · subst h_jeq
                  left; exact h_found
                · right
                  refine ⟨j, hj, ?_, h_lj_prime⟩
                  rw [h_i1]; omega
          · intro hrf; exact h_rv_prime hrf
          · -- membership
            intro hrf
            rcases h_mem hrf with ⟨hf_true, h_rv_eq⟩ | ⟨j, hj, h_jge, h_rv_eq⟩
            · left; exact ⟨hf_true, h_rv_eq⟩
            · right
              refine ⟨j, hj, ?_, h_rv_eq⟩
              rw [h_i1] at h_jge; omega
          · intro hrf
            obtain ⟨h_min_best, h_min_suffix⟩ := h_min hrf
            refine ⟨h_min_best, ?_⟩
            intro j hj h_jge h_lj_prime
            by_cases h_jeq : j = i.toNat
            · subst h_jeq
              have h_li_le_best : (l.val[i.toNat]'hi_lt).toNat ≤ best.toNat :=
                UInt64.le_iff_toNat_le.mp h_le_best
              have h_best_le_rv : best.toNat ≤ rv.toNat := h_min_best h_found
              omega
            · have h_jge1 : (i + 1).toNat ≤ j := by rw [h_i1]; omega
              exact h_min_suffix j hj h_jge1 h_lj_prime
      · -- l[i] is not prime; skip.
        have h_ip_false :
            clever_093_sum_largest_prime.is_prime (l.val[i.toNat]'hi_lt) = RustM.ok false :=
          (is_prime_false_iff (l.val[i.toNat]'hi_lt) h_li_bound).mpr h_prime
        have h_step := largest_prime_at_skip_not_prime l i best found hi_lt h_ip_false
        obtain ⟨rv, rf, hres, h_live, h_rv_prime, h_mem, h_min⟩ :=
          ih (i + 1) best found h_m_le h_i1_le h_best_prime
        refine ⟨rv, rf, ?_, ?_, ?_, ?_, ?_⟩
        · rw [h_step]; exact hres
        · constructor
          · intro hrf
            rcases h_live.mp hrf with hf | ⟨j, hj, h_jge, h_lj_prime⟩
            · left; exact hf
            · right
              refine ⟨j, hj, ?_, h_lj_prime⟩
              rw [h_i1] at h_jge; omega
          · rintro (hf | ⟨j, hj, h_jge, h_lj_prime⟩)
            · apply h_live.mpr; left; exact hf
            · apply h_live.mpr
              by_cases h_jeq : j = i.toNat
              · subst h_jeq
                exact absurd h_lj_prime h_prime
              · right
                refine ⟨j, hj, ?_, h_lj_prime⟩
                rw [h_i1]; omega
        · intro hrf; exact h_rv_prime hrf
        · -- membership
          intro hrf
          rcases h_mem hrf with ⟨hf_true, h_rv_eq⟩ | ⟨j, hj, h_jge, h_rv_eq⟩
          · left; exact ⟨hf_true, h_rv_eq⟩
          · right
            refine ⟨j, hj, ?_, h_rv_eq⟩
            rw [h_i1] at h_jge; omega
        · intro hrf
          obtain ⟨h_min_best, h_min_suffix⟩ := h_min hrf
          refine ⟨h_min_best, ?_⟩
          intro j hj h_jge h_lj_prime
          by_cases h_jeq : j = i.toNat
          · subst h_jeq; exact absurd h_lj_prime h_prime
          · have h_jge1 : (i + 1).toNat ≤ j := by rw [h_i1]; omega
            exact h_min_suffix j hj h_jge1 h_lj_prime

/-! ## Correctness of `digit_sum_at` against the Nat oracle. -/

private theorem digit_sum_nat_succ_eq (n : Nat) (h : 0 < n) :
    digit_sum_nat n = n % 10 + digit_sum_nat (n / 10) := by
  conv => lhs; unfold digit_sum_nat
  rw [dif_pos h]

private theorem digit_sum_nat_zero_eq (n : Nat) (h : ¬ 0 < n) :
    digit_sum_nat n = 0 := by
  unfold digit_sum_nat; rw [dif_neg h]

/-- Bound: `digit_sum_nat n ≤ 9 * d` where `d` is the number of decimal
    digits of `n` (i.e., the smallest `d` with `n < 10^d`). -/
private theorem digit_sum_nat_le_9_times (k : Nat) :
    ∀ n : Nat, n < 10 ^ k → digit_sum_nat n ≤ 9 * k := by
  induction k with
  | zero =>
    intro n h
    have hn0 : n = 0 := by simp at h; omega
    have h_zero : digit_sum_nat n = 0 := by
      rw [hn0]; exact digit_sum_nat_zero_eq 0 (by decide)
    omega
  | succ k ih =>
    intro n h
    by_cases hn : 0 < n
    · have h_div : n / 10 < 10 ^ k := by
        have h10 : 10 ^ (k + 1) = 10 * 10 ^ k := by
          rw [Nat.pow_succ, Nat.mul_comm]
        rw [h10] at h
        exact Nat.div_lt_of_lt_mul h
      have ih_app : digit_sum_nat (n / 10) ≤ 9 * k := ih (n / 10) h_div
      have h_mod_le : n % 10 ≤ 9 := by
        have : n % 10 < 10 := Nat.mod_lt n (by decide)
        omega
      rw [digit_sum_nat_succ_eq n hn]
      omega
    · have h_zero : digit_sum_nat n = 0 := digit_sum_nat_zero_eq n hn
      omega

/-- Correctness of `digit_sum_at`: returns `acc + digit_sum_nat n`. -/
private theorem digit_sum_at_correct :
    ∀ (n : u64) (acc : u64),
      acc.toNat + digit_sum_nat n.toNat < 2 ^ 64 →
      ∃ v : u64,
        clever_093_sum_largest_prime.digit_sum_at n acc = RustM.ok v
        ∧ v.toNat = acc.toNat + digit_sum_nat n.toNat := by
  intro n
  induction h_meas : n.toNat using Nat.strongRecOn generalizing n with
  | _ k ih =>
    intro acc h_no_ov
    -- Bridge k to n.toNat in the goal and hypothesis up front.
    subst h_meas
    unfold clever_093_sum_largest_prime.digit_sum_at
    by_cases hn_eq_zero : n = (0 : u64)
    · -- Base case: n = 0
      have h_dec : decide (n = (0 : u64)) = true := decide_eq_true hn_eq_zero
      simp only [show (n ==? (0 : u64)) =
                   (pure (decide (n = (0 : u64))) : RustM Bool) from rfl,
                 h_dec, pure_bind, ↓reduceIte]
      refine ⟨acc, rfl, ?_⟩
      have h_n_zero : n.toNat = 0 := by rw [hn_eq_zero]; rfl
      have h_digit_zero : digit_sum_nat n.toNat = 0 := by
        rw [h_n_zero]; exact digit_sum_nat_zero_eq 0 (by decide)
      rw [h_digit_zero]
    · -- Step case: n ≠ 0
      have h_dec : decide (n = (0 : u64)) = false := decide_eq_false hn_eq_zero
      simp only [show (n ==? (0 : u64)) =
                   (pure (decide (n = (0 : u64))) : RustM Bool) from rfl,
                 h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
      have h_n_ne_zero : n ≠ (0 : u64) := hn_eq_zero
      have hn_pos : 0 < n.toNat := by
        rcases Nat.eq_zero_or_pos n.toNat with h0 | h0
        · exfalso; apply h_n_ne_zero
          apply UInt64.toNat_inj.mp
          rw [h0]; rfl
        · exact h0
      have h_ten_ne : (10 : u64) ≠ 0 := by decide
      have h_div_eq : (n /? (10 : u64) : RustM u64) = pure (n / 10) :=
        div_pure n (10 : u64) h_ten_ne
      have h_mod_eq : (n %? (10 : u64) : RustM u64) = pure (n % 10) :=
        mod_pure n (10 : u64) h_ten_ne
      have h_div_toNat : (n / 10).toNat = n.toNat / 10 := UInt64.toNat_div n 10
      have h_mod_toNat : (n % 10).toNat = n.toNat % 10 := UInt64.toNat_mod n 10
      have h_div_lt : (n / 10).toNat < n.toNat := by
        rw [h_div_toNat]
        exact Nat.div_lt_self hn_pos (by decide)
      have h_mod_le_9 : (n % 10).toNat ≤ 9 := by
        rw [h_mod_toNat]
        have : n.toNat % 10 < 10 := Nat.mod_lt n.toNat (by decide)
        omega
      -- acc + n % 10 doesn't overflow
      have h_acc_add_mod_no_ov : acc.toNat + (n % 10).toNat < 2 ^ 64 := by
        rw [h_mod_toNat]
        have h_step :
            digit_sum_nat n.toNat = n.toNat % 10 + digit_sum_nat (n.toNat / 10) :=
          digit_sum_nat_succ_eq n.toNat hn_pos
        omega
      have h_add_acc_mod : (acc +? (n % 10) : RustM u64) = pure (acc + (n % 10)) :=
        add_pure_u64 acc (n % 10) h_acc_add_mod_no_ov
      have h_acc_plus_mod_toNat : (acc + (n % 10)).toNat = acc.toNat + (n % 10).toNat :=
        UInt64.toNat_add_of_lt h_acc_add_mod_no_ov
      -- Apply IH on (n/10, acc + n%10).
      have h_ih_pre : (acc + (n % 10)).toNat + digit_sum_nat (n / 10).toNat < 2 ^ 64 := by
        rw [h_acc_plus_mod_toNat, h_mod_toNat, h_div_toNat]
        have h_step :
            digit_sum_nat n.toNat = n.toNat % 10 + digit_sum_nat (n.toNat / 10) :=
          digit_sum_nat_succ_eq n.toNat hn_pos
        omega
      obtain ⟨v, hv_eq, hv_toNat⟩ :=
        ih (n / 10).toNat h_div_lt (n / 10) rfl (acc + (n % 10)) h_ih_pre
      rw [h_mod_eq]
      simp only [pure_bind]
      rw [h_add_acc_mod]
      simp only [pure_bind]
      rw [h_div_eq]
      simp only [pure_bind]
      refine ⟨v, hv_eq, ?_⟩
      rw [hv_toNat, h_acc_plus_mod_toNat, h_mod_toNat, h_div_toNat]
      have h_step :
          digit_sum_nat n.toNat = n.toNat % 10 + digit_sum_nat (n.toNat / 10) :=
        digit_sum_nat_succ_eq n.toNat hn_pos
      omega

/-- Digit-sum bound used to discharge no-overflow side conditions. -/
private theorem digit_sum_nat_bound_u64 (p : u64) :
    digit_sum_nat p.toNat ≤ 9 * 20 := by
  apply digit_sum_nat_le_9_times 20
  have : p.toNat < 2 ^ 64 := p.toNat_lt
  have h64 : (2 : Nat) ^ 64 < 10 ^ 20 := by decide
  omega

/-! ## Top-level theorems. -/

theorem sum_largest_prime_empty
    (lst : RustSlice u64) (hempty : lst.val.size = 0) :
    clever_093_sum_largest_prime.sum_largest_prime lst = RustM.ok (0 : u64) := by
  unfold clever_093_sum_largest_prime.sum_largest_prime
  -- largest_prime_at lst 0 0 false on empty slice returns (0, false).
  have h_oob : lst.val.size ≤ (0 : usize).toNat := by
    rw [usize_zero_toNat, hempty]; exact Nat.le_refl _
  have h_lpa := largest_prime_at_oob lst (0 : usize) (0 : u64) false h_oob
  rw [h_lpa]
  simp only [pure_bind, RustM_ok_bind, rust_primitives.hax.logical_op.not,
             Bool.not_false, ↓reduceIte]
  rfl

theorem sum_largest_prime_no_primes_zero
    (lst : RustSlice u64)
    (h_bound : ∀ (i : Nat) (hi : i < lst.val.size), (lst.val[i]'hi).toNat < 2 ^ 32)
    (h_no_primes : ∀ (i : Nat) (hi : i < lst.val.size),
        ¬ is_prime_nat (lst.val[i]'hi).toNat) :
    clever_093_sum_largest_prime.sum_largest_prime lst = RustM.ok (0 : u64) := by
  unfold clever_093_sum_largest_prime.sum_largest_prime
  -- Apply master correctness.
  have h_zero_le : (0 : usize).toNat ≤ lst.val.size := by
    rw [usize_zero_toNat]; omega
  have h_meas : lst.val.size - (0 : usize).toNat ≤ lst.val.size := by
    rw [usize_zero_toNat]; omega
  have h_init : (false = true → is_prime_nat (0 : u64).toNat) := by
    intro h; cases h
  obtain ⟨rv, rf, hres, h_live, _h_prime, _h_mem, _h_min⟩ :=
    largest_prime_at_correct lst h_bound lst.val.size (0 : usize) (0 : u64) false
      h_meas h_zero_le h_init
  -- rf must be false (no primes in [0, size)).
  have h_rf_false : rf = false := by
    cases hrf : rf
    · rfl
    · exfalso
      rcases h_live.mp hrf with hf | ⟨j, hj, h_jge, h_lj_prime⟩
      · cases hf
      · exact h_no_primes j hj h_lj_prime
  rw [hres, h_rf_false]
  simp only [pure_bind, RustM_ok_bind, rust_primitives.hax.logical_op.not,
             Bool.not_false, ↓reduceIte]
  rfl

theorem sum_largest_prime_eq_digit_sum_of_max_prime
    (lst : RustSlice u64) (p : u64)
    (h_bound : ∀ (i : Nat) (hi : i < lst.val.size), (lst.val[i]'hi).toNat < 2 ^ 32)
    (h_p_in : ∃ (i : Nat) (hi : i < lst.val.size), (lst.val[i]'hi) = p)
    (h_p_prime : is_prime_nat p.toNat)
    (h_p_max : ∀ (i : Nat) (hi : i < lst.val.size),
        is_prime_nat (lst.val[i]'hi).toNat → (lst.val[i]'hi).toNat ≤ p.toNat) :
    ∃ r : u64,
      clever_093_sum_largest_prime.sum_largest_prime lst = RustM.ok r
      ∧ r.toNat = digit_sum_nat p.toNat := by
  unfold clever_093_sum_largest_prime.sum_largest_prime
  have h_zero_le : (0 : usize).toNat ≤ lst.val.size := by
    rw [usize_zero_toNat]; omega
  have h_meas : lst.val.size - (0 : usize).toNat ≤ lst.val.size := by
    rw [usize_zero_toNat]; omega
  have h_init : (false = true → is_prime_nat (0 : u64).toNat) := by
    intro h; cases h
  obtain ⟨rv, rf, hres, h_live, h_rv_prime, h_mem, h_min⟩ :=
    largest_prime_at_correct lst h_bound lst.val.size (0 : usize) (0 : u64) false
      h_meas h_zero_le h_init
  obtain ⟨i_p, hi_p, h_lst_ip_eq_p⟩ := h_p_in
  have h_lst_ip_prime : is_prime_nat (lst.val[i_p]'hi_p).toNat := by
    rw [h_lst_ip_eq_p]; exact h_p_prime
  have h_rf_true : rf = true := by
    apply h_live.mpr; right
    refine ⟨i_p, hi_p, ?_, h_lst_ip_prime⟩
    rw [usize_zero_toNat]; omega
  have h_rv_is_prime : is_prime_nat rv.toNat := h_rv_prime h_rf_true
  obtain ⟨_, h_min_suffix⟩ := h_min h_rf_true
  have h_p_le_rv : p.toNat ≤ rv.toNat := by
    have h_lst_ip_le_rv : (lst.val[i_p]'hi_p).toNat ≤ rv.toNat := by
      apply h_min_suffix i_p hi_p _ h_lst_ip_prime
      rw [usize_zero_toNat]; omega
    rw [h_lst_ip_eq_p] at h_lst_ip_le_rv; exact h_lst_ip_le_rv
  -- From the new membership invariant: rv = best (impossible since found=false) or rv = l[j].
  have h_rv_le_p : rv.toNat ≤ p.toNat := by
    rcases h_mem h_rf_true with ⟨hf, _⟩ | ⟨j, hj, h_jge, h_rv_eq⟩
    · -- found = true is false.
      cases hf
    · -- rv = l[j]; l[j] is prime (since rv is prime); by h_p_max, l[j] ≤ p.
      have h_lj_prime : is_prime_nat (lst.val[j]'hj).toNat := by
        rw [← h_rv_eq]; exact h_rv_is_prime
      have h_lj_le_p : (lst.val[j]'hj).toNat ≤ p.toNat := h_p_max j hj h_lj_prime
      rw [h_rv_eq]; exact h_lj_le_p
  have h_rv_eq_p : rv.toNat = p.toNat := by omega
  -- Now we need to call digit_sum_at p 0 and show the result.
  -- Since rf = true, the !found branch goes to digit_sum_at p 0.
  have h_rv_toNat_lt : rv.toNat < 2 ^ 32 := by
    -- rv = l[j] for some j (in suffix), and h_bound gives l[j].toNat < 2^32.
    -- Hmm again need rv = l[j]. But we have rv.toNat = p.toNat.
    -- And p is in lst (by h_p_in), so by h_bound, p.toNat < 2^32. So rv.toNat < 2^32.
    have h_p_lt : p.toNat < 2 ^ 32 := by
      rw [← h_lst_ip_eq_p]; exact h_bound i_p hi_p
    rw [h_rv_eq_p]; exact h_p_lt
  -- digit_sum_at rv 0 succeeds.
  have h_digit_no_ov : (0 : u64).toNat + digit_sum_nat rv.toNat < 2 ^ 64 := by
    rw [u64_zero_toNat]
    have h_bound_d : digit_sum_nat rv.toNat ≤ 9 * 20 := digit_sum_nat_bound_u64 rv
    have : (9 * 20 : Nat) < 2 ^ 64 := by decide
    omega
  obtain ⟨v_ds, hv_ds_eq, hv_ds_toNat⟩ :=
    digit_sum_at_correct rv (0 : u64) h_digit_no_ov
  refine ⟨v_ds, ?_, ?_⟩
  · rw [hres, h_rf_true]
    simp only [pure_bind, RustM_ok_bind, rust_primitives.hax.logical_op.not,
               Bool.not_true, ↓reduceIte, Bool.false_eq_true]
    exact hv_ds_eq
  · rw [hv_ds_toNat, u64_zero_toNat, h_rv_eq_p]
    omega

end Clever_093_sum_largest_primeObligations
