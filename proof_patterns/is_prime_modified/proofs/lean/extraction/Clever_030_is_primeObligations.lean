-- Companion obligations file for the `clever_030_is_prime` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_030_is_prime

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_030_is_primeObligations

/-! ## Numeric helper lemmas (u64 ⇄ Nat bridges) -/

private theorem u64_two_toNat : (2 : u64).toNat = 2 := rfl
private theorem u64_one_toNat : (1 : u64).toNat = 1 := rfl
private theorem u64_zero_toNat : (0 : u64).toNat = 0 := rfl

private theorem two32_sq : (2 : Nat) ^ 32 * 2 ^ 32 = 2 ^ 64 := by decide
private theorem two17_sq_lt_2_64 : (2 : Nat) ^ 17 * 2 ^ 17 < 2 ^ 64 := by decide
private theorem two17_sq_gt_2_32 : (2 : Nat) ^ 32 < (2 : Nat) ^ 17 * 2 ^ 17 := by decide

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

/-- `d *? d = .fail .integerOverflow` when `d.toNat * d.toNat` does NOT fit. -/
private theorem mul_self_fail (d : u64) (h : 2 ^ 64 ≤ d.toNat * d.toNat) :
    (d *? d : RustM u64) = .fail .integerOverflow := by
  show (rust_primitives.ops.arith.Mul.mul d d : RustM u64) = .fail .integerOverflow
  show (if BitVec.umulOverflow d.toBitVec d.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (d * d)) = _
  have h_ov : UInt64.mulOverflow d d := by
    rw [UInt64.mulOverflow_iff]; exact h
  have h_bv : BitVec.umulOverflow d.toBitVec d.toBitVec = true := by
    simpa [UInt64.mulOverflow] using h_ov
  rw [h_bv]; rfl

/-- `n %? d = pure (n % d)` when `d ≠ 0`. -/
private theorem mod_pure (n d : u64) (h : d ≠ 0) :
    (n %? d : RustM u64) = pure (n % d) := by
  show (rust_primitives.ops.arith.Rem.rem n d : RustM u64) = pure (n % d)
  show (if d = 0 then (.fail .divisionByZero : RustM u64) else pure (n % d)) = _
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

/-- `d ≠ 0` from `d.toNat ≥ 1`. -/
private theorem u64_ne_zero_of_toNat_pos (d : u64) (h : 1 ≤ d.toNat) : d ≠ 0 := by
  intro h_eq
  have h_zero : d.toNat = 0 := by rw [h_eq]; rfl
  omega

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

/-! ## One-step unfold of `has_divisor_at` -/

private theorem has_divisor_at_unfold (n d : u64)
    (h_d_ne : d ≠ 0)
    (h_mul_fits : d.toNat * d.toNat < 2 ^ 64) :
    clever_030_is_prime.has_divisor_at n d =
      (if d.toNat * d.toNat > n.toNat then
        (RustM.ok false : RustM Bool)
       else if n.toNat % d.toNat = 0 then
        (RustM.ok true : RustM Bool)
       else
        clever_030_is_prime.has_divisor_at n (d + 1)) := by
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
  conv => lhs; unfold clever_030_is_prime.has_divisor_at
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

/-- `(d + 1).toNat = d.toNat + 1` when the sum fits. -/
private theorem succ_toNat (d : u64) (h : d.toNat + 1 < 2 ^ 64) :
    (d + 1).toNat = d.toNat + 1 := by
  rw [UInt64.toNat_add_of_lt (by rw [u64_one_toNat]; exact h), u64_one_toNat]

/-! ## Specialised branch lemmas -/

private theorem has_divisor_at_found (n d : u64)
    (h_d_ge : 2 ≤ d.toNat)
    (h_le : d.toNat * d.toNat ≤ n.toNat)
    (h_dvd : d.toNat ∣ n.toNat) :
    clever_030_is_prime.has_divisor_at n d = RustM.ok true := by
  have h_d_ne : d ≠ 0 := u64_ne_zero_of_toNat_pos d (by omega)
  have h_mul_fits : d.toNat * d.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt h_le n.toNat_lt
  have h_not_gt : ¬ d.toNat * d.toNat > n.toNat := by omega
  have h_mod_zero : n.toNat % d.toNat = 0 := by
    obtain ⟨k, hk⟩ := h_dvd
    rw [hk, Nat.mul_mod_right]
  rw [has_divisor_at_unfold n d h_d_ne h_mul_fits, if_neg h_not_gt, if_pos h_mod_zero]

private theorem has_divisor_at_base (n d : u64)
    (h_d_ne : d ≠ 0)
    (h_mul_fits : d.toNat * d.toNat < 2 ^ 64)
    (h_gt : d.toNat * d.toNat > n.toNat) :
    clever_030_is_prime.has_divisor_at n d = RustM.ok false := by
  rw [has_divisor_at_unfold n d h_d_ne h_mul_fits, if_pos h_gt]

private theorem mul_fits_of_ok (n d : u64) (b : Bool)
    (h_d_ne : d ≠ 0)
    (hat : clever_030_is_prime.has_divisor_at n d = RustM.ok b) :
    d.toNat * d.toNat < 2 ^ 64 := by
  by_cases h_fits : d.toNat * d.toNat < 2 ^ 64
  · exact h_fits
  · exfalso
    have h_ge : 2 ^ 64 ≤ d.toNat * d.toNat := Nat.le_of_not_lt h_fits
    have h_fail : (d *? d : RustM u64) = .fail .integerOverflow :=
      mul_self_fail d h_ge
    conv at hat => lhs; unfold clever_030_is_prime.has_divisor_at
    rw [h_fail] at hat
    simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, Option.bind] at hat
    cases hat

/-! ## Finding a witness divisor -/

private theorem has_divisor_at_finds_witness (n : u64) :
    ∀ (m : Nat) (d : u64),
      2 ≤ d.toNat →
      (∃ d' : Nat, d.toNat ≤ d' ∧ d' - d.toNat ≤ m
          ∧ d' * d' ≤ n.toNat ∧ d' ∣ n.toNat) →
      clever_030_is_prime.has_divisor_at n d = RustM.ok true := by
  intro m
  induction m with
  | zero =>
    intro d h_d_ge hex
    obtain ⟨d', h_le, h_diff, h_dd, h_dvd⟩ := hex
    have h_eq : d' = d.toNat := by omega
    rw [h_eq] at h_dd h_dvd
    exact has_divisor_at_found n d h_d_ge h_dd h_dvd
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
    rw [has_divisor_at_unfold n d h_d_ne h_fits, if_neg h_not_gt]
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

/-! ## Completeness workhorse

If `n.toNat < 2 ^ 32`, no `k ∈ [d.toNat, 2 ^ 17]` divides `n.toNat`, and
`d.toNat ≤ 2 ^ 17`, then `has_divisor_at n d = ok false`.

The bound `2 ^ 17` is chosen because:
  - At `d.toNat = 2 ^ 17`, we have `d * d = 2 ^ 34 > 2 ^ 32 > n.toNat`, so the
    recursion exits via the `d * d > n` branch.
  - For `d.toNat ≤ 2 ^ 17`, `d * d ≤ 2 ^ 34 < 2 ^ 64`, so no overflow occurs.

The induction measure is `2 ^ 17 - d.toNat`. -/

private theorem has_divisor_at_complete_aux (n : u64) (h_n_fit : n.toNat < 2 ^ 32) :
    ∀ (m : Nat) (d : u64),
      (2 : Nat) ^ 17 - d.toNat ≤ m →
      2 ≤ d.toNat →
      d.toNat ≤ (2 : Nat) ^ 17 →
      (∀ k : Nat, d.toNat ≤ k → k * k ≤ n.toNat → ¬ k ∣ n.toNat) →
      clever_030_is_prime.has_divisor_at n d = RustM.ok false := by
  intro m
  induction m with
  | zero =>
    intro d h_m h_d_ge h_d_le h_no_dvd
    -- d.toNat = 2^17, so d*d = 2^34 > 2^32 > n.toNat.
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
    exact has_divisor_at_base n d h_d_ne h_dd_fits h_gt
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
      exact has_divisor_at_base n d h_d_ne h_dd_fits h_gt
    · have h_d_lt_top : d.toNat < (2 : Nat) ^ 17 := by omega
      -- d * d ≤ (2^17 - 1)^2 < 2^34 < 2^64
      have h_dd_lt : d.toNat * d.toNat < (2 : Nat) ^ 17 * 2 ^ 17 := by
        exact Nat.mul_lt_mul_of_lt_of_lt h_d_lt_top h_d_lt_top
      have h_dd_fits : d.toNat * d.toNat < 2 ^ 64 :=
        Nat.lt_trans h_dd_lt two17_sq_lt_2_64
      have h_d_ne : d ≠ 0 := u64_ne_zero_of_toNat_pos d (by omega)
      rw [has_divisor_at_unfold n d h_d_ne h_dd_fits]
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

/-! ## Boolean extraction from `is_prime` -/

private theorem has_divisor_at_2_eq_false_of_is_prime_true (n : u64)
    (hn : 2 ≤ n.toNat)
    (h : clever_030_is_prime.is_prime n = RustM.ok true) :
    clever_030_is_prime.has_divisor_at n (2 : u64) = RustM.ok false := by
  have h_n_not_lt_u : ¬ n < (2 : u64) := by
    intro hlt
    have := UInt64.lt_iff_toNat_lt.mp hlt
    rw [u64_two_toNat] at this; omega
  have h_dec_false : decide (n < (2 : u64)) = false := decide_eq_false h_n_not_lt_u
  conv at h => lhs; unfold clever_030_is_prime.is_prime
  rw [show (n <? (2 : u64) : RustM Bool) = pure (decide (n < (2 : u64))) from rfl,
      h_dec_false] at h
  simp only [pure_bind, Bool.false_eq_true, if_false] at h
  cases hh : clever_030_is_prime.has_divisor_at n (2 : u64) with
  | none => rw [hh] at h; cases h
  | some r =>
    cases r with
    | error e => rw [hh] at h; cases h
    | ok b =>
      cases b with
      | true => rw [hh] at h; cases h
      | false => rfl

private theorem is_prime_true_of_has_divisor_at_2_false (n : u64)
    (hn : 2 ≤ n.toNat)
    (h : clever_030_is_prime.has_divisor_at n (2 : u64) = RustM.ok false) :
    clever_030_is_prime.is_prime n = RustM.ok true := by
  unfold clever_030_is_prime.is_prime
  have h_n_not_lt_u : ¬ n < (2 : u64) := by
    intro hlt
    have := UInt64.lt_iff_toNat_lt.mp hlt
    rw [u64_two_toNat] at this; omega
  have h_dec_false : decide (n < (2 : u64)) = false := decide_eq_false h_n_not_lt_u
  rw [show (n <? (2 : u64) : RustM Bool) = pure (decide (n < (2 : u64))) from rfl,
      h_dec_false]
  simp only [pure_bind, Bool.false_eq_true, if_false]
  rw [h]
  rfl

private theorem is_prime_false_of_has_divisor_at_2_true (n : u64)
    (hn : 2 ≤ n.toNat)
    (h : clever_030_is_prime.has_divisor_at n (2 : u64) = RustM.ok true) :
    clever_030_is_prime.is_prime n = RustM.ok false := by
  unfold clever_030_is_prime.is_prime
  have h_n_not_lt_u : ¬ n < (2 : u64) := by
    intro hlt
    have := UInt64.lt_iff_toNat_lt.mp hlt
    rw [u64_two_toNat] at this; omega
  have h_dec_false : decide (n < (2 : u64)) = false := decide_eq_false h_n_not_lt_u
  rw [show (n <? (2 : u64) : RustM Bool) = pure (decide (n < (2 : u64))) from rfl,
      h_dec_false]
  simp only [pure_bind, Bool.false_eq_true, if_false]
  rw [h]
  rfl

/-! ## Main contract clauses -/

/-- Boundary clause: values below 2 are never prime. -/
theorem is_prime_below_two (n : u64) (h : n.toNat < 2) :
    clever_030_is_prime.is_prime n = RustM.ok false := by
  unfold clever_030_is_prime.is_prime
  have h_lt : n < (2 : u64) := by
    apply UInt64.lt_iff_toNat_lt.mpr
    rw [u64_two_toNat]; exact h
  rw [show (n <? (2 : u64) : RustM Bool) = pure (decide (n < (2 : u64))) from rfl]
  simp only [pure_bind, decide_eq_true h_lt, if_true]
  rfl

/-- Soundness: if `is_prime n = ok true`, then no `k ∈ [2, n)` divides `n.toNat`. -/
theorem is_prime_sound (n : u64)
    (h : clever_030_is_prime.is_prime n = RustM.ok true) :
    ∀ k : Nat, 2 ≤ k → k < n.toNat → ¬ k ∣ n.toNat := by
  have hn : 2 ≤ n.toNat := by
    by_cases h_lt : n.toNat < 2
    · exfalso
      rw [is_prime_below_two n h_lt] at h
      exact absurd h (by decide)
    · omega
  have h_at : clever_030_is_prime.has_divisor_at n (2 : u64) = RustM.ok false :=
    has_divisor_at_2_eq_false_of_is_prime_true n hn h
  intro k h_k_ge h_k_lt h_dvd
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
  -- d_min = min(k, q). d_min ≥ 2, d_min * d_min ≤ k * q = n.toNat, d_min ∣ n.toNat.
  let d_min := min k q
  have h_d_min_def : d_min = min k q := rfl
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
  have h_finds : clever_030_is_prime.has_divisor_at n (2 : u64) = RustM.ok true :=
    has_divisor_at_finds_witness n (d_min - 2) (2 : u64)
      (by rw [u64_two_toNat]; exact Nat.le_refl _)
      ⟨d_min, h_2_le_dmin, h_diff_bound, h_dmin_sq_le_n, h_dmin_dvd_n⟩
  rw [h_at] at h_finds
  exact absurd h_finds (by decide)

/-- Completeness. -/
theorem is_prime_complete (n : u64)
    (hn : 2 ≤ n.toNat)
    (h_fit : n.toNat < 2 ^ 32)
    (h_prime : ∀ k : Nat, 2 ≤ k → k < n.toNat → ¬ k ∣ n.toNat) :
    clever_030_is_prime.is_prime n = RustM.ok true := by
  -- Apply has_divisor_at_complete_aux at d = 2.
  have h_2_ge : 2 ≤ (2 : u64).toNat := by rw [u64_two_toNat]; exact Nat.le_refl _
  have h_2_le_top : (2 : u64).toNat ≤ (2 : Nat) ^ 17 := by
    rw [u64_two_toNat]; decide
  -- The hypothesis h_no_dvd at d = 2: ∀ k, 2 ≤ k, k * k ≤ n, ¬ k ∣ n.
  have h_no_dvd : ∀ k : Nat, (2 : u64).toNat ≤ k → k * k ≤ n.toNat →
      ¬ k ∣ n.toNat := by
    intro k h_k_ge h_k_dd h_k_dvd
    rw [u64_two_toNat] at h_k_ge
    -- From k * k ≤ n.toNat and 2 ≤ k: 2 * k ≤ k * k ≤ n.toNat, so k < n.toNat.
    have h_2k_le_kk : 2 * k ≤ k * k := by
      have : 2 * k = k * 2 := Nat.mul_comm 2 k
      rw [this]
      exact Nat.mul_le_mul_left k h_k_ge
    have h_2k_le_n : 2 * k ≤ n.toNat := Nat.le_trans h_2k_le_kk h_k_dd
    have h_k_lt_n : k < n.toNat := by omega
    exact h_prime k h_k_ge h_k_lt_n h_k_dvd
  have h_at : clever_030_is_prime.has_divisor_at n (2 : u64) = RustM.ok false :=
    has_divisor_at_complete_aux n h_fit
      ((2 : Nat) ^ 17 - (2 : u64).toNat) (2 : u64)
      (Nat.le_refl _) (by rw [u64_two_toNat]; exact Nat.le_refl _) h_2_le_top h_no_dvd
  exact is_prime_true_of_has_divisor_at_2_false n hn h_at

/-- Composite product. -/
theorem is_prime_product_is_composite (a b : u64)
    (ha : 2 ≤ a.toNat) (hb : 2 ≤ b.toNat)
    (h_fit : a.toNat * b.toNat < 2 ^ 64) :
    clever_030_is_prime.is_prime (a * b) = RustM.ok false := by
  let c := a * b
  have h_c_toNat : c.toNat = a.toNat * b.toNat := UInt64.toNat_mul_of_lt h_fit
  have h_c_ge_4 : 4 ≤ c.toNat := by
    rw [h_c_toNat]
    have h_ab : 2 * 2 ≤ a.toNat * b.toNat := Nat.mul_le_mul ha hb
    omega
  have h_c_ge_2 : 2 ≤ c.toNat := by omega
  let d_min := min a.toNat b.toNat
  have h_d_min_def : d_min = min a.toNat b.toNat := rfl
  have h_d_min_ge_2 : 2 ≤ d_min := Nat.le_min.mpr ⟨ha, hb⟩
  have h_dmin_le_a : d_min ≤ a.toNat := Nat.min_le_left a.toNat b.toNat
  have h_dmin_le_b : d_min ≤ b.toNat := Nat.min_le_right a.toNat b.toNat
  have h_dmin_sq_le : d_min * d_min ≤ c.toNat := by
    rw [h_c_toNat]; exact Nat.mul_le_mul h_dmin_le_a h_dmin_le_b
  have h_dmin_dvd : d_min ∣ c.toNat := by
    rw [h_c_toNat]
    rcases Nat.le_total a.toNat b.toNat with hab | hab
    · have h_eq : d_min = a.toNat := Nat.min_eq_left hab
      rw [h_eq]; exact Nat.dvd_mul_right a.toNat b.toNat
    · have h_eq : d_min = b.toNat := Nat.min_eq_right hab
      rw [h_eq]; exact Nat.dvd_mul_left b.toNat a.toNat
  have h_2_le_dmin : (2 : u64).toNat ≤ d_min := by rw [u64_two_toNat]; exact h_d_min_ge_2
  have h_diff_bound : d_min - (2 : u64).toNat ≤ d_min - 2 := by
    rw [u64_two_toNat]; exact Nat.le_refl _
  have h_at : clever_030_is_prime.has_divisor_at c (2 : u64) = RustM.ok true :=
    has_divisor_at_finds_witness c (d_min - 2) (2 : u64)
      (by rw [u64_two_toNat]; exact Nat.le_refl _)
      ⟨d_min, h_2_le_dmin, h_diff_bound, h_dmin_sq_le, h_dmin_dvd⟩
  exact is_prime_false_of_has_divisor_at_2_true c h_c_ge_2 h_at

end Clever_030_is_primeObligations
