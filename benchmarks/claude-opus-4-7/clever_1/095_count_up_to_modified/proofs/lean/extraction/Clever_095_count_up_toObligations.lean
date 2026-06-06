-- Companion obligations file for the `clever_095_count_up_to` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_095_count_up_to

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_095_count_up_toObligations

/-- Mathematical primality on `Nat`. -/
private def is_prime_nat (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ k : Nat, 2 ≤ k → k < p → ¬ k ∣ p

/-! ## Numeric helper lemmas (u64 ⇄ Nat bridges)
    Ported verbatim from `is_prime_modified` / `largest_prime_factor_modified`. -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem u64_two_toNat : (2 : u64).toNat = 2 := rfl
private theorem u64_one_toNat : (1 : u64).toNat = 1 := rfl
private theorem u64_zero_toNat : (0 : u64).toNat = 0 := rfl

private theorem two32_sq : (2 : Nat) ^ 32 * 2 ^ 32 = 2 ^ 64 := by decide
private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide
private theorem usize_size_eq_2_64 : USize64.size = 2 ^ 64 := by decide

/-- `(d+1)*(d+1) = d*d + 2*d + 1`. Avoids `ring` (Mathlib not imported). -/
private theorem nat_succ_sq (d : Nat) :
    (d + 1) * (d + 1) = d * d + 2 * d + 1 := by
  rw [Nat.mul_add, Nat.add_mul, Nat.add_mul,
      Nat.one_mul, Nat.mul_one]
  omega

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

/-! ## One-step unfold of `is_prime_at` -/

private theorem is_prime_at_unfold (n d : u64)
    (h_d_ne : d ≠ 0)
    (h_mul_fits : d.toNat * d.toNat < 2 ^ 64) :
    clever_095_count_up_to.is_prime_at n d =
      (if d.toNat * d.toNat > n.toNat then
        (RustM.ok true : RustM Bool)
       else if n.toNat % d.toNat = 0 then
        (RustM.ok false : RustM Bool)
       else
        clever_095_count_up_to.is_prime_at n (d + 1)) := by
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
  conv => lhs; unfold clever_095_count_up_to.is_prime_at
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

/-! ## Specialised branch lemmas -/

private theorem is_prime_at_base_true (n d : u64)
    (h_d_ne : d ≠ 0)
    (h_mul_fits : d.toNat * d.toNat < 2 ^ 64)
    (h_gt : d.toNat * d.toNat > n.toNat) :
    clever_095_count_up_to.is_prime_at n d = RustM.ok true := by
  rw [is_prime_at_unfold n d h_d_ne h_mul_fits, if_pos h_gt]

private theorem is_prime_at_found_false (n d : u64)
    (h_d_ge : 2 ≤ d.toNat)
    (h_le : d.toNat * d.toNat ≤ n.toNat)
    (h_dvd : d.toNat ∣ n.toNat) :
    clever_095_count_up_to.is_prime_at n d = RustM.ok false := by
  have h_d_ne : d ≠ 0 := u64_ne_zero_of_toNat_pos d (by omega)
  have h_mul_fits : d.toNat * d.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt h_le n.toNat_lt
  have h_not_gt : ¬ d.toNat * d.toNat > n.toNat := by omega
  have h_mod_zero : n.toNat % d.toNat = 0 := by
    obtain ⟨k, hk⟩ := h_dvd
    rw [hk, Nat.mul_mod_right]
  rw [is_prime_at_unfold n d h_d_ne h_mul_fits, if_neg h_not_gt, if_pos h_mod_zero]

/-- If `is_prime_at n d` succeeds, then `d.toNat * d.toNat < 2^64`. -/
private theorem mul_fits_of_ok (n d : u64) (b : Bool)
    (h_d_ne : d ≠ 0)
    (hat : clever_095_count_up_to.is_prime_at n d = RustM.ok b) :
    d.toNat * d.toNat < 2 ^ 64 := by
  by_cases h_fits : d.toNat * d.toNat < 2 ^ 64
  · exact h_fits
  · exfalso
    have h_ge : 2 ^ 64 ≤ d.toNat * d.toNat := Nat.le_of_not_lt h_fits
    have h_fail : (d *? d : RustM u64) = .fail .integerOverflow :=
      mul_self_fail d h_ge
    conv at hat => lhs; unfold clever_095_count_up_to.is_prime_at
    rw [h_fail] at hat
    simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, Option.bind] at hat
    cases hat

/-! ## Soundness of the "ok true" return value:
     No divisor of `n` exists in `[d, ⌊√n⌋]`. -/

private theorem is_prime_at_sound_true (n : u64) :
    ∀ (m : Nat) (d : u64),
      2 ≤ d.toNat →
      n.toNat - (d.toNat * d.toNat) ≤ m →
      clever_095_count_up_to.is_prime_at n d = RustM.ok true →
      ∀ k : Nat, d.toNat ≤ k → k * k ≤ n.toNat → ¬ k ∣ n.toNat := by
  intro m
  induction m with
  | zero =>
    intro d h_d_ge hm h_ok k h_k_ge h_k_dd h_k_dvd
    have h_d_ne : d ≠ 0 := u64_ne_zero_of_toNat_pos d (by omega)
    have h_dd_le_n : d.toNat * d.toNat ≤ n.toNat := by
      have h_dd_le_kk : d.toNat * d.toNat ≤ k * k := Nat.mul_le_mul h_k_ge h_k_ge
      omega
    have h_fits : d.toNat * d.toNat < 2 ^ 64 :=
      Nat.lt_of_le_of_lt h_dd_le_n n.toNat_lt
    by_cases h_gt : d.toNat * d.toNat > n.toNat
    · have h_dd_le_kk : d.toNat * d.toNat ≤ k * k := Nat.mul_le_mul h_k_ge h_k_ge
      omega
    · have h_dd_eq : d.toNat * d.toNat = n.toNat := by omega
      have h_k_eq_d : k = d.toNat := by
        rcases Nat.eq_or_lt_of_le h_k_ge with heq | hlt
        · exact heq.symm
        · exfalso
          have h_lt_sq : d.toNat * d.toNat < k * k :=
            Nat.mul_lt_mul_of_lt_of_le hlt (Nat.le_of_lt hlt) (by omega)
          omega
      have h_d_dvd : d.toNat ∣ n.toNat := h_k_eq_d ▸ h_k_dvd
      have h_false : clever_095_count_up_to.is_prime_at n d = RustM.ok false :=
        is_prime_at_found_false n d h_d_ge h_dd_le_n h_d_dvd
      rw [h_false] at h_ok
      injection h_ok with h_eq
      injection h_eq with h_eq'
      exact Bool.false_ne_true h_eq'
  | succ m ih =>
    intro d h_d_ge hm h_ok k h_k_ge h_k_dd h_k_dvd
    have h_d_ne : d ≠ 0 := u64_ne_zero_of_toNat_pos d (by omega)
    have h_fits := mul_fits_of_ok n d true h_d_ne h_ok
    by_cases h_gt : d.toNat * d.toNat > n.toNat
    · have h_dd_le_kk : d.toNat * d.toNat ≤ k * k := Nat.mul_le_mul h_k_ge h_k_ge
      omega
    · have h_dd_le_n : d.toNat * d.toNat ≤ n.toNat := Nat.le_of_not_lt h_gt
      by_cases h_mod : n.toNat % d.toNat = 0
      · have h_d_dvd : d.toNat ∣ n.toNat := Nat.dvd_of_mod_eq_zero h_mod
        have h_false : clever_095_count_up_to.is_prime_at n d = RustM.ok false :=
          is_prime_at_found_false n d h_d_ge h_dd_le_n h_d_dvd
        rw [h_false] at h_ok
        injection h_ok with h_eq
        injection h_eq with h_eq'
        exact absurd h_eq' (by decide)
      · have h_add_fits : d.toNat + 1 < 2 ^ 64 :=
          add_one_fits_of_dd_le_n n d h_dd_le_n
        have h_succ_toNat : (d + 1).toNat = d.toNat + 1 := succ_toNat d h_add_fits
        have h_succ_ge : 2 ≤ (d + 1).toNat := by rw [h_succ_toNat]; omega
        have h_meas_succ : n.toNat - ((d + 1).toNat * (d + 1).toNat) ≤ m := by
          rw [h_succ_toNat]
          have h_step : d.toNat * d.toNat + 1 ≤ (d.toNat + 1) * (d.toNat + 1) := by
            rw [nat_succ_sq d.toNat]; omega
          omega
        have h_ok_succ : clever_095_count_up_to.is_prime_at n (d + 1) = RustM.ok true := by
          have h_unf := is_prime_at_unfold n d h_d_ne h_fits
          rw [h_unf, if_neg h_gt, if_neg h_mod] at h_ok
          exact h_ok
        by_cases h_k_eq_d : k = d.toNat
        · have h_d_dvd : d.toNat ∣ n.toNat := h_k_eq_d ▸ h_k_dvd
          obtain ⟨q, hq⟩ := h_d_dvd
          have h_mz : n.toNat % d.toNat = 0 := by rw [hq]; exact Nat.mul_mod_right _ _
          exact h_mod h_mz
        · have h_k_ge_succ : (d + 1).toNat ≤ k := by rw [h_succ_toNat]; omega
          exact ih (d + 1) h_succ_ge h_meas_succ h_ok_succ k h_k_ge_succ h_k_dd h_k_dvd

/-! ## Soundness of the "ok false" return value:
     Some divisor of `n` exists in `[d, ⌊√n⌋]`. -/

private theorem is_prime_at_sound_false (n : u64) :
    ∀ (m : Nat) (d : u64),
      2 ≤ d.toNat →
      n.toNat - (d.toNat * d.toNat) ≤ m →
      clever_095_count_up_to.is_prime_at n d = RustM.ok false →
      ∃ k : Nat, d.toNat ≤ k ∧ k * k ≤ n.toNat ∧ k ∣ n.toNat := by
  intro m
  induction m with
  | zero =>
    intro d h_d_ge hm h_ok
    have h_d_ne : d ≠ 0 := u64_ne_zero_of_toNat_pos d (by omega)
    have h_fits := mul_fits_of_ok n d false h_d_ne h_ok
    by_cases h_gt : d.toNat * d.toNat > n.toNat
    · exfalso
      have h_true : clever_095_count_up_to.is_prime_at n d = RustM.ok true :=
        is_prime_at_base_true n d h_d_ne h_fits h_gt
      rw [h_true] at h_ok
      injection h_ok with h_eq
      injection h_eq with h_eq'
      exact absurd h_eq' (by decide)
    · -- d*d = n.toNat (m=0 case). Then d|n, contradiction with the assumption that
      -- the "false" branch was reached only via n%d ≠ 0. But that's only in the
      -- if-chain; here we don't have that assumption. We derive d|n directly.
      have h_dd_eq : d.toNat * d.toNat = n.toNat := by omega
      have h_dd_le_n : d.toNat * d.toNat ≤ n.toNat := by omega
      refine ⟨d.toNat, Nat.le_refl _, h_dd_le_n, ?_⟩
      -- d | n.toNat since n.toNat = d * d.
      rw [← h_dd_eq]
      exact ⟨d.toNat, rfl⟩
  | succ m ih =>
    intro d h_d_ge hm h_ok
    have h_d_ne : d ≠ 0 := u64_ne_zero_of_toNat_pos d (by omega)
    have h_fits := mul_fits_of_ok n d false h_d_ne h_ok
    by_cases h_gt : d.toNat * d.toNat > n.toNat
    · exfalso
      have h_true : clever_095_count_up_to.is_prime_at n d = RustM.ok true :=
        is_prime_at_base_true n d h_d_ne h_fits h_gt
      rw [h_true] at h_ok
      injection h_ok with h_eq
      injection h_eq with h_eq'
      exact absurd h_eq' (by decide)
    · have h_dd_le_n : d.toNat * d.toNat ≤ n.toNat := Nat.le_of_not_lt h_gt
      by_cases h_mod : n.toNat % d.toNat = 0
      · refine ⟨d.toNat, Nat.le_refl _, h_dd_le_n, Nat.dvd_of_mod_eq_zero h_mod⟩
      · have h_add_fits : d.toNat + 1 < 2 ^ 64 :=
          add_one_fits_of_dd_le_n n d h_dd_le_n
        have h_succ_toNat : (d + 1).toNat = d.toNat + 1 := succ_toNat d h_add_fits
        have h_succ_ge : 2 ≤ (d + 1).toNat := by rw [h_succ_toNat]; omega
        have h_meas_succ : n.toNat - ((d + 1).toNat * (d + 1).toNat) ≤ m := by
          rw [h_succ_toNat]
          have h_step : d.toNat * d.toNat + 1 ≤ (d.toNat + 1) * (d.toNat + 1) := by
            rw [nat_succ_sq d.toNat]; omega
          omega
        have h_unf := is_prime_at_unfold n d h_d_ne h_fits
        rw [h_unf, if_neg h_gt, if_neg h_mod] at h_ok
        obtain ⟨k, h_k_ge, h_k_dd, h_k_dvd⟩ :=
          ih (d + 1) h_succ_ge h_meas_succ h_ok
        refine ⟨k, ?_, h_k_dd, h_k_dvd⟩
        omega

/-! ## Boolean extraction from `is_prime` -/

private theorem is_prime_below_two (n : u64) (h : n.toNat < 2) :
    clever_095_count_up_to.is_prime n = RustM.ok false := by
  unfold clever_095_count_up_to.is_prime
  have h_lt : n < (2 : u64) := by
    apply UInt64.lt_iff_toNat_lt.mpr
    rw [u64_two_toNat]; exact h
  rw [show (n <? (2 : u64) : RustM Bool) = pure (decide (n < (2 : u64))) from rfl]
  simp only [pure_bind, decide_eq_true h_lt, if_true]
  rfl

private theorem is_prime_at_2_of_is_prime (n : u64) (hn : 2 ≤ n.toNat)
    (b : Bool) (h : clever_095_count_up_to.is_prime n = RustM.ok b) :
    clever_095_count_up_to.is_prime_at n (2 : u64) = RustM.ok b := by
  have h_n_not_lt_u : ¬ n < (2 : u64) := by
    intro hlt
    have := UInt64.lt_iff_toNat_lt.mp hlt
    rw [u64_two_toNat] at this; omega
  have h_dec_false : decide (n < (2 : u64)) = false := decide_eq_false h_n_not_lt_u
  conv at h => lhs; unfold clever_095_count_up_to.is_prime
  rw [show (n <? (2 : u64) : RustM Bool) = pure (decide (n < (2 : u64))) from rfl,
      h_dec_false] at h
  simp only [pure_bind, Bool.false_eq_true, if_false] at h
  exact h

/-- Soundness: `is_prime n = ok true → is_prime_nat n.toNat`. -/
private theorem is_prime_sound_true (n : u64)
    (h : clever_095_count_up_to.is_prime n = RustM.ok true) :
    is_prime_nat n.toNat := by
  have hn : 2 ≤ n.toNat := by
    by_cases h_lt : n.toNat < 2
    · exfalso
      rw [is_prime_below_two n h_lt] at h
      injection h with h_eq
      injection h_eq with h_eq'
      exact Bool.false_ne_true h_eq'
    · omega
  have h_at : clever_095_count_up_to.is_prime_at n (2 : u64) = RustM.ok true :=
    is_prime_at_2_of_is_prime n hn true h
  refine ⟨hn, ?_⟩
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
  have h_no_dvd :=
    is_prime_at_sound_true n (n.toNat) (2 : u64)
      (by rw [u64_two_toNat]; exact Nat.le_refl _)
      (by omega) h_at d_min
      (by rw [u64_two_toNat]; exact h_d_min_ge_2)
      h_dmin_sq_le_n h_dmin_dvd_n
  exact h_no_dvd

/-- Sound-false: `is_prime n = ok false → ¬ is_prime_nat n.toNat`. -/
private theorem is_prime_sound_false (n : u64)
    (h : clever_095_count_up_to.is_prime n = RustM.ok false) :
    ¬ is_prime_nat n.toNat := by
  rintro ⟨hn, h_no_dvd⟩
  have h_at : clever_095_count_up_to.is_prime_at n (2 : u64) = RustM.ok false :=
    is_prime_at_2_of_is_prime n hn false h
  obtain ⟨k, h_k_ge, h_k_dd, h_k_dvd⟩ :=
    is_prime_at_sound_false n n.toNat (2 : u64)
      (by rw [u64_two_toNat]; exact Nat.le_refl _)
      (by omega) h_at
  rw [u64_two_toNat] at h_k_ge
  have h_k_lt_n : k < n.toNat := by
    have h_2k_le_kk : 2 * k ≤ k * k := by
      have : k * 2 ≤ k * k := Nat.mul_le_mul_left k h_k_ge
      omega
    omega
  exact h_no_dvd k h_k_ge h_k_lt_n h_k_dvd

/-! ## Push helper for `Vec` (`extend_from_slice` of a 1-element chunk). -/

private def push_one (acc : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec u64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

/-! ## One-step reductions for `build_at` -/

/-- Out-of-bounds: `k ≥ n` → returns `acc`. -/
private theorem build_at_oob (n k : u64) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (h : n.toNat ≤ k.toNat) :
    clever_095_count_up_to.build_at n k acc = RustM.ok acc := by
  conv => lhs; unfold clever_095_count_up_to.build_at
  have h_ge_u : k ≥ n := UInt64.le_iff_toNat_le.mpr h
  have h_dec : decide (k ≥ n) = true := decide_eq_true h_ge_u
  simp only [show (k >=? n : RustM Bool) = pure (decide (k ≥ n)) from rfl,
             h_dec, pure_bind, ↓reduceIte]
  rfl

private theorem k_add_one_eq (n k : u64) (hk : k.toNat < n.toNat) :
    (k +? (1 : u64) : RustM u64) = RustM.ok (k + 1) := by
  have h_n_lt_2_64 : n.toNat < 2 ^ 64 := n.toNat_lt
  have h_no_ov_k : k.toNat + 1 < 2 ^ 64 := by omega
  show (rust_primitives.ops.arith.Add.add k 1 : RustM u64) = RustM.ok (k + 1)
  show (if BitVec.uaddOverflow k.toBitVec (1 : u64).toBitVec
        then (.fail .integerOverflow : RustM u64)
        else pure (k + 1)) = _
  have h_no_bv_k :
      BitVec.uaddOverflow k.toBitVec (1 : u64).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow k.toBitVec (1 : u64).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have h_ov : UInt64.addOverflow k 1 := hbo
      have hii := UInt64.addOverflow_iff.mp h_ov
      rw [u64_one_toNat] at hii
      omega
  rw [h_no_bv_k]; rfl

/-- Push step: `k < n ∧ is_prime k = ok true` → push `k`, recurse on `(k+1, acc++[k])`. -/
private theorem build_at_step_push (n k : u64) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hk : k.toNat < n.toNat)
    (h_prime : clever_095_count_up_to.is_prime k = RustM.ok true)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_095_count_up_to.build_at n k acc =
      clever_095_count_up_to.build_at n (k + 1) (push_one acc k h_acc) := by
  conv => lhs; unfold clever_095_count_up_to.build_at
  have h_not_ge : ¬ k ≥ n := by
    intro hle
    have := UInt64.le_iff_toNat_le.mp hle
    omega
  have h_dec_ge : decide (k ≥ n) = false := decide_eq_false h_not_ge
  have h_add_k : (k +? (1 : u64) : RustM u64) = RustM.ok (k + 1) :=
    k_add_one_eq n k hk
  simp only [show (k >=? n : RustM Bool) = pure (decide (k ≥ n)) from rfl,
             h_dec_ge, pure_bind, Bool.false_eq_true, ↓reduceIte,
             h_prime, RustM_ok_bind]
  rw [show (rust_primitives.unsize
            (RustArray.ofVec #v[k] : RustArray u64 1)
            : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[k], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size : acc.val.size + (#[k] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  rw [show (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
              ⟨#[k], one_lt_usize_size⟩
            : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
        = RustM.ok (push_one acc k h_acc) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  simp only [RustM_ok_bind]
  rw [h_add_k]
  rfl

/-- Skip step: `k < n ∧ is_prime k = ok false` → recurse on `(k+1, acc)`. -/
private theorem build_at_step_skip (n k : u64) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hk : k.toNat < n.toNat)
    (h_prime : clever_095_count_up_to.is_prime k = RustM.ok false) :
    clever_095_count_up_to.build_at n k acc =
      clever_095_count_up_to.build_at n (k + 1) acc := by
  conv => lhs; unfold clever_095_count_up_to.build_at
  have h_not_ge : ¬ k ≥ n := by
    intro hle
    have := UInt64.le_iff_toNat_le.mp hle
    omega
  have h_dec_ge : decide (k ≥ n) = false := decide_eq_false h_not_ge
  have h_add_k : (k +? (1 : u64) : RustM u64) = RustM.ok (k + 1) :=
    k_add_one_eq n k hk
  simp only [show (k >=? n : RustM Bool) = pure (decide (k ≥ n)) from rfl,
             h_dec_ge, pure_bind, Bool.false_eq_true, ↓reduceIte,
             h_prime, RustM_ok_bind, h_add_k]

/-- Inner-call-fail propagation. -/
private theorem build_at_step_inner_fail (n k : u64) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hk : k.toNat < n.toNat)
    (e : Error)
    (h_prime : clever_095_count_up_to.is_prime k = RustM.fail e) :
    clever_095_count_up_to.build_at n k acc = RustM.fail e := by
  conv => lhs; unfold clever_095_count_up_to.build_at
  have h_not_ge : ¬ k ≥ n := by
    intro hle
    have := UInt64.le_iff_toNat_le.mp hle
    omega
  have h_dec_ge : decide (k ≥ n) = false := decide_eq_false h_not_ge
  simp only [show (k >=? n : RustM Bool) = pure (decide (k ≥ n)) from rfl,
             h_dec_ge, pure_bind, Bool.false_eq_true, ↓reduceIte,
             h_prime]
  rfl

/-- Inner-call-diverge propagation. -/
private theorem build_at_step_inner_div (n k : u64) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hk : k.toNat < n.toNat)
    (h_prime : clever_095_count_up_to.is_prime k = RustM.div) :
    clever_095_count_up_to.build_at n k acc = RustM.div := by
  conv => lhs; unfold clever_095_count_up_to.build_at
  have h_not_ge : ¬ k ≥ n := by
    intro hle
    have := UInt64.le_iff_toNat_le.mp hle
    omega
  have h_dec_ge : decide (k ≥ n) = false := decide_eq_false h_not_ge
  simp only [show (k >=? n : RustM Bool) = pure (decide (k ≥ n)) from rfl,
             h_dec_ge, pure_bind, Bool.false_eq_true, ↓reduceIte,
             h_prime]
  rfl

/-! ## Strong induction over `build_at`.
     Now includes `h_acc_room` to bound `acc.val.size + (n.toNat - k.toNat)` so the
     `extend_from_slice` 1-element push never overflows `USize64.size`. -/

private theorem build_at_correct (n : u64) :
    ∀ (m : Nat) (k : u64) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
      (v : alloc.vec.Vec u64 alloc.alloc.Global),
      n.toNat - k.toNat ≤ m →
      k.toNat ≤ n.toNat →
      acc.val.size + (n.toNat - k.toNat) < USize64.size →
      clever_095_count_up_to.build_at n k acc = RustM.ok v →
      ∃ rest : List u64,
        v.val.toList = acc.val.toList ++ rest ∧
        (∀ x ∈ rest, is_prime_nat x.toNat) ∧
        rest.Pairwise (fun a b => a.toNat < b.toNat) ∧
        (∀ x ∈ rest, k.toNat ≤ x.toNat ∧ x.toNat < n.toNat) ∧
        (∀ p : Nat, is_prime_nat p → k.toNat ≤ p → p < n.toNat →
            ∃ x ∈ rest, x.toNat = p) := by
  intro m
  induction m with
  | zero =>
    intro k acc v hm hk_le h_room hres
    have hk_eq : k.toNat = n.toNat := by omega
    have hk_ge : n.toNat ≤ k.toNat := by omega
    rw [build_at_oob n k acc hk_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    refine ⟨[], ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · intro x hx; simp at hx
    · exact List.Pairwise.nil
    · intro x hx; simp at hx
    · intro p _ h_ge h_lt
      exfalso; omega
  | succ m ih =>
    intro k acc v hm hk_le h_room hres
    by_cases hk_ge : n.toNat ≤ k.toNat
    · have hk_eq : k.toNat = n.toNat := by omega
      rw [build_at_oob n k acc hk_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      refine ⟨[], ?_, ?_, ?_, ?_, ?_⟩
      · simp
      · intro x hx; simp at hx
      · exact List.Pairwise.nil
      · intro x hx; simp at hx
      · intro p _ h_ge h_lt
        exfalso; omega
    · have hk_lt : k.toNat < n.toNat := Nat.lt_of_not_le hk_ge
      have h_n_lt_2_64 : n.toNat < 2 ^ 64 := n.toNat_lt
      have h_no_ov_k : k.toNat + 1 < 2 ^ 64 := by omega
      have h_k1_toNat : (k + 1).toNat = k.toNat + 1 := succ_toNat k h_no_ov_k
      have h_k1_le : (k + 1).toNat ≤ n.toNat := by rw [h_k1_toNat]; omega
      have h_meas : n.toNat - (k + 1).toNat ≤ m := by rw [h_k1_toNat]; omega
      -- Room for the next iteration: acc' + (n - (k+1)) < USize64.size.
      have h_room_skip : acc.val.size + (n.toNat - (k + 1).toNat) < USize64.size := by
        rw [h_k1_toNat]; omega
      -- Acc size + 1 fits (used in push branch). From h_room: acc.val.size + (n.toNat - k.toNat) < USize64.size with n.toNat - k.toNat ≥ 1.
      have h_acc_succ : acc.val.size + 1 < USize64.size := by
        have h_diff_pos : 1 ≤ n.toNat - k.toNat := by omega
        omega
      -- Dispatch on inner is_prime k.
      generalize h_prime_def : clever_095_count_up_to.is_prime k = rprime
      cases rprime with
      | none =>
        exfalso
        have h_prime : clever_095_count_up_to.is_prime k = RustM.div := h_prime_def
        rw [build_at_step_inner_div n k acc hk_lt h_prime] at hres
        cases hres
      | some res =>
        cases res with
        | error e =>
          exfalso
          have h_prime : clever_095_count_up_to.is_prime k = RustM.fail e := h_prime_def
          rw [build_at_step_inner_fail n k acc hk_lt e h_prime] at hres
          cases hres
        | ok b =>
          have h_prime : clever_095_count_up_to.is_prime k = RustM.ok b := h_prime_def
          cases b with
          | true =>
            -- Push branch.
            rw [build_at_step_push n k acc hk_lt h_prime h_acc_succ] at hres
            -- Compute room after push: (acc+1) + (n - (k+1)) = acc + (n - k) < USize64.size.
            have h_push_size : (push_one acc k h_acc_succ).val.size = acc.val.size + 1 := by
              show (acc.val ++ #[k]).size = acc.val.size + 1
              rw [Array.size_append]; rfl
            have h_room_push :
                (push_one acc k h_acc_succ).val.size + (n.toNat - (k + 1).toNat) <
                  USize64.size := by
              rw [h_push_size, h_k1_toNat]; omega
            obtain ⟨rest', hval', hprime', hpw', hbound', hcompl'⟩ :=
              ih (k + 1) (push_one acc k h_acc_succ) v h_meas h_k1_le h_room_push hres
            refine ⟨k :: rest', ?_, ?_, ?_, ?_, ?_⟩
            · -- v.val.toList = acc.val.toList ++ (k :: rest')
              rw [hval']
              show (acc.val ++ #[k]).toList ++ rest' = acc.val.toList ++ k :: rest'
              simp
            · intro x hx
              rcases List.mem_cons.mp hx with h_eq | hxr
              · rw [h_eq]; exact is_prime_sound_true k h_prime
              · exact hprime' x hxr
            · refine List.Pairwise.cons ?_ hpw'
              intro y hy
              have := hbound' y hy
              rw [h_k1_toNat] at this
              omega
            · intro x hx
              rcases List.mem_cons.mp hx with h_eq | hxr
              · rw [h_eq]; exact ⟨Nat.le_refl _, hk_lt⟩
              · have := hbound' x hxr
                rw [h_k1_toNat] at this
                refine ⟨by omega, this.2⟩
            · intro p hp_prime h_p_ge h_p_lt
              by_cases h_p_eq_k : p = k.toNat
              · refine ⟨k, ?_, h_p_eq_k.symm⟩
                exact List.mem_cons_self
              · have h_p_ge_succ : (k + 1).toNat ≤ p := by
                  rw [h_k1_toNat]; omega
                obtain ⟨x, hx, hx_eq⟩ :=
                  hcompl' p hp_prime h_p_ge_succ h_p_lt
                exact ⟨x, List.mem_cons_of_mem _ hx, hx_eq⟩
          | false =>
            -- Skip branch.
            rw [build_at_step_skip n k acc hk_lt h_prime] at hres
            obtain ⟨rest', hval', hprime', hpw', hbound', hcompl'⟩ :=
              ih (k + 1) acc v h_meas h_k1_le h_room_skip hres
            refine ⟨rest', hval', hprime', hpw', ?_, ?_⟩
            · intro x hxr
              have := hbound' x hxr
              rw [h_k1_toNat] at this
              refine ⟨by omega, this.2⟩
            · intro p hp_prime h_p_ge h_p_lt
              by_cases h_p_eq_k : p = k.toNat
              · exfalso
                have h_not_prime : ¬ is_prime_nat k.toNat :=
                  is_prime_sound_false k h_prime
                apply h_not_prime
                rw [← h_p_eq_k]; exact hp_prime
              · have h_p_ge_succ : (k + 1).toNat ≤ p := by
                  rw [h_k1_toNat]; omega
                exact hcompl' p hp_prime h_p_ge_succ h_p_lt

/-! ## Top-level wrapper: count_up_to.
     Returns postconditions in terms of `v.val.toList` directly, avoiding the
     awkward `rest = v.val.toList` bridge in the top-level theorems. -/

private theorem count_up_to_aux (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_095_count_up_to.count_up_to n = RustM.ok v) :
    (∀ x ∈ v.val.toList, is_prime_nat x.toNat) ∧
    v.val.toList.Pairwise (fun a b => a.toNat < b.toNat) ∧
    (∀ x ∈ v.val.toList, x.toNat < n.toNat) ∧
    (∀ p : Nat, is_prime_nat p → p < n.toNat →
        ∃ x ∈ v.val.toList, x.toNat = p) := by
  unfold clever_095_count_up_to.count_up_to at hres
  have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new, RustM_ok_bind] at hres
  let acc0 : alloc.vec.Vec u64 alloc.alloc.Global := ⟨(List.nil).toArray, by grind⟩
  have h_zero_le : (0 : u64).toNat ≤ n.toNat := by
    rw [u64_zero_toNat]; omega
  have h_meas : n.toNat - (0 : u64).toNat ≤ n.toNat := by
    rw [u64_zero_toNat]; omega
  have h_room0 : acc0.val.size + (n.toNat - (0 : u64).toNat) < USize64.size := by
    show 0 + (n.toNat - (0 : u64).toNat) < USize64.size
    rw [u64_zero_toNat, Nat.zero_add]
    rw [usize_size_eq_2_64]
    exact n.toNat_lt
  obtain ⟨rest, hval, hprime, hpw, hbound, hcompl⟩ :=
    build_at_correct n n.toNat (0 : u64) acc0 v h_meas h_zero_le h_room0 hres
  have h_vlist : v.val.toList = rest := by
    rw [hval]
    show ((List.nil : List u64).toArray).toList ++ rest = rest
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    apply hprime
    rw [← h_vlist]; exact hx
  · rw [h_vlist]; exact hpw
  · intro x hx
    apply (hbound x ?_).2
    rw [← h_vlist]; exact hx
  · intro p hp_prime hp_lt
    have h_p_ge_zero : (0 : u64).toNat ≤ p := by rw [u64_zero_toNat]; omega
    obtain ⟨x, hx, hx_eq⟩ := hcompl p hp_prime h_p_ge_zero hp_lt
    refine ⟨x, ?_, hx_eq⟩
    rw [h_vlist]; exact hx

/-! ## Main contract clauses -/

/-- Boundary clause: when `n < 2`, the result is the empty `Vec`.
    Captures the Rust property test `empty_below_two`. -/
theorem empty_below_two
    (n : u64) (h : n.toNat < 2) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_095_count_up_to.count_up_to n = RustM.ok v ∧ v.val.size = 0 := by
  refine ⟨⟨(List.nil : List u64).toArray, by grind⟩, ?_, rfl⟩
  unfold clever_095_count_up_to.count_up_to
  have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new, RustM_ok_bind]
  by_cases h_n_zero : n.toNat = 0
  · have h_zero_ge : n.toNat ≤ (0 : u64).toNat := by rw [u64_zero_toNat]; omega
    rw [build_at_oob n (0 : u64) _ h_zero_ge]
  · have h_n_eq_1 : n.toNat = 1 := by omega
    have h_zero_lt : (0 : u64).toNat < n.toNat := by rw [u64_zero_toNat]; omega
    have h_prime_zero : clever_095_count_up_to.is_prime (0 : u64) = RustM.ok false :=
      is_prime_below_two (0 : u64) (by rw [u64_zero_toNat]; decide)
    rw [build_at_step_skip n (0 : u64) _ h_zero_lt h_prime_zero]
    have h_one_ge : n.toNat ≤ ((0 : u64) + 1).toNat := by
      have h_succ : ((0 : u64) + 1).toNat = (0 : u64).toNat + 1 :=
        succ_toNat (0 : u64) (by rw [u64_zero_toNat]; decide)
      rw [h_succ, u64_zero_toNat]; omega
    rw [build_at_oob n ((0 : u64) + 1) _ h_one_ge]

/-- Soundness clause: every element of the returned `Vec` is prime.
    Captures the Rust property test `all_elements_prime`. -/
theorem all_elements_prime
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_095_count_up_to.count_up_to n = RustM.ok v) :
    ∀ (k : Nat) (hk : k < v.val.size), is_prime_nat (v.val[k]'hk).toNat := by
  obtain ⟨hprime, _, _, _⟩ := count_up_to_aux n v hres
  intro k hk
  apply hprime
  -- v.val[k] ∈ v.val.toList
  have h_arr_mem : v.val[k]'hk ∈ v.val := Array.getElem_mem hk
  exact Array.mem_def.mp h_arr_mem

/-- Upper-bound clause: every element of the returned `Vec` is strictly
    less than `n`. Captures the Rust property test `all_elements_below_n`. -/
theorem all_elements_below_n
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_095_count_up_to.count_up_to n = RustM.ok v) :
    ∀ (k : Nat) (hk : k < v.val.size), (v.val[k]'hk).toNat < n.toNat := by
  obtain ⟨_, _, hbound, _⟩ := count_up_to_aux n v hres
  intro k hk
  apply hbound
  have h_arr_mem : v.val[k]'hk ∈ v.val := Array.getElem_mem hk
  exact Array.mem_def.mp h_arr_mem

/-- Ordering clause: consecutive entries of the returned `Vec` are strictly
    increasing. Captures the Rust property test `strictly_ascending`. -/
theorem strictly_ascending
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_095_count_up_to.count_up_to n = RustM.ok v) :
    ∀ (k : Nat) (hk : k + 1 < v.val.size),
      (v.val[k]'(Nat.lt_of_succ_lt hk)).toNat < (v.val[k + 1]'hk).toNat := by
  obtain ⟨_, hpw, _, _⟩ := count_up_to_aux n v hres
  intro k hk
  have hk1_list : k + 1 < v.val.toList.length := by simp [hk]
  have hk_list : k < v.val.toList.length := Nat.lt_of_succ_lt hk1_list
  have h_pw_at :=
    List.pairwise_iff_getElem.mp hpw k (k + 1) hk_list hk1_list (Nat.lt_succ_self _)
  -- h_pw_at : (v.val.toList[k]).toNat < (v.val.toList[k+1]).toNat
  -- Bridge via Array.getElem_toList (simp lemma rewrites toList[i] → array[i]).
  simp only [Array.getElem_toList] at h_pw_at
  exact h_pw_at

/-- Completeness clause: every prime in `[0, n)` appears in the returned
    `Vec`. Captures the Rust property test `complete`. -/
theorem complete
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_095_count_up_to.count_up_to n = RustM.ok v)
    (p : Nat) (hp_prime : is_prime_nat p) (hp_lt : p < n.toNat) :
    ∃ (k : Nat) (hk : k < v.val.size), (v.val[k]'hk).toNat = p := by
  obtain ⟨_, _, _, hcompl⟩ := count_up_to_aux n v hres
  obtain ⟨x, hx, hx_eq⟩ := hcompl p hp_prime hp_lt
  obtain ⟨k, hk_lt, hget⟩ := List.mem_iff_getElem.mp hx
  have hk_size : k < v.val.size := by simpa using hk_lt
  refine ⟨k, hk_size, ?_⟩
  -- hget : v.val.toList[k] = x. Bridge via Array.getElem_toList.
  simp only [Array.getElem_toList] at hget
  -- Now hget : v.val[k] = x (with implicit proofs erased / unified)
  exact hget ▸ hx_eq

end Clever_095_count_up_toObligations
