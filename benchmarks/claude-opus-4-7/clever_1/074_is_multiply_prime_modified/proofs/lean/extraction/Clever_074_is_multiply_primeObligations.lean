-- Companion obligations file for the `clever_074_is_multiply_prime` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_074_is_multiply_prime

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_074_is_multiply_primeObligations

/-! ## Spec-side oracles -/

/-- Mathematical primality on `Nat`. -/
private def is_prime_nat (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ k : Nat, 2 ≤ k → k < p → ¬ k ∣ p

/-- `n` is the product of exactly three primes (counted with multiplicity). -/
private def is_multiply_prime_nat (n : Nat) : Prop :=
  ∃ p q r : Nat, is_prime_nat p ∧ is_prime_nat q ∧ is_prime_nat r
    ∧ p * q * r = n

/-! ## Concrete unit pins (from the `small_cases` test) -/

theorem small_cases_8 :
    clever_074_is_multiply_prime.is_multiply_prime (8 : u64) = RustM.ok true := by
  native_decide

theorem small_cases_12 :
    clever_074_is_multiply_prime.is_multiply_prime (12 : u64) = RustM.ok true := by
  native_decide

theorem small_cases_27 :
    clever_074_is_multiply_prime.is_multiply_prime (27 : u64) = RustM.ok true := by
  native_decide

theorem small_cases_30 :
    clever_074_is_multiply_prime.is_multiply_prime (30 : u64) = RustM.ok true := by
  native_decide

theorem small_cases_105 :
    clever_074_is_multiply_prime.is_multiply_prime (105 : u64) = RustM.ok true := by
  native_decide

theorem small_cases_1 :
    clever_074_is_multiply_prime.is_multiply_prime (1 : u64) = RustM.ok false := by
  native_decide

theorem small_cases_2 :
    clever_074_is_multiply_prime.is_multiply_prime (2 : u64) = RustM.ok false := by
  native_decide

theorem small_cases_4 :
    clever_074_is_multiply_prime.is_multiply_prime (4 : u64) = RustM.ok false := by
  native_decide

theorem small_cases_6 :
    clever_074_is_multiply_prime.is_multiply_prime (6 : u64) = RustM.ok false := by
  native_decide

theorem small_cases_7 :
    clever_074_is_multiply_prime.is_multiply_prime (7 : u64) = RustM.ok false := by
  native_decide

theorem small_cases_24 :
    clever_074_is_multiply_prime.is_multiply_prime (24 : u64) = RustM.ok false := by
  native_decide

/-! ## Numeric helper lemmas (u64 ⇄ Nat bridges) -/

private theorem u64_two_toNat : (2 : u64).toNat = 2 := rfl
private theorem u64_one_toNat : (1 : u64).toNat = 1 := rfl
private theorem u64_zero_toNat : (0 : u64).toNat = 0 := rfl
private theorem u64_eight_toNat : (8 : u64).toNat = 8 := rfl

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

/-! ## One-step unfold of `smallest_prime_at` -/

private theorem smallest_prime_at_unfold (m d : u64)
    (h_d_ne : d ≠ 0)
    (h_mul_fits : d.toNat * d.toNat < 2 ^ 64) :
    clever_074_is_multiply_prime.smallest_prime_at m d =
      (if d.toNat * d.toNat > m.toNat then
        (RustM.ok m : RustM u64)
       else if m.toNat % d.toNat = 0 then
        (RustM.ok d : RustM u64)
       else
        clever_074_is_multiply_prime.smallest_prime_at m (d + 1)) := by
  have h_dd_eq : (d *? d : RustM u64) = pure (d * d) :=
    mul_self_pure d h_mul_fits
  have h_dd_toNat : (d * d).toNat = d.toNat * d.toNat :=
    UInt64.toNat_mul_of_lt h_mul_fits
  have h_mod_eq : (m %? d : RustM u64) = pure (m % d) := mod_pure m d h_d_ne
  have h_mod_toNat : (m % d).toNat = m.toNat % d.toNat := UInt64.toNat_mod m d
  have h_gt_def : ((d * d) >? m : RustM Bool) = pure (decide ((d * d) > m)) := rfl
  have h_eq_def : ((m % d) ==? (0 : u64) : RustM Bool) =
      pure (decide ((m % d) = (0 : u64))) := rfl
  have h_gt_iff : ((d * d) > m) ↔ (d.toNat * d.toNat > m.toNat) := by
    constructor
    · intro h
      have := UInt64.lt_iff_toNat_lt.mp h
      rw [h_dd_toNat] at this; exact this
    · intro h
      apply UInt64.lt_iff_toNat_lt.mpr
      rw [h_dd_toNat]; exact h
  have h_eq_iff : ((m % d) = (0 : u64)) ↔ (m.toNat % d.toNat = 0) := by
    constructor
    · intro h
      have := congrArg UInt64.toNat h
      rw [h_mod_toNat, u64_zero_toNat] at this
      exact this
    · intro h
      apply UInt64.toNat_inj.mp
      rw [h_mod_toNat, u64_zero_toNat]
      exact h
  conv => lhs; unfold clever_074_is_multiply_prime.smallest_prime_at
  rw [h_dd_eq]
  simp only [pure_bind]
  rw [h_gt_def]
  simp only [pure_bind]
  by_cases h_gt : d.toNat * d.toNat > m.toNat
  · have h_gt_u : (d * d) > m := h_gt_iff.mpr h_gt
    rw [if_pos (decide_eq_true h_gt_u), if_pos h_gt]
    rfl
  · have h_not_gt_u : ¬ (d * d) > m := fun h => h_gt (h_gt_iff.mp h)
    have h_dec_gt : (decide ((d * d) > m)) = false := decide_eq_false h_not_gt_u
    rw [h_dec_gt, if_neg h_gt]
    simp only [Bool.false_eq_true, if_false]
    rw [h_mod_eq]
    simp only [pure_bind]
    rw [h_eq_def]
    simp only [pure_bind]
    by_cases h_mod : m.toNat % d.toNat = 0
    · have h_mod_u : (m % d) = (0 : u64) := h_eq_iff.mpr h_mod
      rw [if_pos (decide_eq_true h_mod_u), if_pos h_mod]
      rfl
    · have h_not_mod_u : ¬ (m % d) = (0 : u64) := fun h => h_mod (h_eq_iff.mp h)
      have h_dec_mod : (decide ((m % d) = (0 : u64))) = false :=
        decide_eq_false h_not_mod_u
      rw [h_dec_mod, if_neg h_mod]
      simp only [Bool.false_eq_true, if_false]
      have h_add_fits : d.toNat + 1 < 2 ^ 64 :=
        add_one_fits_of_dd_le_n m d (Nat.le_of_not_lt h_gt)
      rw [add_one_pure d h_add_fits]
      simp only [pure_bind]

/-! ## Main spec for `smallest_prime_at`. -/

private theorem smallest_prime_at_spec_aux
    (m : u64) (h_m_lo : 2 ≤ m.toNat) (h_m_hi : m.toNat < 2 ^ 32) :
    ∀ (steps : Nat) (d : u64),
      (2 : Nat) ^ 17 - d.toNat ≤ steps →
      2 ≤ d.toNat →
      d.toNat ≤ (2 : Nat) ^ 17 →
      (∀ k : Nat, 2 ≤ k → k < d.toNat → ¬ k ∣ m.toNat) →
      ∃ r : u64,
        clever_074_is_multiply_prime.smallest_prime_at m d = RustM.ok r
        ∧ 2 ≤ r.toNat
        ∧ r.toNat ≤ m.toNat
        ∧ r.toNat ∣ m.toNat
        ∧ ∀ k : Nat, 2 ≤ k → k < r.toNat → ¬ k ∣ m.toNat := by
  intro steps
  induction steps with
  | zero =>
    intro d h_m h_d_ge h_d_le h_no_dvd
    have h_d_eq : d.toNat = (2 : Nat) ^ 17 := by omega
    have h_dd_eq : d.toNat * d.toNat = (2 : Nat) ^ 17 * 2 ^ 17 := by rw [h_d_eq]
    have h_gt : d.toNat * d.toNat > m.toNat := by
      rw [h_dd_eq]
      have h2 : (2 : Nat) ^ 32 < 2 ^ 17 * 2 ^ 17 := two17_sq_gt_2_32
      omega
    have h_dd_fits : d.toNat * d.toNat < 2 ^ 64 := by
      rw [h_dd_eq]; exact two17_sq_lt_2_64
    have h_d_ne : d ≠ 0 := u64_ne_zero_of_toNat_pos d (by omega)
    refine ⟨m, ?_, h_m_lo, Nat.le_refl _, Nat.dvd_refl _, ?_⟩
    · rw [smallest_prime_at_unfold m d h_d_ne h_dd_fits, if_pos h_gt]
    · intro k h_k_ge h_k_lt h_dvd
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
      have h_dmin_sq_le_m : d_min * d_min ≤ m.toNat := by
        have h1 : d_min * d_min ≤ k * q := Nat.mul_le_mul h_dmin_le_k h_dmin_le_q
        rw [← hq] at h1; exact h1
      have h_dmin_dvd_m : d_min ∣ m.toNat := by
        rcases Nat.le_total k q with hkq | hkq
        · have h_eq : d_min = k := Nat.min_eq_left hkq
          rw [h_eq, hq]
          exact Nat.dvd_mul_right k q
        · have h_eq : d_min = q := Nat.min_eq_right hkq
          rw [h_eq, hq]
          exact Nat.dvd_mul_left q k
      have h_dmin_lt_d : d_min < d.toNat := by
        rw [h_d_eq]
        have h1 : d_min * d_min < (2 : Nat) ^ 17 * 2 ^ 17 := by
          have h_a : d_min * d_min ≤ m.toNat := h_dmin_sq_le_m
          have h_b : d_min * d_min < 2 ^ 32 := Nat.lt_of_le_of_lt h_a h_m_hi
          have h32 : (2 : Nat) ^ 32 < 2 ^ 17 * 2 ^ 17 := two17_sq_gt_2_32
          omega
        rcases Nat.lt_or_ge d_min ((2 : Nat) ^ 17) with h_lt | h_ge
        · exact h_lt
        · exfalso
          have h_sq_ge : (2 : Nat) ^ 17 * 2 ^ 17 ≤ d_min * d_min :=
            Nat.mul_le_mul h_ge h_ge
          omega
      exact (h_no_dvd d_min h_d_min_ge_2 h_dmin_lt_d h_dmin_dvd_m).elim
  | succ steps ih =>
    intro d h_m h_d_ge h_d_le h_no_dvd
    by_cases h_at_top : d.toNat = (2 : Nat) ^ 17
    · have h_dd_eq : d.toNat * d.toNat = (2 : Nat) ^ 17 * 2 ^ 17 := by rw [h_at_top]
      have h_gt : d.toNat * d.toNat > m.toNat := by
        rw [h_dd_eq]
        have h2 : (2 : Nat) ^ 32 < 2 ^ 17 * 2 ^ 17 := two17_sq_gt_2_32
        omega
      have h_dd_fits : d.toNat * d.toNat < 2 ^ 64 := by
        rw [h_dd_eq]; exact two17_sq_lt_2_64
      have h_d_ne : d ≠ 0 := u64_ne_zero_of_toNat_pos d (by omega)
      refine ⟨m, ?_, h_m_lo, Nat.le_refl _, Nat.dvd_refl _, ?_⟩
      · rw [smallest_prime_at_unfold m d h_d_ne h_dd_fits, if_pos h_gt]
      · intro k h_k_ge h_k_lt h_dvd
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
        have h_dmin_sq_le_m : d_min * d_min ≤ m.toNat := by
          have h1 : d_min * d_min ≤ k * q := Nat.mul_le_mul h_dmin_le_k h_dmin_le_q
          rw [← hq] at h1; exact h1
        have h_dmin_dvd_m : d_min ∣ m.toNat := by
          rcases Nat.le_total k q with hkq | hkq
          · have h_eq : d_min = k := Nat.min_eq_left hkq
            rw [h_eq, hq]; exact Nat.dvd_mul_right k q
          · have h_eq : d_min = q := Nat.min_eq_right hkq
            rw [h_eq, hq]; exact Nat.dvd_mul_left q k
        have h_dmin_lt_d : d_min < d.toNat := by
          rw [h_at_top]
          have h1 : d_min * d_min < (2 : Nat) ^ 17 * 2 ^ 17 := by
            have h_lt32 : d_min * d_min < 2 ^ 32 :=
              Nat.lt_of_le_of_lt h_dmin_sq_le_m h_m_hi
            have h32 : (2 : Nat) ^ 32 < 2 ^ 17 * 2 ^ 17 := two17_sq_gt_2_32
            omega
          rcases Nat.lt_or_ge d_min ((2 : Nat) ^ 17) with h_lt | h_ge
          · exact h_lt
          · exfalso
            have h_sq_ge : (2 : Nat) ^ 17 * 2 ^ 17 ≤ d_min * d_min :=
              Nat.mul_le_mul h_ge h_ge
            omega
        exact (h_no_dvd d_min h_d_min_ge_2 h_dmin_lt_d h_dmin_dvd_m).elim
    · have h_d_lt_top : d.toNat < (2 : Nat) ^ 17 := by omega
      have h_dd_lt : d.toNat * d.toNat < (2 : Nat) ^ 17 * 2 ^ 17 := by
        exact Nat.mul_lt_mul_of_lt_of_lt h_d_lt_top h_d_lt_top
      have h_dd_fits : d.toNat * d.toNat < 2 ^ 64 :=
        Nat.lt_trans h_dd_lt two17_sq_lt_2_64
      have h_d_ne : d ≠ 0 := u64_ne_zero_of_toNat_pos d (by omega)
      rw [smallest_prime_at_unfold m d h_d_ne h_dd_fits]
      by_cases h_gt : d.toNat * d.toNat > m.toNat
      · rw [if_pos h_gt]
        refine ⟨m, rfl, h_m_lo, Nat.le_refl _, Nat.dvd_refl _, ?_⟩
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
        have h_dmin_sq_le_m : d_min * d_min ≤ m.toNat := by
          have h1 : d_min * d_min ≤ k * q := Nat.mul_le_mul h_dmin_le_k h_dmin_le_q
          rw [← hq] at h1; exact h1
        have h_dmin_dvd_m : d_min ∣ m.toNat := by
          rcases Nat.le_total k q with hkq | hkq
          · have h_eq : d_min = k := Nat.min_eq_left hkq
            rw [h_eq, hq]; exact Nat.dvd_mul_right k q
          · have h_eq : d_min = q := Nat.min_eq_right hkq
            rw [h_eq, hq]; exact Nat.dvd_mul_left q k
        have h_dmin_lt_d : d_min < d.toNat := by
          rcases Nat.lt_or_ge d_min d.toNat with h_lt | h_ge
          · exact h_lt
          · exfalso
            have h_sq_ge : d.toNat * d.toNat ≤ d_min * d_min :=
              Nat.mul_le_mul h_ge h_ge
            omega
        exact (h_no_dvd d_min h_d_min_ge_2 h_dmin_lt_d h_dmin_dvd_m).elim
      · rw [if_neg h_gt]
        have h_dd_le_m : d.toNat * d.toNat ≤ m.toNat := Nat.le_of_not_lt h_gt
        by_cases h_mod : m.toNat % d.toNat = 0
        · rw [if_pos h_mod]
          have h_d_le_m : d.toNat ≤ m.toNat := by
            have h1 : d.toNat ≤ d.toNat * d.toNat := Nat.le_mul_of_pos_left _ (by omega)
            omega
          refine ⟨d, rfl, h_d_ge, h_d_le_m, Nat.dvd_of_mod_eq_zero h_mod, ?_⟩
          intro k h_k_ge h_k_lt h_dvd
          exact h_no_dvd k h_k_ge h_k_lt h_dvd
        · rw [if_neg h_mod]
          have h_add_fits : d.toNat + 1 < 2 ^ 64 :=
            add_one_fits_of_dd_le_n m d h_dd_le_m
          have h_succ_toNat : (d + 1).toNat = d.toNat + 1 := succ_toNat d h_add_fits
          have h_succ_ge : 2 ≤ (d + 1).toNat := by rw [h_succ_toNat]; omega
          have h_succ_le : (d + 1).toNat ≤ (2 : Nat) ^ 17 := by
            rw [h_succ_toNat]; omega
          have h_succ_steps : (2 : Nat) ^ 17 - (d + 1).toNat ≤ steps := by
            rw [h_succ_toNat]; omega
          have h_no_dvd_succ : ∀ k : Nat, 2 ≤ k → k < (d + 1).toNat →
              ¬ k ∣ m.toNat := by
            intro k h_k_ge h_k_lt h_k_dvd
            rw [h_succ_toNat] at h_k_lt
            by_cases h_k_eq : k = d.toNat
            · rw [h_k_eq] at h_k_dvd
              exact h_mod (Nat.mod_eq_zero_of_dvd h_k_dvd)
            · exact h_no_dvd k h_k_ge (by omega) h_k_dvd
          exact ih (d + 1) h_succ_steps h_succ_ge h_succ_le h_no_dvd_succ

/-- Bundled spec for `smallest_prime_at` at `d = 2`. -/
private theorem smallest_prime_at_2_spec
    (m : u64) (h_m_lo : 2 ≤ m.toNat) (h_m_hi : m.toNat < 2 ^ 32) :
    ∃ r : u64,
      clever_074_is_multiply_prime.smallest_prime_at m (2 : u64) = RustM.ok r
      ∧ 2 ≤ r.toNat
      ∧ r.toNat ≤ m.toNat
      ∧ r.toNat ∣ m.toNat
      ∧ ∀ k : Nat, 2 ≤ k → k < r.toNat → ¬ k ∣ m.toNat := by
  apply smallest_prime_at_spec_aux m h_m_lo h_m_hi
    ((2 : Nat) ^ 17 - (2 : u64).toNat) (2 : u64) (Nat.le_refl _)
  · rw [u64_two_toNat]; exact Nat.le_refl _
  · rw [u64_two_toNat]; decide
  · intro k h_k_ge h_k_lt h_k_dvd
    rw [u64_two_toNat] at h_k_lt; omega

/-- If `r.toNat ∣ m.toNat`, `2 ≤ r.toNat`, and no `k ∈ [2, r.toNat)` divides
    `m.toNat`, then `r.toNat` is prime. -/
private theorem is_prime_of_minimal_divisor
    (m r : Nat) (h_m_lo : 2 ≤ m) (h_r_lo : 2 ≤ r)
    (h_r_dvd : r ∣ m) (h_min : ∀ k : Nat, 2 ≤ k → k < r → ¬ k ∣ m) :
    is_prime_nat r := by
  refine ⟨h_r_lo, ?_⟩
  intro k h_k_lo h_k_lt h_k_dvd_r
  have h_k_dvd_m : k ∣ m := Nat.dvd_trans h_k_dvd_r h_r_dvd
  exact h_min k h_k_lo h_k_lt h_k_dvd_m

/-! ## `RustM.ok` is `pure`; bind rewriting helper. -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

/-! ## Failure / edge clause: `a < 8 → false` -/

theorem is_multiply_prime_below_8 (a : u64) (h : a.toNat < 8) :
    clever_074_is_multiply_prime.is_multiply_prime a = RustM.ok false := by
  unfold clever_074_is_multiply_prime.is_multiply_prime
  have h_lt : a < (8 : u64) := by
    apply UInt64.lt_iff_toNat_lt.mpr
    rw [u64_eight_toNat]; exact h
  have h_dec : decide (a < (8 : u64)) = true := decide_eq_true h_lt
  rw [show (a <? (8 : u64) : RustM Bool) = pure (decide (a < (8 : u64))) from rfl]
  simp only [pure_bind, h_dec, ↓reduceIte]
  rfl

/-! ## `is_multiply_prime` peel: when `a ≥ 8` we drop the leading `if a < 8` guard. -/

private theorem is_multiply_prime_peel_ge_8 (a : u64) (h_a_ge : 8 ≤ a.toNat) :
    clever_074_is_multiply_prime.is_multiply_prime a =
      ((clever_074_is_multiply_prime.smallest_prime_at a (2 : u64)) >>= fun p1 =>
        (a /? p1) >>= fun q1 =>
          (q1 <? (2 : u64)) >>= fun b1 =>
            if b1 then (pure false : RustM Bool)
            else
              (clever_074_is_multiply_prime.smallest_prime_at q1 (2 : u64)) >>= fun p2 =>
                (q1 /? p2) >>= fun q2 =>
                  (q2 <? (2 : u64)) >>= fun b2 =>
                    if b2 then (pure false : RustM Bool)
                    else
                      (clever_074_is_multiply_prime.smallest_prime_at q2 (2 : u64)) >>= fun p3 =>
                        (p3 ==? q2)) := by
  unfold clever_074_is_multiply_prime.is_multiply_prime
  have h_a_not_lt : ¬ a < (8 : u64) := by
    intro hlt
    have := UInt64.lt_iff_toNat_lt.mp hlt
    rw [u64_eight_toNat] at this; omega
  rw [show (a <? (8 : u64) : RustM Bool) = pure (decide (a < (8 : u64))) from rfl,
      decide_eq_false h_a_not_lt]
  simp only [pure_bind, Bool.false_eq_true, ↓reduceIte]

/-! ## Soundness -/

/-- Postcondition — soundness direction.

    Note: the obligations stage allowed adding the precondition
    `a.toNat < 2 ^ 32` if needed; we use it here to apply
    `smallest_prime_at_2_spec`, which itself requires `m < 2 ^ 32` to
    bound the trial-division iteration. -/
theorem is_multiply_prime_sound (a : u64) (h_fit : a.toNat < 2 ^ 32)
    (h : clever_074_is_multiply_prime.is_multiply_prime a = RustM.ok true) :
    is_multiply_prime_nat a.toNat := by
  -- Step 1: derive a ≥ 8
  have h_a_ge_8 : 8 ≤ a.toNat := by
    rcases Nat.lt_or_ge a.toNat 8 with h_lt | h_ge
    · exfalso
      rw [is_multiply_prime_below_8 a h_lt] at h
      exact absurd h (by decide)
    · exact h_ge
  have h_a_ge_2 : 2 ≤ a.toNat := by omega
  -- Step 2: extract p1 via spec
  obtain ⟨p1, h_sp1, h_p1_lo, h_p1_le, h_p1_dvd, h_p1_min⟩ :=
    smallest_prime_at_2_spec a h_a_ge_2 h_fit
  have h_p1_ne : p1 ≠ 0 := u64_ne_zero_of_toNat_pos p1 (by omega)
  have h_p1_prime : is_prime_nat p1.toNat :=
    is_prime_of_minimal_divisor a.toNat p1.toNat h_a_ge_2 h_p1_lo h_p1_dvd h_p1_min
  -- Step 3: peel the leading guard
  rw [is_multiply_prime_peel_ge_8 a h_a_ge_8] at h
  rw [h_sp1] at h
  simp only [RustM_ok_bind] at h
  rw [div_pure a p1 h_p1_ne] at h
  simp only [pure_bind] at h
  -- Step 4: reduce (q1 <? 2)
  rw [show ((a / p1) <? (2 : u64) : RustM Bool) = pure (decide ((a / p1) < (2 : u64))) from rfl] at h
  simp only [pure_bind] at h
  have h_q1_toNat : (a / p1).toNat = a.toNat / p1.toNat := UInt64.toNat_div a p1
  have h_q1_ge_2 : 2 ≤ (a / p1).toNat := by
    rcases Nat.lt_or_ge (a / p1).toNat 2 with h_lt | h_ge
    · exfalso
      have h_q1_lt_u : (a / p1) < (2 : u64) :=
        UInt64.lt_iff_toNat_lt.mpr (by rw [u64_two_toNat]; exact h_lt)
      rw [decide_eq_true h_q1_lt_u] at h
      simp only [↓reduceIte] at h
      exact absurd h (by decide)
    · exact h_ge
  have h_q1_not_lt_u : ¬ (a / p1) < (2 : u64) := by
    intro hlt
    have := UInt64.lt_iff_toNat_lt.mp hlt
    rw [u64_two_toNat] at this; omega
  rw [decide_eq_false h_q1_not_lt_u] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  -- Step 5: extract p2 via spec on q1
  have h_q1_lt_2_32 : (a / p1).toNat < 2 ^ 32 := by
    rw [h_q1_toNat]
    have := Nat.div_le_self a.toNat p1.toNat
    omega
  obtain ⟨p2, h_sp2, h_p2_lo, h_p2_le, h_p2_dvd, h_p2_min⟩ :=
    smallest_prime_at_2_spec (a / p1) h_q1_ge_2 h_q1_lt_2_32
  have h_p2_ne : p2 ≠ 0 := u64_ne_zero_of_toNat_pos p2 (by omega)
  have h_p2_prime : is_prime_nat p2.toNat :=
    is_prime_of_minimal_divisor (a / p1).toNat p2.toNat h_q1_ge_2 h_p2_lo h_p2_dvd h_p2_min
  rw [h_sp2] at h
  simp only [RustM_ok_bind] at h
  rw [div_pure (a / p1) p2 h_p2_ne] at h
  simp only [pure_bind] at h
  -- Step 6: reduce (q2 <? 2)
  rw [show ((a / p1 / p2) <? (2 : u64) : RustM Bool) = pure (decide ((a / p1 / p2) < (2 : u64))) from rfl] at h
  simp only [pure_bind] at h
  have h_q2_toNat : ((a / p1) / p2).toNat = (a / p1).toNat / p2.toNat :=
    UInt64.toNat_div (a / p1) p2
  have h_q2_ge_2 : 2 ≤ ((a / p1) / p2).toNat := by
    rcases Nat.lt_or_ge ((a / p1) / p2).toNat 2 with h_lt | h_ge
    · exfalso
      have h_q2_lt_u : ((a / p1) / p2) < (2 : u64) :=
        UInt64.lt_iff_toNat_lt.mpr (by rw [u64_two_toNat]; exact h_lt)
      rw [decide_eq_true h_q2_lt_u] at h
      simp only [↓reduceIte] at h
      exact absurd h (by decide)
    · exact h_ge
  have h_q2_not_lt_u : ¬ ((a / p1) / p2) < (2 : u64) := by
    intro hlt
    have := UInt64.lt_iff_toNat_lt.mp hlt
    rw [u64_two_toNat] at this; omega
  rw [decide_eq_false h_q2_not_lt_u] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  -- Step 7: extract p3
  have h_q2_lt_2_32 : ((a / p1) / p2).toNat < 2 ^ 32 := by
    rw [h_q2_toNat]
    have := Nat.div_le_self (a / p1).toNat p2.toNat
    omega
  obtain ⟨p3, h_sp3, h_p3_lo, h_p3_le, h_p3_dvd, h_p3_min⟩ :=
    smallest_prime_at_2_spec ((a / p1) / p2) h_q2_ge_2 h_q2_lt_2_32
  rw [h_sp3] at h
  simp only [RustM_ok_bind] at h
  -- Step 8: extract p3 = q2 from `(p3 ==? q2) = ok true`
  rw [show (p3 ==? ((a / p1) / p2) : RustM Bool) = pure (p3 == ((a / p1) / p2)) from rfl] at h
  have h_beq : (p3 == ((a / p1) / p2)) = true := by
    have h_inj : RustM.ok ((p3 : u64) == ((a / p1) / p2)) = RustM.ok true := h
    injection h_inj with h_inner
    injection h_inner with h_eq
  have h_p3_eq_q2 : p3 = ((a / p1) / p2) := eq_of_beq h_beq
  -- Step 9: q2 is prime
  have h_q2_prime : is_prime_nat ((a / p1) / p2).toNat := by
    apply is_prime_of_minimal_divisor ((a / p1) / p2).toNat ((a / p1) / p2).toNat h_q2_ge_2 h_q2_ge_2
      (Nat.dvd_refl _)
    intro k h_k_lo h_k_lt h_k_dvd
    have h_k_lt_p3 : k < p3.toNat := by rw [h_p3_eq_q2]; exact h_k_lt
    exact h_p3_min k h_k_lo h_k_lt_p3 h_k_dvd
  -- Step 10: construct witness a = p1 * p2 * q2
  refine ⟨p1.toNat, p2.toNat, ((a / p1) / p2).toNat, h_p1_prime, h_p2_prime, h_q2_prime, ?_⟩
  have h_a_eq : a.toNat = p1.toNat * (a / p1).toNat := by
    have h1 : a.toNat / p1.toNat * p1.toNat = a.toNat := Nat.div_mul_cancel h_p1_dvd
    rw [h_q1_toNat, Nat.mul_comm]; exact h1.symm
  have h_q1_eq : (a / p1).toNat = p2.toNat * ((a / p1) / p2).toNat := by
    have h1 : (a / p1).toNat / p2.toNat * p2.toNat = (a / p1).toNat :=
      Nat.div_mul_cancel h_p2_dvd
    rw [h_q2_toNat, Nat.mul_comm]; exact h1.symm
  rw [h_a_eq, h_q1_eq]
  rw [Nat.mul_assoc]

/-! ## Euclid-style helpers for completeness / accepts / rejects -/

/-- If `p` is prime and `¬ p ∣ a`, then `p` and `a` are coprime. -/
private theorem coprime_of_not_dvd (p a : Nat) (hp : is_prime_nat p) (h : ¬ p ∣ a) :
    Nat.Coprime p a := by
  unfold Nat.Coprime
  have hp_ge : 2 ≤ p := hp.1
  have h_gcd_dvd_p : Nat.gcd p a ∣ p := Nat.gcd_dvd_left p a
  have h_gcd_dvd_a : Nat.gcd p a ∣ a := Nat.gcd_dvd_right p a
  have h_gcd_pos : 1 ≤ Nat.gcd p a := by
    rcases Nat.eq_zero_or_pos (Nat.gcd p a) with h0 | hpos
    · rw [Nat.gcd_eq_zero_iff] at h0
      obtain ⟨h_p_eq_0, _⟩ := h0
      omega
    · exact hpos
  have h_gcd_le_p : Nat.gcd p a ≤ p := Nat.le_of_dvd (by omega) h_gcd_dvd_p
  rcases Nat.lt_or_ge (Nat.gcd p a) 2 with h_lt | h_ge
  · omega
  · rcases Nat.lt_or_ge (Nat.gcd p a) p with h_lt_p | h_ge_p
    · exfalso; exact hp.2 _ h_ge h_lt_p h_gcd_dvd_p
    · have h_gcd_eq_p : Nat.gcd p a = p := Nat.le_antisymm h_gcd_le_p h_ge_p
      exfalso; apply h; rw [← h_gcd_eq_p]; exact h_gcd_dvd_a

/-- Euclid's lemma: if a prime divides a product, it divides one of the factors. -/
private theorem euclid_lemma (p a b : Nat) (hp : is_prime_nat p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  by_cases h_dvd_a : p ∣ a
  · left; exact h_dvd_a
  · right
    have h_cop : Nat.Coprime p a := coprime_of_not_dvd p a hp h_dvd_a
    exact h_cop.dvd_of_dvd_mul_left h

/-- If `p` and `q` are both prime and `p ∣ q`, then `p = q`. -/
private theorem prime_dvd_prime_eq (p q : Nat) (hp : is_prime_nat p) (hq : is_prime_nat q)
    (h : p ∣ q) : p = q := by
  have hp_ge : 2 ≤ p := hp.1
  have hq_ge : 2 ≤ q := hq.1
  have h_p_le_q : p ≤ q := Nat.le_of_dvd (by omega) h
  rcases Nat.lt_or_ge p q with h_lt | h_ge
  · exfalso; exact hq.2 p hp_ge h_lt h
  · exact Nat.le_antisymm h_p_le_q h_ge

/-! ## `rejects_semiprime` -/

theorem is_multiply_prime_rejects_semiprime
    (p q : u64)
    (hp : is_prime_nat p.toNat) (hq : is_prime_nat q.toNat)
    (h_fit : p.toNat * q.toNat < 2 ^ 32) :
    clever_074_is_multiply_prime.is_multiply_prime (p * q) = RustM.ok false := by
  have hp_ge : 2 ≤ p.toNat := hp.1
  have hq_ge : 2 ≤ q.toNat := hq.1
  have h_pq_fits : p.toNat * q.toNat < 2 ^ 64 := by
    have : (2 : Nat) ^ 32 ≤ 2 ^ 64 := by decide
    omega
  have h_pq_toNat : (p * q).toNat = p.toNat * q.toNat := UInt64.toNat_mul_of_lt h_pq_fits
  -- Case 1: (p*q) < 8 — apply below_8
  rcases Nat.lt_or_ge (p * q).toNat 8 with h_a_lt | h_a_ge
  · exact is_multiply_prime_below_8 (p * q) h_a_lt
  -- Case 2: (p*q) ≥ 8
  have h_a_ge_2 : 2 ≤ (p * q).toNat := by omega
  have h_a_lt_2_32 : (p * q).toNat < 2 ^ 32 := by rw [h_pq_toNat]; exact h_fit
  -- Get p1 via spec
  obtain ⟨p1, h_sp1, h_p1_lo, h_p1_le, h_p1_dvd, h_p1_min⟩ :=
    smallest_prime_at_2_spec (p * q) h_a_ge_2 h_a_lt_2_32
  have h_p1_ne : p1 ≠ 0 := u64_ne_zero_of_toNat_pos p1 (by omega)
  have h_p1_prime : is_prime_nat p1.toNat :=
    is_prime_of_minimal_divisor (p * q).toNat p1.toNat h_a_ge_2 h_p1_lo h_p1_dvd h_p1_min
  -- p1 | p * q ⟹ p1 | p ∨ p1 | q (Euclid).
  rw [h_pq_toNat] at h_p1_dvd
  have h_p1_in : p1.toNat = p.toNat ∨ p1.toNat = q.toNat := by
    rcases euclid_lemma p1.toNat p.toNat q.toNat h_p1_prime h_p1_dvd with h_dvd | h_dvd
    · left; exact prime_dvd_prime_eq _ _ h_p1_prime hp h_dvd
    · right; exact prime_dvd_prime_eq _ _ h_p1_prime hq h_dvd
  have h_q1_toNat : ((p * q) / p1).toNat = (p * q).toNat / p1.toNat := UInt64.toNat_div (p * q) p1
  have h_q1_eq_other : ((p * q) / p1).toNat = p.toNat ∨ ((p * q) / p1).toNat = q.toNat := by
    rcases h_p1_in with h_p1_eq_p | h_p1_eq_q
    · right
      rw [h_q1_toNat, h_pq_toNat, h_p1_eq_p]
      rw [Nat.mul_div_cancel_left q.toNat (by omega : 0 < p.toNat)]
    · left
      rw [h_q1_toNat, h_pq_toNat, h_p1_eq_q]
      rw [Nat.mul_div_cancel _ (by omega : 0 < q.toNat)]
  have h_q1_prime : is_prime_nat ((p * q) / p1).toNat := by
    rcases h_q1_eq_other with h | h
    · rw [h]; exact hp
    · rw [h]; exact hq
  have h_q1_ge_2 : 2 ≤ ((p * q) / p1).toNat := h_q1_prime.1
  have h_q1_lt_2_32 : ((p * q) / p1).toNat < 2 ^ 32 := by
    rw [h_q1_toNat]
    have := Nat.div_le_self (p * q).toNat p1.toNat
    omega
  obtain ⟨p2, h_sp2, h_p2_lo, h_p2_le, h_p2_dvd, h_p2_min⟩ :=
    smallest_prime_at_2_spec ((p * q) / p1) h_q1_ge_2 h_q1_lt_2_32
  have h_p2_ne : p2 ≠ 0 := u64_ne_zero_of_toNat_pos p2 (by omega)
  have h_p2_prime : is_prime_nat p2.toNat :=
    is_prime_of_minimal_divisor ((p * q) / p1).toNat p2.toNat h_q1_ge_2 h_p2_lo h_p2_dvd h_p2_min
  have h_p2_eq_q1 : p2.toNat = ((p * q) / p1).toNat :=
    prime_dvd_prime_eq _ _ h_p2_prime h_q1_prime h_p2_dvd
  have h_q2_toNat : (((p * q) / p1) / p2).toNat = ((p * q) / p1).toNat / p2.toNat :=
    UInt64.toNat_div ((p * q) / p1) p2
  have h_q2_eq_1 : (((p * q) / p1) / p2).toNat = 1 := by
    rw [h_q2_toNat, h_p2_eq_q1]
    exact Nat.div_self (by omega)
  rw [is_multiply_prime_peel_ge_8 (p * q) h_a_ge]
  rw [h_sp1]
  simp only [RustM_ok_bind]
  rw [div_pure (p * q) p1 h_p1_ne]
  simp only [pure_bind]
  rw [show (((p * q) / p1) <? (2 : u64) : RustM Bool) = pure (decide (((p * q) / p1) < (2 : u64))) from rfl]
  simp only [pure_bind]
  have h_q1_not_lt_u : ¬ ((p * q) / p1) < (2 : u64) := by
    intro hlt
    have := UInt64.lt_iff_toNat_lt.mp hlt
    rw [u64_two_toNat] at this; omega
  rw [decide_eq_false h_q1_not_lt_u]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [h_sp2]
  simp only [RustM_ok_bind]
  rw [div_pure ((p * q) / p1) p2 h_p2_ne]
  simp only [pure_bind]
  rw [show ((((p * q) / p1) / p2) <? (2 : u64) : RustM Bool) = pure (decide ((((p * q) / p1) / p2) < (2 : u64))) from rfl]
  simp only [pure_bind]
  have h_q2_lt_u : (((p * q) / p1) / p2) < (2 : u64) :=
    UInt64.lt_iff_toNat_lt.mpr (by rw [u64_two_toNat, h_q2_eq_1]; decide)
  rw [decide_eq_true h_q2_lt_u]
  simp only [↓reduceIte]
  rfl

/-! ## `accepts_product_of_three_primes` -/

theorem is_multiply_prime_accepts_product_of_three_primes
    (p q r : u64)
    (hp : is_prime_nat p.toNat) (hq : is_prime_nat q.toNat)
    (hr : is_prime_nat r.toNat)
    (h_fit : p.toNat * q.toNat * r.toNat < 2 ^ 32) :
    clever_074_is_multiply_prime.is_multiply_prime (p * q * r) = RustM.ok true := by
  have hp_ge : 2 ≤ p.toNat := hp.1
  have hq_ge : 2 ≤ q.toNat := hq.1
  have hr_ge : 2 ≤ r.toNat := hr.1
  have h_pq_fits : p.toNat * q.toNat < 2 ^ 64 := by
    have h1 : p.toNat * q.toNat * 1 ≤ p.toNat * q.toNat * r.toNat :=
      Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_one] at h1
    have : (2 : Nat) ^ 32 ≤ 2 ^ 64 := by decide
    omega
  have h_pq_toNat : (p * q).toNat = p.toNat * q.toNat := UInt64.toNat_mul_of_lt h_pq_fits
  have h_pqr_fits : (p * q).toNat * r.toNat < 2 ^ 64 := by
    rw [h_pq_toNat]
    have : (2 : Nat) ^ 32 ≤ 2 ^ 64 := by decide
    omega
  have h_pqr_toNat : (p * q * r).toNat = p.toNat * q.toNat * r.toNat := by
    rw [show ((p * q) * r).toNat = (p * q).toNat * r.toNat from UInt64.toNat_mul_of_lt h_pqr_fits,
        h_pq_toNat]
  let a : u64 := p * q * r
  show clever_074_is_multiply_prime.is_multiply_prime a = RustM.ok true
  have h_a_toNat : a.toNat = p.toNat * q.toNat * r.toNat := h_pqr_toNat
  have h_a_ge_8 : 8 ≤ a.toNat := by
    rw [h_a_toNat]
    have h1 : 2 * 2 ≤ p.toNat * q.toNat := Nat.mul_le_mul hp_ge hq_ge
    have h2 : (2 * 2) * 2 ≤ (p.toNat * q.toNat) * r.toNat := Nat.mul_le_mul h1 hr_ge
    have h3 : (2 * 2) * 2 = 8 := by decide
    rw [h3] at h2; exact h2
  have h_a_ge_2 : 2 ≤ a.toNat := by omega
  have h_a_lt_2_32 : a.toNat < 2 ^ 32 := by rw [h_a_toNat]; exact h_fit
  -- p1 = smallest_prime_at(a, 2)
  obtain ⟨p1, h_sp1, h_p1_lo, h_p1_le, h_p1_dvd, h_p1_min⟩ :=
    smallest_prime_at_2_spec a h_a_ge_2 h_a_lt_2_32
  have h_p1_ne : p1 ≠ 0 := u64_ne_zero_of_toNat_pos p1 (by omega)
  have h_p1_prime : is_prime_nat p1.toNat :=
    is_prime_of_minimal_divisor a.toNat p1.toNat h_a_ge_2 h_p1_lo h_p1_dvd h_p1_min
  -- p1 | a = p*q*r ⟹ p1 ∈ {p, q, r}
  rw [h_a_toNat] at h_p1_dvd
  have h_p1_in_pqr : p1.toNat = p.toNat ∨ p1.toNat = q.toNat ∨ p1.toNat = r.toNat := by
    -- p1 | (p*q)*r ⟹ p1 | (p*q) ∨ p1 | r
    rcases euclid_lemma p1.toNat (p.toNat * q.toNat) r.toNat h_p1_prime h_p1_dvd with h_dvd | h_dvd
    · -- p1 | p*q ⟹ p1 | p ∨ p1 | q
      rcases euclid_lemma p1.toNat p.toNat q.toNat h_p1_prime h_dvd with h_p | h_q
      · left; exact prime_dvd_prime_eq _ _ h_p1_prime hp h_p
      · right; left; exact prime_dvd_prime_eq _ _ h_p1_prime hq h_q
    · right; right; exact prime_dvd_prime_eq _ _ h_p1_prime hr h_dvd
  -- q1 = a/p1. q1.toNat = (p*q*r)/p1. Three cases:
  --   p1 = p: q1.toNat = q*r
  --   p1 = q: q1.toNat = p*r
  --   p1 = r: q1.toNat = p*q
  have h_q1_toNat : (a / p1).toNat = a.toNat / p1.toNat := UInt64.toNat_div a p1
  have h_q1_eq_2primes_product :
      ((a / p1).toNat = q.toNat * r.toNat ∧ is_prime_nat q.toNat ∧ is_prime_nat r.toNat)
      ∨ ((a / p1).toNat = p.toNat * r.toNat ∧ is_prime_nat p.toNat ∧ is_prime_nat r.toNat)
      ∨ ((a / p1).toNat = p.toNat * q.toNat ∧ is_prime_nat p.toNat ∧ is_prime_nat q.toNat) := by
    rcases h_p1_in_pqr with h_eq | h_eq | h_eq
    · left
      refine ⟨?_, hq, hr⟩
      rw [h_q1_toNat, h_a_toNat, h_eq]
      rw [Nat.mul_assoc]
      rw [Nat.mul_div_cancel_left _ (by omega : 0 < p.toNat)]
    · right; left
      refine ⟨?_, hp, hr⟩
      rw [h_q1_toNat, h_a_toNat, h_eq]
      have h_comm : p.toNat * q.toNat * r.toNat = q.toNat * (p.toNat * r.toNat) := by
        rw [Nat.mul_comm p.toNat q.toNat, Nat.mul_assoc]
      rw [h_comm, Nat.mul_div_cancel_left _ (by omega : 0 < q.toNat)]
    · right; right
      refine ⟨?_, hp, hq⟩
      rw [h_q1_toNat, h_a_toNat, h_eq]
      rw [Nat.mul_div_cancel _ (by omega : 0 < r.toNat)]
  -- In each case q1 = a/b for primes a, b. q1.toNat ≥ 2*2 = 4 ≥ 2.
  have h_q1_ge_2 : 2 ≤ (a / p1).toNat := by
    rcases h_q1_eq_2primes_product with ⟨h, hx, hy⟩ | ⟨h, hx, hy⟩ | ⟨h, hx, hy⟩
    all_goals
      rw [h]
      have : 2 * 2 ≤ _ * _ := Nat.mul_le_mul hx.1 hy.1
      omega
  have h_q1_lt_2_32 : (a / p1).toNat < 2 ^ 32 := by
    rw [h_q1_toNat]
    have := Nat.div_le_self a.toNat p1.toNat
    omega
  -- p2 = smallest_prime_at(q1, 2). q1 = X * Y for primes X, Y.
  obtain ⟨p2, h_sp2, h_p2_lo, h_p2_le, h_p2_dvd, h_p2_min⟩ :=
    smallest_prime_at_2_spec (a / p1) h_q1_ge_2 h_q1_lt_2_32
  have h_p2_ne : p2 ≠ 0 := u64_ne_zero_of_toNat_pos p2 (by omega)
  have h_p2_prime : is_prime_nat p2.toNat :=
    is_prime_of_minimal_divisor (a / p1).toNat p2.toNat h_q1_ge_2 h_p2_lo h_p2_dvd h_p2_min
  -- p2 | q1 = X * Y ⟹ p2 = X or p2 = Y. Then q2 = the other one.
  -- q2 = q1/p2. q2 is the remaining prime. q2 ≥ 2.
  -- p3 = smallest_prime_at(q2, 2) = q2 (since q2 is prime).
  -- Then p3 = q2 ⟹ ok true.
  have h_q2_toNat : ((a / p1) / p2).toNat = (a / p1).toNat / p2.toNat :=
    UInt64.toNat_div (a / p1) p2
  have h_q2_prime : is_prime_nat ((a / p1) / p2).toNat := by
    rcases h_q1_eq_2primes_product with ⟨h_q1_eq, h_X, h_Y⟩ | ⟨h_q1_eq, h_X, h_Y⟩ | ⟨h_q1_eq, h_X, h_Y⟩
    all_goals (
      rw [h_q1_eq] at h_p2_dvd
      rcases euclid_lemma p2.toNat _ _ h_p2_prime h_p2_dvd with h_dvd_X | h_dvd_Y
      · -- p2 = X. q2 = q1/p2 = Y.
        have h_p2_eq_X : p2.toNat = _ := prime_dvd_prime_eq _ _ h_p2_prime h_X h_dvd_X
        rw [h_q2_toNat, h_q1_eq, h_p2_eq_X]
        rw [Nat.mul_div_cancel_left _ (by have := h_X.1; omega)]
        exact h_Y
      · -- p2 = Y. q2 = q1/p2 = X.
        have h_p2_eq_Y : p2.toNat = _ := prime_dvd_prime_eq _ _ h_p2_prime h_Y h_dvd_Y
        rw [h_q2_toNat, h_q1_eq, h_p2_eq_Y]
        rw [Nat.mul_div_cancel _ (by have := h_Y.1; omega)]
        exact h_X)
  have h_q2_ge_2 : 2 ≤ ((a / p1) / p2).toNat := h_q2_prime.1
  have h_q2_lt_2_32 : ((a / p1) / p2).toNat < 2 ^ 32 := by
    rw [h_q2_toNat]
    have := Nat.div_le_self (a / p1).toNat p2.toNat
    omega
  -- p3 = smallest_prime_at(q2, 2). q2 prime ⟹ p3 = q2.
  obtain ⟨p3, h_sp3, h_p3_lo, h_p3_le, h_p3_dvd, h_p3_min⟩ :=
    smallest_prime_at_2_spec ((a / p1) / p2) h_q2_ge_2 h_q2_lt_2_32
  have h_p3_prime : is_prime_nat p3.toNat :=
    is_prime_of_minimal_divisor ((a / p1) / p2).toNat p3.toNat h_q2_ge_2 h_p3_lo h_p3_dvd h_p3_min
  have h_p3_eq_q2_toNat : p3.toNat = ((a / p1) / p2).toNat :=
    prime_dvd_prime_eq _ _ h_p3_prime h_q2_prime h_p3_dvd
  have h_p3_eq_q2 : p3 = ((a / p1) / p2) := UInt64.toNat_inj.mp h_p3_eq_q2_toNat
  -- Now drive the function
  rw [is_multiply_prime_peel_ge_8 a h_a_ge_8]
  rw [h_sp1]
  simp only [RustM_ok_bind]
  rw [div_pure a p1 h_p1_ne]
  simp only [pure_bind]
  rw [show ((a / p1) <? (2 : u64) : RustM Bool) = pure (decide ((a / p1) < (2 : u64))) from rfl]
  simp only [pure_bind]
  have h_q1_not_lt_u : ¬ (a / p1) < (2 : u64) := by
    intro hlt
    have := UInt64.lt_iff_toNat_lt.mp hlt
    rw [u64_two_toNat] at this; omega
  rw [decide_eq_false h_q1_not_lt_u]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [h_sp2]
  simp only [RustM_ok_bind]
  rw [div_pure (a / p1) p2 h_p2_ne]
  simp only [pure_bind]
  rw [show ((a / p1 / p2) <? (2 : u64) : RustM Bool) = pure (decide ((a / p1 / p2) < (2 : u64))) from rfl]
  simp only [pure_bind]
  have h_q2_not_lt_u : ¬ ((a / p1) / p2) < (2 : u64) := by
    intro hlt
    have := UInt64.lt_iff_toNat_lt.mp hlt
    rw [u64_two_toNat] at this; omega
  rw [decide_eq_false h_q2_not_lt_u]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [h_sp3]
  simp only [RustM_ok_bind]
  rw [show (p3 ==? ((a / p1) / p2) : RustM Bool) = pure (p3 == ((a / p1) / p2)) from rfl]
  have h_beq_self : ((p3 : u64) == ((a / p1) / p2)) = true := by
    rw [h_p3_eq_q2]
    exact beq_self_eq_true _
  rw [h_beq_self]
  rfl

/-! ## Completeness -/

/-- Postcondition — completeness direction. -/
theorem is_multiply_prime_complete (a : u64) (h_fit : a.toNat < 2 ^ 32)
    (h_spec : is_multiply_prime_nat a.toNat) :
    clever_074_is_multiply_prime.is_multiply_prime a = RustM.ok true := by
  obtain ⟨p, q, r, hp, hq, hr, h_eq⟩ := h_spec
  -- p, q, r : Nat with p*q*r = a.toNat
  -- Lift them to u64. Each is ≤ a.toNat < 2^32 < 2^64.
  have hp_ge : 2 ≤ p := hp.1
  have hq_ge : 2 ≤ q := hq.1
  have hr_ge : 2 ≤ r := hr.1
  have hp_le : p ≤ a.toNat := by
    have h1 : p ≤ p * (q * r) := by
      have h_qr_pos : 0 < q * r := Nat.mul_pos (by omega) (by omega)
      have : p * 1 ≤ p * (q * r) := Nat.mul_le_mul_left _ h_qr_pos
      rw [Nat.mul_one] at this; exact this
    have h_assoc : p * (q * r) = p * q * r := (Nat.mul_assoc _ _ _).symm
    rw [h_assoc] at h1
    omega
  have hq_le : q ≤ a.toNat := by
    have h1 : q ≤ p * q := by
      have : 1 * q ≤ p * q := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.one_mul] at this; exact this
    have h2 : p * q ≤ p * q * r := by
      have : p * q * 1 ≤ p * q * r := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_one] at this; exact this
    omega
  have hr_le : r ≤ a.toNat := by
    have h1 : r ≤ p * q * r := by
      have h_pq_pos : 0 < p * q := Nat.mul_pos (by omega) (by omega)
      have : 1 * r ≤ p * q * r := Nat.mul_le_mul_right _ h_pq_pos
      rw [Nat.one_mul] at this; exact this
    omega
  have hp_lt_64 : p < 2 ^ 64 := by
    have : (2 : Nat) ^ 32 ≤ 2 ^ 64 := by decide
    omega
  have hq_lt_64 : q < 2 ^ 64 := by
    have : (2 : Nat) ^ 32 ≤ 2 ^ 64 := by decide
    omega
  have hr_lt_64 : r < 2 ^ 64 := by
    have : (2 : Nat) ^ 32 ≤ 2 ^ 64 := by decide
    omega
  -- Construct u64 values
  let p' : u64 := UInt64.ofNat p
  let q' : u64 := UInt64.ofNat q
  let r' : u64 := UInt64.ofNat r
  have hp'_toNat : p'.toNat = p := UInt64.toNat_ofNat_of_lt' hp_lt_64
  have hq'_toNat : q'.toNat = q := UInt64.toNat_ofNat_of_lt' hq_lt_64
  have hr'_toNat : r'.toNat = r := UInt64.toNat_ofNat_of_lt' hr_lt_64
  have hp'_prime : is_prime_nat p'.toNat := by rw [hp'_toNat]; exact hp
  have hq'_prime : is_prime_nat q'.toNat := by rw [hq'_toNat]; exact hq
  have hr'_prime : is_prime_nat r'.toNat := by rw [hr'_toNat]; exact hr
  have h_fit' : p'.toNat * q'.toNat * r'.toNat < 2 ^ 32 := by
    rw [hp'_toNat, hq'_toNat, hr'_toNat, h_eq]; exact h_fit
  -- accepts gives us: is_multiply_prime (p'*q'*r') = ok true.
  have h_accepts :=
    is_multiply_prime_accepts_product_of_three_primes p' q' r' hp'_prime hq'_prime hr'_prime h_fit'
  -- Show p'*q'*r' = a (in u64).
  have h_pq_fits : p'.toNat * q'.toNat < 2 ^ 64 := by
    rw [hp'_toNat, hq'_toNat]
    have h1 : p * q ≤ a.toNat := by
      have h2 : p * q ≤ p * q * r := by
        have : p * q * 1 ≤ p * q * r := Nat.mul_le_mul_left _ (by omega)
        rw [Nat.mul_one] at this; exact this
      omega
    have : a.toNat < 2 ^ 64 := a.toNat_lt
    omega
  have h_pqr_fits : (p' * q').toNat * r'.toNat < 2 ^ 64 := by
    rw [show (p' * q').toNat = p'.toNat * q'.toNat from UInt64.toNat_mul_of_lt h_pq_fits,
        hp'_toNat, hq'_toNat, hr'_toNat, h_eq]
    exact a.toNat_lt
  have h_prod_toNat : (p' * q' * r').toNat = a.toNat := by
    rw [show ((p' * q') * r').toNat = (p' * q').toNat * r'.toNat from
          UInt64.toNat_mul_of_lt h_pqr_fits,
        show (p' * q').toNat = p'.toNat * q'.toNat from UInt64.toNat_mul_of_lt h_pq_fits,
        hp'_toNat, hq'_toNat, hr'_toNat, h_eq]
  have h_prod_eq_a : p' * q' * r' = a := UInt64.toNat_inj.mp h_prod_toNat
  rw [← h_prod_eq_a]
  exact h_accepts

end Clever_074_is_multiply_primeObligations
