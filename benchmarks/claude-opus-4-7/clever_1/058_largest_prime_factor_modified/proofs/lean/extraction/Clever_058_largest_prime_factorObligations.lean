-- Companion obligations file for the `clever_058_largest_prime_factor` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_058_largest_prime_factor

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_058_largest_prime_factorObligations

/-! ## Spec-side primality oracle

Mathematical primality on `Nat`. Mirrors `is_prime_nat` in
`clever_038_prime_fib_modified` and `is_prime_int` in
`clever_024_factorize_modified`: the standard "≥ 2 ∧ no proper
divisor" definition. -/

/-- Mathematical primality on `Nat`. -/
private def is_prime_nat (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ k : Nat, 2 ≤ k → k < p → ¬ k ∣ p

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

/-! ## One-step unfold of `smallest_divisor_at` -/

private theorem smallest_divisor_at_unfold (m d : u64)
    (h_d_ne : d ≠ 0)
    (h_mul_fits : d.toNat * d.toNat < 2 ^ 64) :
    clever_058_largest_prime_factor.smallest_divisor_at m d =
      (if d.toNat * d.toNat > m.toNat then
        (RustM.ok m : RustM u64)
       else if m.toNat % d.toNat = 0 then
        (RustM.ok d : RustM u64)
       else
        clever_058_largest_prime_factor.smallest_divisor_at m (d + 1)) := by
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
  conv => lhs; unfold clever_058_largest_prime_factor.smallest_divisor_at
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

/-! ## Main spec for `smallest_divisor_at`

`smallest_divisor_at m d` returns the smallest `k ≥ d` with `k ∣ m` if any
exists in `[d, ⌊√m⌋]`; else returns `m`. We bundle the postcondition with
the invariant that no `k ∈ [2, d)` divides `m` (carried through the
recursion).

By strong induction on the measure `2^17 - d.toNat`. The bound `d ≤ 2^17`
is preserved: once `d * d > m`, the recursion exits; while we recurse,
`d * d ≤ m < 2^32` so `d < 2^16 < 2^17`. -/

private theorem smallest_divisor_at_spec_aux
    (m : u64) (h_m_lo : 2 ≤ m.toNat) (h_m_hi : m.toNat < 2 ^ 32) :
    ∀ (steps : Nat) (d : u64),
      (2 : Nat) ^ 17 - d.toNat ≤ steps →
      2 ≤ d.toNat →
      d.toNat ≤ (2 : Nat) ^ 17 →
      (∀ k : Nat, 2 ≤ k → k < d.toNat → ¬ k ∣ m.toNat) →
      ∃ r : u64,
        clever_058_largest_prime_factor.smallest_divisor_at m d = RustM.ok r
        ∧ 2 ≤ r.toNat
        ∧ r.toNat ≤ m.toNat
        ∧ r.toNat ∣ m.toNat
        ∧ ∀ k : Nat, 2 ≤ k → k < r.toNat → ¬ k ∣ m.toNat := by
  intro steps
  induction steps with
  | zero =>
    intro d h_m h_d_ge h_d_le h_no_dvd
    -- d.toNat = 2^17, so d*d = 2^34 > 2^32 > m.toNat. Returns m.
    have h_d_eq : d.toNat = (2 : Nat) ^ 17 := by omega
    have h_dd_eq : d.toNat * d.toNat = (2 : Nat) ^ 17 * 2 ^ 17 := by rw [h_d_eq]
    have h_gt : d.toNat * d.toNat > m.toNat := by
      rw [h_dd_eq]
      have h1 : m.toNat < 2 ^ 32 := h_m_hi
      have h2 : (2 : Nat) ^ 32 < 2 ^ 17 * 2 ^ 17 := two17_sq_gt_2_32
      omega
    have h_dd_fits : d.toNat * d.toNat < 2 ^ 64 := by
      rw [h_dd_eq]; exact two17_sq_lt_2_64
    have h_d_ne : d ≠ 0 := u64_ne_zero_of_toNat_pos d (by omega)
    refine ⟨m, ?_, h_m_lo, Nat.le_refl _, Nat.dvd_refl _, ?_⟩
    · rw [smallest_divisor_at_unfold m d h_d_ne h_dd_fits, if_pos h_gt]
    · -- For k < m: any divisor of m. But k ≥ d = 2^17 > sqrt(m). So if k ∣ m,
      -- then m / k ≤ m/2^17 < m / m^(1/2) = sqrt(m) < 2^16 < d. From h_no_dvd
      -- applied to m/k: ¬ m/k ∣ m. But m = (m/k) * k, so m/k ∣ m. Contradiction.
      -- Wait, k might be > sqrt(m) but still ∣ m (e.g. k = m). Let's restrict
      -- to k < m.toNat.
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
      -- Consider d_min = min(k, q). d_min ≥ 2, d_min² ≤ m.toNat, d_min ∣ m.
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
      -- Need d_min < d.toNat = 2^17, then contradict via h_no_dvd.
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
    · -- d.toNat = 2^17: identical to base case
      have h_dd_eq : d.toNat * d.toNat = (2 : Nat) ^ 17 * 2 ^ 17 := by rw [h_at_top]
      have h_gt : d.toNat * d.toNat > m.toNat := by
        rw [h_dd_eq]
        have h2 : (2 : Nat) ^ 32 < 2 ^ 17 * 2 ^ 17 := two17_sq_gt_2_32
        omega
      have h_dd_fits : d.toNat * d.toNat < 2 ^ 64 := by
        rw [h_dd_eq]; exact two17_sq_lt_2_64
      have h_d_ne : d ≠ 0 := u64_ne_zero_of_toNat_pos d (by omega)
      refine ⟨m, ?_, h_m_lo, Nat.le_refl _, Nat.dvd_refl _, ?_⟩
      · rw [smallest_divisor_at_unfold m d h_d_ne h_dd_fits, if_pos h_gt]
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
    · -- d.toNat < 2^17, so d*d ≤ (2^17-1)² < 2^34 < 2^64
      have h_d_lt_top : d.toNat < (2 : Nat) ^ 17 := by omega
      have h_dd_lt : d.toNat * d.toNat < (2 : Nat) ^ 17 * 2 ^ 17 := by
        exact Nat.mul_lt_mul_of_lt_of_lt h_d_lt_top h_d_lt_top
      have h_dd_fits : d.toNat * d.toNat < 2 ^ 64 :=
        Nat.lt_trans h_dd_lt two17_sq_lt_2_64
      have h_d_ne : d ≠ 0 := u64_ne_zero_of_toNat_pos d (by omega)
      rw [smallest_divisor_at_unfold m d h_d_ne h_dd_fits]
      by_cases h_gt : d.toNat * d.toNat > m.toNat
      · -- d² > m: return m
        rw [if_pos h_gt]
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
        -- d_min² ≤ m < d² so d_min < d
        have h_dmin_lt_d : d_min < d.toNat := by
          rcases Nat.lt_or_ge d_min d.toNat with h_lt | h_ge
          · exact h_lt
          · exfalso
            have h_sq_ge : d.toNat * d.toNat ≤ d_min * d_min :=
              Nat.mul_le_mul h_ge h_ge
            omega
        exact (h_no_dvd d_min h_d_min_ge_2 h_dmin_lt_d h_dmin_dvd_m).elim
      · -- d² ≤ m: check m % d
        rw [if_neg h_gt]
        have h_dd_le_m : d.toNat * d.toNat ≤ m.toNat := Nat.le_of_not_lt h_gt
        by_cases h_mod : m.toNat % d.toNat = 0
        · -- d divides m: return d
          rw [if_pos h_mod]
          have h_d_le_m : d.toNat ≤ m.toNat := by
            have h1 : d.toNat ≤ d.toNat * d.toNat := Nat.le_mul_of_pos_left _ (by omega)
            omega
          refine ⟨d, rfl, h_d_ge, h_d_le_m, Nat.dvd_of_mod_eq_zero h_mod, ?_⟩
          intro k h_k_ge h_k_lt h_dvd
          exact h_no_dvd k h_k_ge h_k_lt h_dvd
        · -- d doesn't divide m: recurse on d+1
          rw [if_neg h_mod]
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

/-- Bundled spec for `smallest_divisor_at` at `d = 2`. -/
private theorem smallest_divisor_at_2_spec
    (m : u64) (h_m_lo : 2 ≤ m.toNat) (h_m_hi : m.toNat < 2 ^ 32) :
    ∃ r : u64,
      clever_058_largest_prime_factor.smallest_divisor_at m (2 : u64) = RustM.ok r
      ∧ 2 ≤ r.toNat
      ∧ r.toNat ≤ m.toNat
      ∧ r.toNat ∣ m.toNat
      ∧ ∀ k : Nat, 2 ≤ k → k < r.toNat → ¬ k ∣ m.toNat := by
  apply smallest_divisor_at_spec_aux m h_m_lo h_m_hi
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
  -- k ∣ r, r ∣ m ⇒ k ∣ m. But k < r and k ≥ 2 ⇒ ¬ k ∣ m. Contradiction.
  have h_k_dvd_m : k ∣ m := Nat.dvd_trans h_k_dvd_r h_r_dvd
  exact h_min k h_k_lo h_k_lt h_k_dvd_m

/-! ## One-step unfold of `strip_factor` -/

private theorem strip_factor_unfold (n p : u64) (h_p_ne : p ≠ 0) :
    clever_058_largest_prime_factor.strip_factor n p =
      (if n.toNat % p.toNat = 0 then
        clever_058_largest_prime_factor.strip_factor (n / p) p
       else
        (RustM.ok n : RustM u64)) := by
  have h_mod_eq : (n %? p : RustM u64) = pure (n % p) := mod_pure n p h_p_ne
  have h_div_eq : (n /? p : RustM u64) = pure (n / p) := div_pure n p h_p_ne
  have h_mod_toNat : (n % p).toNat = n.toNat % p.toNat := UInt64.toNat_mod n p
  have h_eq_def : ((n % p) ==? (0 : u64) : RustM Bool) =
      pure (decide ((n % p) = (0 : u64))) := rfl
  have h_eq_iff : ((n % p) = (0 : u64)) ↔ (n.toNat % p.toNat = 0) := by
    constructor
    · intro h
      have := congrArg UInt64.toNat h
      rw [h_mod_toNat, u64_zero_toNat] at this
      exact this
    · intro h
      apply UInt64.toNat_inj.mp
      rw [h_mod_toNat, u64_zero_toNat]
      exact h
  conv => lhs; unfold clever_058_largest_prime_factor.strip_factor
  rw [h_mod_eq]
  simp only [pure_bind]
  rw [h_eq_def]
  simp only [pure_bind]
  by_cases h_mod : n.toNat % p.toNat = 0
  · have h_mod_u : (n % p) = (0 : u64) := h_eq_iff.mpr h_mod
    rw [if_pos (decide_eq_true h_mod_u), if_pos h_mod]
    rw [h_div_eq]
    simp only [pure_bind]
  · have h_not_mod_u : ¬ (n % p) = (0 : u64) := fun h => h_mod (h_eq_iff.mp h)
    have h_dec_mod : (decide ((n % p) = (0 : u64))) = false := decide_eq_false h_not_mod_u
    rw [h_dec_mod, if_neg h_mod]
    simp only [Bool.false_eq_true, if_false]
    rfl

/-! ## Main spec for `strip_factor`

For `n ≥ 1` and `p ≥ 2`: terminates with a value `r` such that
`1 ≤ r ≤ n`, `r ∣ n`, and `p ∤ r`. The result is `n / p^v_p(n)`. -/

private theorem strip_factor_spec_aux (p : u64) (h_p_lo : 2 ≤ p.toNat) :
    ∀ (steps : Nat) (n : u64),
      n.toNat ≤ steps → 1 ≤ n.toNat →
      ∃ r : u64,
        clever_058_largest_prime_factor.strip_factor n p = RustM.ok r
        ∧ 1 ≤ r.toNat
        ∧ r.toNat ≤ n.toNat
        ∧ r.toNat ∣ n.toNat
        ∧ ¬ p.toNat ∣ r.toNat
        ∧ (∀ q : Nat, Nat.Coprime q p.toNat → q ∣ n.toNat → q ∣ r.toNat) := by
  intro steps
  induction steps with
  | zero =>
    intro n h_meas h_n_ge_1
    omega
  | succ steps ih =>
    intro n h_meas h_n_ge_1
    have h_p_ne : p ≠ 0 := u64_ne_zero_of_toNat_pos p (by omega)
    rw [strip_factor_unfold n p h_p_ne]
    by_cases h_mod : n.toNat % p.toNat = 0
    · -- p ∣ n: recurse on n/p
      rw [if_pos h_mod]
      have h_p_dvd : p.toNat ∣ n.toNat := Nat.dvd_of_mod_eq_zero h_mod
      obtain ⟨k, hk⟩ := h_p_dvd
      have h_div_toNat : (n / p).toNat = n.toNat / p.toNat := UInt64.toNat_div n p
      have h_div_eq_k : (n / p).toNat = k := by
        rw [h_div_toNat, hk, Nat.mul_div_cancel_left _ (by omega : 0 < p.toNat)]
      have h_k_pos : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with hz | hp
        · subst hz; rw [Nat.mul_zero] at hk; omega
        · exact hp
      have h_np_ge : 1 ≤ (n / p).toNat := by rw [h_div_eq_k]; exact h_k_pos
      have h_np_lt_n : (n / p).toNat < n.toNat := by
        rw [h_div_eq_k, hk]
        have h1 : 1 * k < p.toNat * k :=
          Nat.mul_lt_mul_of_pos_right (by omega : 1 < p.toNat) h_k_pos
        omega
      have h_np_meas : (n / p).toNat ≤ steps := by omega
      obtain ⟨r, h_eq, h_r_lo, h_r_le, h_r_dvd, h_p_not_dvd, h_coprime⟩ :=
        ih (n / p) h_np_meas h_np_ge
      refine ⟨r, h_eq, h_r_lo, ?_, ?_, h_p_not_dvd, ?_⟩
      · exact Nat.le_trans h_r_le (Nat.le_of_lt h_np_lt_n)
      · have h_npn : (n / p).toNat ∣ n.toNat :=
          ⟨p.toNat, by rw [h_div_eq_k, hk, Nat.mul_comm]⟩
        exact Nat.dvd_trans h_r_dvd h_npn
      · -- Coprime preservation: q coprime p, q ∣ n ⇒ q ∣ r
        intro q h_cop h_q_dvd
        -- n = (n/p) * p. q coprime p, q ∣ (n/p)*p ⇒ q ∣ n/p ⇒ q ∣ r (by IH).
        have h_n_eq : n.toNat = (n / p).toNat * p.toNat := by
          rw [h_div_eq_k, hk, Nat.mul_comm]
        have h_q_dvd' : q ∣ (n / p).toNat * p.toNat := by rw [← h_n_eq]; exact h_q_dvd
        have h_q_dvd_np : q ∣ (n / p).toNat :=
          Nat.Coprime.dvd_of_dvd_mul_right h_cop h_q_dvd'
        exact h_coprime q h_cop h_q_dvd_np
    · rw [if_neg h_mod]
      refine ⟨n, rfl, h_n_ge_1, Nat.le_refl _, Nat.dvd_refl _, ?_, ?_⟩
      · intro h_dvd
        exact h_mod (Nat.mod_eq_zero_of_dvd h_dvd)
      · intro q h_cop h_q_dvd; exact h_q_dvd

private theorem strip_factor_spec (p : u64) (h_p_lo : 2 ≤ p.toNat) (n : u64)
    (h_n_ge_1 : 1 ≤ n.toNat) :
    ∃ r : u64,
      clever_058_largest_prime_factor.strip_factor n p = RustM.ok r
      ∧ 1 ≤ r.toNat
      ∧ r.toNat ≤ n.toNat
      ∧ r.toNat ∣ n.toNat
      ∧ ¬ p.toNat ∣ r.toNat
      ∧ (∀ q : Nat, Nat.Coprime q p.toNat → q ∣ n.toNat → q ∣ r.toNat) :=
  strip_factor_spec_aux p h_p_lo n.toNat n (Nat.le_refl _) h_n_ge_1

/-- If `p` and `q` are distinct primes (witnessed by `is_prime_nat`), they are
    coprime. -/
private theorem coprime_of_distinct_primes
    (p q : Nat) (hp : is_prime_nat p) (hq : is_prime_nat q) (h_ne : q ≠ p) :
    Nat.Coprime q p := by
  -- gcd(q, p) ∣ q ⇒ gcd ∈ {1, q}. If gcd = q, q ∣ p ⇒ q = 1 ∨ q = p (since p prime).
  -- q ≥ 2 ⇒ q ≠ 1; and q ≠ p. Contradiction. So gcd = 1.
  obtain ⟨hp_ge, hp_no_dvd⟩ := hp
  obtain ⟨hq_ge, hq_no_dvd⟩ := hq
  unfold Nat.Coprime
  -- gcd q p divides both q and p
  have h_gcd_dvd_q : Nat.gcd q p ∣ q := Nat.gcd_dvd_left q p
  have h_gcd_dvd_p : Nat.gcd q p ∣ p := Nat.gcd_dvd_right q p
  -- gcd is positive (since q ≥ 2)
  have h_gcd_pos : 1 ≤ Nat.gcd q p := by
    rcases Nat.eq_zero_or_pos (Nat.gcd q p) with h0 | hp
    · rw [Nat.gcd_eq_zero_iff] at h0
      omega
    · exact hp
  -- gcd ≤ q (since gcd ∣ q and q > 0)
  have h_gcd_le_q : Nat.gcd q p ≤ q :=
    Nat.le_of_dvd (by omega) h_gcd_dvd_q
  -- gcd ≤ p (since gcd ∣ p and p > 0)
  have h_gcd_le_p : Nat.gcd q p ≤ p :=
    Nat.le_of_dvd (by omega) h_gcd_dvd_p
  -- Case analysis on gcd vs 2
  rcases Nat.lt_or_ge (Nat.gcd q p) 2 with h_lt_2 | h_ge_2
  · -- gcd ∈ {0, 1}, but gcd ≥ 1, so gcd = 1
    omega
  · -- gcd ≥ 2: from is_prime_nat p, gcd dividing p and gcd ∈ [2, p) would contradict.
    -- So gcd = p. But gcd ≤ q and gcd = p: p ≤ q.
    rcases Nat.lt_or_ge (Nat.gcd q p) p with h_lt_p | h_ge_p
    · -- gcd ∈ [2, p): hp_no_dvd says gcd ∤ p. Contradiction.
      exfalso
      exact hp_no_dvd _ h_ge_2 h_lt_p h_gcd_dvd_p
    · -- gcd ≥ p, and gcd ≤ p ⇒ gcd = p.
      have h_gcd_eq_p : Nat.gcd q p = p := Nat.le_antisymm h_gcd_le_p h_ge_p
      -- Now gcd = p ∣ q. From hq_no_dvd: if p ∈ [2, q), ¬ p ∣ q. So p ≥ q.
      have h_p_dvd_q : p ∣ q := h_gcd_eq_p ▸ h_gcd_dvd_q
      have h_p_lt_q_or : p < q ∨ p ≥ q := Nat.lt_or_ge p q
      rcases h_p_lt_q_or with h_p_lt_q | h_p_ge_q
      · exfalso
        exact hq_no_dvd p hp_ge h_p_lt_q h_p_dvd_q
      · -- p ≥ q and p ∣ q (with q > 0): p ≤ q, so p = q. Then q ≠ p contradicts.
        have h_p_le_q : p ≤ q := Nat.le_of_dvd (by omega) h_p_dvd_q
        have h_p_eq_q : p = q := Nat.le_antisymm h_p_le_q h_p_ge_q
        exact absurd h_p_eq_q.symm h_ne

/-! ## Base lemma: `largest_prime_at` for `n ≤ 1` -/

private theorem largest_prime_at_n_le_one (n c : u64) (h : n.toNat ≤ 1) :
    clever_058_largest_prime_factor.largest_prime_at n c = RustM.ok c := by
  unfold clever_058_largest_prime_factor.largest_prime_at
  have h_le : n ≤ (1 : u64) := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [u64_one_toNat]; exact h
  have h_dec : decide (n ≤ (1 : u64)) = true := decide_eq_true h_le
  simp only [show (n <=? (1 : u64)) =
               (pure (decide (n ≤ (1 : u64))) : RustM Bool) from rfl,
             h_dec, pure_bind, ↓reduceIte]
  rfl

/-- `RustM.ok x >>= f = f x` (the explicit `RustM.ok` form). -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

/-! ## Step lemma: one-step unfold of `largest_prime_at` for `n ≥ 2`.

When `n.toNat ≥ 2` and the inner computations succeed with the given values,
`largest_prime_at n c` equals the recursive call. -/

private theorem largest_prime_at_step (n c p stripped : u64)
    (h_n_lo : 2 ≤ n.toNat)
    (h_sd : clever_058_largest_prime_factor.smallest_divisor_at n (2 : u64) = RustM.ok p)
    (h_sf : clever_058_largest_prime_factor.strip_factor n p = RustM.ok stripped) :
    clever_058_largest_prime_factor.largest_prime_at n c =
      clever_058_largest_prime_factor.largest_prime_at stripped p := by
  conv => lhs; unfold clever_058_largest_prime_factor.largest_prime_at
  have h_not_le : ¬ n ≤ (1 : u64) := by
    intro hle
    have := UInt64.le_iff_toNat_le.mp hle
    rw [u64_one_toNat] at this; omega
  have h_dec : decide (n ≤ (1 : u64)) = false := decide_eq_false h_not_le
  simp only [show (n <=? (1 : u64)) =
               (pure (decide (n ≤ (1 : u64))) : RustM Bool) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
  rw [h_sd]
  simp only [RustM_ok_bind]
  rw [h_sf]
  simp only [RustM_ok_bind]

/-! ## Main spec for `largest_prime_at` (the n ≥ 2 case).

By strong induction on the measure `n.toNat`. -/

private theorem largest_prime_at_spec_aux :
    ∀ (steps : Nat) (n c : u64),
      n.toNat ≤ steps → 2 ≤ n.toNat → n.toNat < 2 ^ 32 →
      ∃ r : u64,
        clever_058_largest_prime_factor.largest_prime_at n c = RustM.ok r
        ∧ r.toNat ∣ n.toNat
        ∧ is_prime_nat r.toNat
        ∧ ∀ q : Nat, r.toNat < q → is_prime_nat q → ¬ q ∣ n.toNat := by
  intro steps
  induction steps with
  | zero =>
    intro n c h_meas h_n_lo h_n_hi
    omega
  | succ steps ih =>
    intro n c h_meas h_n_lo h_n_hi
    -- Get the smallest divisor p of n
    obtain ⟨p, h_p_eq, h_p_lo, h_p_le, h_p_dvd, h_p_min⟩ :=
      smallest_divisor_at_2_spec n h_n_lo h_n_hi
    -- p is prime
    have h_p_prime : is_prime_nat p.toNat :=
      is_prime_of_minimal_divisor n.toNat p.toNat h_n_lo h_p_lo h_p_dvd h_p_min
    -- Get stripped = strip_factor(n, p)
    have h_n_ge_1 : 1 ≤ n.toNat := by omega
    obtain ⟨stripped, h_s_eq, h_s_lo, h_s_le, h_s_dvd, h_p_not_dvd_s, h_s_coprime⟩ :=
      strip_factor_spec p h_p_lo n h_n_ge_1
    -- Apply the step unfold
    rw [largest_prime_at_step n c p stripped h_n_lo h_p_eq h_s_eq]
    -- stripped < n (since p ∣ n, p ≥ 2)
    have h_s_lt_n : stripped.toNat < n.toNat := by
      -- stripped ≤ n and p ∤ stripped, but p ∣ n: so stripped < n unless equal.
      -- Use stripped ≤ n/p ≤ n/2 < n. Direct: stripped ∣ n, p ∣ n, p ∤ stripped.
      -- stripped < n because stripped * p ∣ n in some sense...
      -- Cleaner: stripped ∣ n, stripped < n iff stripped ≠ n. Equal would give p ∣ stripped.
      rcases Nat.lt_or_eq_of_le h_s_le with h_lt | h_eq
      · exact h_lt
      · exfalso
        -- stripped = n, but p ∣ n and p ∤ stripped — contradiction.
        rw [h_eq] at h_p_not_dvd_s
        exact h_p_not_dvd_s h_p_dvd
    have h_s_meas : stripped.toNat ≤ steps := by omega
    have h_s_hi : stripped.toNat < 2 ^ 32 := Nat.lt_of_le_of_lt h_s_le h_n_hi
    -- Case split on stripped ≤ 1 or stripped ≥ 2
    by_cases h_s_le_1 : stripped.toNat ≤ 1
    · -- stripped ≤ 1: returns p. Since stripped ≥ 1, stripped = 1.
      have h_s_eq_1 : stripped.toNat = 1 := by omega
      have h_call : clever_058_largest_prime_factor.largest_prime_at stripped p
          = RustM.ok p := largest_prime_at_n_le_one stripped p h_s_le_1
      refine ⟨p, h_call, h_p_dvd, h_p_prime, ?_⟩
      -- Maximality: ∀ q > p prime, ¬ q ∣ n.
      intro q h_q_gt h_q_prime h_q_dvd
      -- q is prime, q > p ≥ 2, so q ≠ p, both prime ⇒ coprime.
      have h_q_ne_p : q ≠ p.toNat := by omega
      have h_cop : Nat.Coprime q p.toNat :=
        coprime_of_distinct_primes p.toNat q h_p_prime h_q_prime h_q_ne_p
      have h_q_dvd_s : q ∣ stripped.toNat := h_s_coprime q h_cop h_q_dvd
      -- stripped = 1, so q ∣ 1, so q ≤ 1. But q ≥ 2 (prime). Contradiction.
      rw [h_s_eq_1] at h_q_dvd_s
      have h_q_le_1 : q ≤ 1 := Nat.le_of_dvd (by omega) h_q_dvd_s
      have h_q_ge_2 : 2 ≤ q := h_q_prime.1
      omega
    · -- stripped ≥ 2: apply IH on (stripped, p)
      have h_s_lo_2 : 2 ≤ stripped.toNat := by omega
      obtain ⟨r, h_r_eq, h_r_dvd_s, h_r_prime, h_r_max⟩ :=
        ih stripped p h_s_meas h_s_lo_2 h_s_hi
      refine ⟨r, h_r_eq, ?_, h_r_prime, ?_⟩
      · -- r ∣ stripped ∣ n
        exact Nat.dvd_trans h_r_dvd_s h_s_dvd
      · -- Maximality: ∀ q > r prime, ¬ q ∣ n.
        intro q h_q_gt h_q_prime h_q_dvd_n
        -- We know r ∣ stripped, r is prime. So r.toNat ≥ 2 ≥ p.toNat (we need r ≥ p).
        -- Actually we need r ≥ 2, which is given by r is prime. q > r ≥ 2.
        -- For q to be coprime with p, need q ≠ p.
        -- If q = p: q ∣ n, q ≠ stripped's primes... hmm need to show q ≠ p.
        -- Actually q > r where r ∣ stripped, p ∤ stripped, so r ≠ p (since p ∤ stripped).
        -- So if q = p, then q = p ≤ r (since r ≥ p smallest)... wait this needs r ≥ p.
        -- Let me think again: r ∣ stripped, p ∤ stripped, so p ∤ r. So r ≠ p, r ≠ some_multiple_of_p.
        -- The maximality argument: q > r ≥ ? We need q ≠ p so we can use coprime.
        -- Suppose q = p: then q = p ≤ n's smallest divisor = p. Then r > q = p? Not nec.
        -- Hmm. Let me think differently.
        -- Actually, r is prime and r ∣ stripped, and p is the smallest prime factor of n.
        -- We have h_p_min: ∀ k, 2 ≤ k → k < p.toNat → ¬ k ∣ n.toNat.
        -- r is prime ≥ 2, r ∣ n (since r ∣ stripped ∣ n). So r ≥ p (else r would contradict h_p_min).
        have h_r_dvd_n : r.toNat ∣ n.toNat := Nat.dvd_trans h_r_dvd_s h_s_dvd
        have h_r_ge_p : p.toNat ≤ r.toNat := by
          rcases Nat.lt_or_ge r.toNat p.toNat with h_r_lt | h_r_ge
          · exfalso
            exact h_p_min r.toNat h_r_prime.1 h_r_lt h_r_dvd_n
          · exact h_r_ge
        -- Now q > r ≥ p, so q > p, so q ≠ p. Coprime.
        have h_q_ne_p : q ≠ p.toNat := by omega
        have h_cop : Nat.Coprime q p.toNat :=
          coprime_of_distinct_primes p.toNat q h_p_prime h_q_prime h_q_ne_p
        -- q ∣ n, q coprime p ⇒ q ∣ stripped (by enhanced strip_factor spec)
        have h_q_dvd_s : q ∣ stripped.toNat := h_s_coprime q h_cop h_q_dvd_n
        -- By IH maximality, ¬ q ∣ stripped. Contradiction.
        exact h_r_max q h_q_gt h_q_prime h_q_dvd_s

private theorem largest_prime_at_spec (n c : u64)
    (h_n_lo : 2 ≤ n.toNat) (h_n_hi : n.toNat < 2 ^ 32) :
    ∃ r : u64,
      clever_058_largest_prime_factor.largest_prime_at n c = RustM.ok r
      ∧ r.toNat ∣ n.toNat
      ∧ is_prime_nat r.toNat
      ∧ ∀ q : Nat, r.toNat < q → is_prime_nat q → ¬ q ∣ n.toNat :=
  largest_prime_at_spec_aux n.toNat n c (Nat.le_refl _) h_n_lo h_n_hi

/-! ## Theorem 1: degenerate case (n ≤ 1 returns sentinel 1) -/

/-- Failure/edge clause: for any `n ≤ 1`, `largest_prime_factor n`
    returns the sentinel value `1`.

    Captures the Rust property test `degenerate_n_le_one`. -/
theorem largest_prime_factor_degenerate
    (n : u64) (h : n.toNat ≤ 1) :
    clever_058_largest_prime_factor.largest_prime_factor n = RustM.ok (1 : u64) := by
  unfold clever_058_largest_prime_factor.largest_prime_factor
  have h_le : n ≤ (1 : u64) := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [u64_one_toNat]; exact h
  have h_dec : decide (n ≤ (1 : u64)) = true := decide_eq_true h_le
  simp only [show (n <=? (1 : u64)) =
               (pure (decide (n ≤ (1 : u64))) : RustM Bool) from rfl,
             h_dec, pure_bind, ↓reduceIte]
  rfl

/-! ## Postcondition 1 (divides): TODO -/

/-- Reduction lemma: for `n ≥ 2`, `largest_prime_factor n` calls
    `largest_prime_at n 1`. -/
private theorem largest_prime_factor_step (n : u64) (h : 2 ≤ n.toNat) :
    clever_058_largest_prime_factor.largest_prime_factor n
      = clever_058_largest_prime_factor.largest_prime_at n (1 : u64) := by
  conv => lhs; unfold clever_058_largest_prime_factor.largest_prime_factor
  have h_not_le : ¬ n ≤ (1 : u64) := by
    intro hle
    have := UInt64.le_iff_toNat_le.mp hle
    rw [u64_one_toNat] at this; omega
  have h_dec : decide (n ≤ (1 : u64)) = false := decide_eq_false h_not_le
  simp only [show (n <=? (1 : u64)) =
               (pure (decide (n ≤ (1 : u64))) : RustM Bool) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]

theorem largest_prime_factor_divides_n
    (n : u64) (h_lo : 2 ≤ n.toNat) (h_hi : n.toNat < 2 ^ 32) :
    ∃ p : u64,
      clever_058_largest_prime_factor.largest_prime_factor n = RustM.ok p
      ∧ p.toNat ∣ n.toNat := by
  rw [largest_prime_factor_step n h_lo]
  obtain ⟨r, h_eq, h_dvd, _, _⟩ := largest_prime_at_spec n (1 : u64) h_lo h_hi
  exact ⟨r, h_eq, h_dvd⟩

theorem largest_prime_factor_is_prime
    (n : u64) (h_lo : 2 ≤ n.toNat) (h_hi : n.toNat < 2 ^ 32) :
    ∃ p : u64,
      clever_058_largest_prime_factor.largest_prime_factor n = RustM.ok p
      ∧ is_prime_nat p.toNat := by
  rw [largest_prime_factor_step n h_lo]
  obtain ⟨r, h_eq, _, h_prime, _⟩ := largest_prime_at_spec n (1 : u64) h_lo h_hi
  exact ⟨r, h_eq, h_prime⟩

theorem largest_prime_factor_is_maximal
    (n : u64) (h_lo : 2 ≤ n.toNat) (h_hi : n.toNat < 2 ^ 32) :
    ∃ p : u64,
      clever_058_largest_prime_factor.largest_prime_factor n = RustM.ok p
      ∧ ∀ q : Nat, p.toNat < q → is_prime_nat q → ¬ q ∣ n.toNat := by
  rw [largest_prime_factor_step n h_lo]
  obtain ⟨r, h_eq, _, _, h_max⟩ := largest_prime_at_spec n (1 : u64) h_lo h_hi
  exact ⟨r, h_eq, h_max⟩

end Clever_058_largest_prime_factorObligations
