-- Companion obligations file for the `clever_013_greatest_common_divisor` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_013_greatest_common_divisor

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_013_greatest_common_divisorObligations

/-! ## Nat-bridge helpers (mirroring `gcd_while_modified`) -/

private theorem gcd_lt_2_64 (a b : u64) : Nat.gcd a.toNat b.toNat < 2 ^ 64 := by
  by_cases hb : b.toNat = 0
  · rw [hb, Nat.gcd_zero_right]
    exact a.toNat_lt
  · have h_le : Nat.gcd a.toNat b.toNat ≤ b.toNat :=
      Nat.gcd_le_right a.toNat (Nat.pos_of_ne_zero hb)
    exact Nat.lt_of_le_of_lt h_le b.toNat_lt

private theorem gcd_toNat_ofNat (a b : u64) :
    (UInt64.ofNat (Nat.gcd a.toNat b.toNat)).toNat = Nat.gcd a.toNat b.toNat :=
  UInt64.toNat_ofNat_of_lt' (gcd_lt_2_64 a b)

/-! ## Closed-form postcondition

The function reduces to `Nat.gcd` on the `toNat` projections of its inputs.
Mirrors the `recursion_example` pattern: strong induction on the measure
`b.toNat` (Euclid's lemma: `(a % b).toNat < b.toNat` when `b > 0`), with
`Nat.gcd_rec` + `Nat.gcd_comm` carrying the algebraic invariant through
each recursive call. -/
theorem greatest_common_divisor_postcondition (a b : u64) :
    clever_013_greatest_common_divisor.greatest_common_divisor a b
      = RustM.ok (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) := by
  induction hk : b.toNat using Nat.strongRecOn generalizing a b with
  | _ k ih =>
    unfold clever_013_greatest_common_divisor.greatest_common_divisor
    by_cases hb : b = 0
    · -- Base case: b = 0. Function returns `pure a`.
      subst hb
      simp only [show ((0 : u64) ==? (0 : u64)) =
                   (pure (decide ((0 : u64) = (0 : u64))) : RustM Bool) from rfl,
                 pure_bind]
      -- After simp, the `if` reduces automatically (`decide ((0:u64) = (0:u64))`
      -- reduces to `true` definitionally). Goal:
      --   pure a = RustM.ok (UInt64.ofNat (Nat.gcd a.toNat k))
      apply congrArg RustM.ok
      apply UInt64.toNat_inj.mp
      -- Bring `k` back to `(0:u64).toNat` so `gcd_toNat_ofNat` can match.
      rw [← hk, gcd_toNat_ofNat, show ((0 : u64).toNat = 0) from rfl, Nat.gcd_zero_right]
    · -- Step case: b ≠ 0. Reduce ==? and %?, then apply IH.
      have hb_pos : 0 < b.toNat := by
        rcases Nat.eq_zero_or_pos b.toNat with h | h
        · exfalso; apply hb; apply UInt64.toNat_inj.mp; rw [h]; rfl
        · exact h
      have h_neq : (decide (b = (0 : u64))) = false := decide_eq_false hb
      simp only [show (b ==? (0 : u64)) =
                   (pure (decide (b = (0 : u64))) : RustM Bool) from rfl,
                 h_neq, pure_bind]
      have h_rem : (a %? b : RustM u64) = pure (a % b) := by
        show (rust_primitives.ops.arith.Rem.rem a b : RustM u64) = pure (a % b)
        show (if b = 0 then (.fail .divisionByZero : RustM u64) else pure (a % b))
              = pure (a % b)
        rw [if_neg hb]
      rw [h_rem]
      simp only [pure_bind]
      -- Goal: greatest_common_divisor b (a % b) = RustM.ok (UInt64.ofNat (Nat.gcd a.toNat b.toNat))
      have h_term_lt : (a % b).toNat < k := by
        rw [← hk, UInt64.toNat_mod]
        exact Nat.mod_lt _ hb_pos
      rw [ih (a % b).toNat h_term_lt b (a % b) rfl]
      apply congrArg RustM.ok
      apply UInt64.toNat_inj.mp
      -- Bring `k` back to `b.toNat` so `gcd_toNat_ofNat` matches the RHS form.
      rw [← hk, gcd_toNat_ofNat, gcd_toNat_ofNat]
      -- Goal: Nat.gcd b.toNat (a % b).toNat = Nat.gcd a.toNat b.toNat
      rw [UInt64.toNat_mod, Nat.gcd_comm b.toNat, ← Nat.gcd_rec, Nat.gcd_comm]

/-! ## Contract clauses derived from the closed form -/

/-- Totality / no-panic. -/
theorem greatest_common_divisor_total (a b : u64) :
    ∃ v : u64,
      clever_013_greatest_common_divisor.greatest_common_divisor a b
        = RustM.ok v :=
  ⟨_, greatest_common_divisor_postcondition a b⟩

/-- Base case 1: `gcd(a, 0) = a`. -/
theorem greatest_common_divisor_b_zero (a : u64) :
    clever_013_greatest_common_divisor.greatest_common_divisor a 0
      = RustM.ok a := by
  rw [greatest_common_divisor_postcondition]
  congr 1
  apply UInt64.toNat_inj.mp
  rw [gcd_toNat_ofNat, show ((0 : u64).toNat = 0) from rfl, Nat.gcd_zero_right]

/-- Base case 2: `gcd(0, b) = b`. -/
theorem greatest_common_divisor_a_zero (b : u64) :
    clever_013_greatest_common_divisor.greatest_common_divisor 0 b
      = RustM.ok b := by
  rw [greatest_common_divisor_postcondition]
  congr 1
  apply UInt64.toNat_inj.mp
  rw [gcd_toNat_ofNat, show ((0 : u64).toNat = 0) from rfl, Nat.gcd_zero_left]

/-- The result divides `a` (common-divisor half). -/
theorem greatest_common_divisor_divides_a (a b : u64) :
    ∃ v : u64,
      clever_013_greatest_common_divisor.greatest_common_divisor a b
        = RustM.ok v
      ∧ v.toNat ∣ a.toNat := by
  refine ⟨_, greatest_common_divisor_postcondition a b, ?_⟩
  rw [gcd_toNat_ofNat]
  exact Nat.gcd_dvd_left a.toNat b.toNat

/-- The result divides `b` (common-divisor half). -/
theorem greatest_common_divisor_divides_b (a b : u64) :
    ∃ v : u64,
      clever_013_greatest_common_divisor.greatest_common_divisor a b
        = RustM.ok v
      ∧ v.toNat ∣ b.toNat := by
  refine ⟨_, greatest_common_divisor_postcondition a b, ?_⟩
  rw [gcd_toNat_ofNat]
  exact Nat.gcd_dvd_right a.toNat b.toNat

/-- Every common divisor of `a` and `b` divides the result. -/
theorem greatest_common_divisor_greatest (a b : u64) :
    ∃ v : u64,
      clever_013_greatest_common_divisor.greatest_common_divisor a b
        = RustM.ok v
      ∧ ∀ d : Nat, d ∣ a.toNat → d ∣ b.toNat → d ∣ v.toNat := by
  refine ⟨_, greatest_common_divisor_postcondition a b, ?_⟩
  intro d hda hdb
  rw [gcd_toNat_ofNat]
  exact Nat.dvd_gcd hda hdb

/-- If the result is `0`, then both inputs are `0`. -/
theorem greatest_common_divisor_zero_iff (a b : u64) :
    ∃ v : u64,
      clever_013_greatest_common_divisor.greatest_common_divisor a b
        = RustM.ok v
      ∧ (v = 0 → a = 0 ∧ b = 0) := by
  refine ⟨_, greatest_common_divisor_postcondition a b, ?_⟩
  intro hv
  -- hv : UInt64.ofNat (Nat.gcd a.toNat b.toNat) = 0
  have h_gcd_zero : Nat.gcd a.toNat b.toNat = 0 := by
    have h := congrArg UInt64.toNat hv
    rw [gcd_toNat_ofNat] at h
    exact h
  -- From gcd = 0: gcd | a and gcd | b, so 0 | a and 0 | b, so a = b = 0.
  have h_dvd_a : Nat.gcd a.toNat b.toNat ∣ a.toNat := Nat.gcd_dvd_left _ _
  have h_dvd_b : Nat.gcd a.toNat b.toNat ∣ b.toNat := Nat.gcd_dvd_right _ _
  rw [h_gcd_zero] at h_dvd_a h_dvd_b
  have ha_nat : a.toNat = 0 := Nat.eq_zero_of_zero_dvd h_dvd_a
  have hb_nat : b.toNat = 0 := Nat.eq_zero_of_zero_dvd h_dvd_b
  refine ⟨?_, ?_⟩
  · apply UInt64.toNat_inj.mp; rw [ha_nat]; rfl
  · apply UInt64.toNat_inj.mp; rw [hb_nat]; rfl

end Clever_013_greatest_common_divisorObligations
