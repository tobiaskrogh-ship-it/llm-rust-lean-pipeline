-- Companion obligations file for the `gcd_rec` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import gcd_rec

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Gcd_recObligations

/-- Workhorse: closed-form characterization of `gcd_rec`.

    `gcd_rec.gcd_rec a b` succeeds and returns the encoded mathematical
    `Nat.gcd` of `b.toNat` and `a.toNat`. The order is swapped because the
    function recurses as `gcd_rec b (a % b)`, matching the recurrence
    `Nat.gcd_rec : gcd m n = gcd (n % m) m` with `m = b` and `n = a`.
    `Nat.gcd` is symmetric, so the two orders agree on the value. -/
private theorem gcd_rec_eq (a b : u64) :
    gcd_rec.gcd_rec a b = pure (UInt64.ofNat (Nat.gcd b.toNat a.toNat)) := by
  induction hk : b.toNat using Nat.strongRecOn generalizing a b
  rename_i k ih
  rw [gcd_rec.gcd_rec]
  simp only [show ((b ==? (0 : u64)) : RustM Bool) = pure (b == 0) from rfl, pure_bind]
  by_cases hk_zero : k = 0
  · -- Base case: `b.toNat = 0`, so `b = 0` and the function returns `pure a`.
    have hb0 : b = 0 := by
      apply UInt64.toNat_inj.mp
      rw [hk, hk_zero]
      rfl
    subst hb0
    subst hk_zero
    have hbeq : ((0 : u64) == (0 : u64)) = true := by decide
    rw [if_pos hbeq]
    rw [Nat.gcd_zero_left]
    -- Goal: `pure a = pure (UInt64.ofNat a.toNat)`
    have ha : UInt64.ofNat a.toNat = a := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_ofNat_of_lt' a.toNat_lt]
    rw [ha]
  · -- Inductive case: `b ≠ 0`. Peel one recursive step and apply the IH.
    have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_zero
    have hb_toNat_pos : 0 < b.toNat := hk ▸ hk_pos
    have hb_ne : b ≠ 0 := by
      intro h
      have : b.toNat = 0 := by rw [h]; rfl
      omega
    have hbne : ¬ (b == (0 : u64)) = true := by
      intro h
      apply hb_ne
      simpa using h
    rw [if_neg hbne]
    -- `a %? b` reduces to `pure (a % b)` because `b ≠ 0`.
    have hmod : (a %? b : RustM u64) = pure (a % b) := by
      show (rust_primitives.ops.arith.Rem.rem a b : RustM u64) = pure (a % b)
      simp only [rust_primitives.ops.arith.Rem.rem]
      rw [if_neg hb_ne]
    rw [hmod, pure_bind]
    -- Apply the strong-induction hypothesis at `(b, a % b)`.
    have hmod_lt : (a % b).toNat < k := by
      rw [UInt64.toNat_mod, ← hk]
      exact Nat.mod_lt _ hb_toNat_pos
    rw [ih (a % b).toNat hmod_lt b (a % b) rfl]
    -- Goal:  pure (UInt64.ofNat (Nat.gcd (a%b).toNat b.toNat))
    --      = pure (UInt64.ofNat (Nat.gcd k a.toNat))
    -- Reduce to the underlying Nat identity, which is `Nat.gcd_rec`.
    congr 2
    rw [UInt64.toNat_mod, ← hk]
    exact (Nat.gcd_rec b.toNat a.toNat).symm

/-- Bound used to convert `(UInt64.ofNat (Nat.gcd ..)).toNat` back to
    `Nat.gcd ..`. Either `b.toNat = 0` (then `Nat.gcd 0 a.toNat = a.toNat
    < 2^64`) or `b.toNat > 0` (then `Nat.gcd b.toNat _ ≤ b.toNat < 2^64`). -/
private theorem gcd_lt (a b : u64) : Nat.gcd b.toNat a.toNat < 2 ^ 64 := by
  by_cases hb : b.toNat = 0
  · rw [hb, Nat.gcd_zero_left]
    exact a.toNat_lt
  · have h_le : Nat.gcd b.toNat a.toNat ≤ b.toNat :=
      Nat.gcd_le_left a.toNat (Nat.pos_of_ne_zero hb)
    exact Nat.lt_of_le_of_lt h_le b.toNat_lt

/-- Helper: `(UInt64.ofNat (Nat.gcd b.toNat a.toNat)).toNat` is exactly
    `Nat.gcd b.toNat a.toNat` because the gcd fits in a `u64`. -/
private theorem gcd_toNat_ofNat (a b : u64) :
    (UInt64.ofNat (Nat.gcd b.toNat a.toNat)).toNat = Nat.gcd b.toNat a.toNat :=
  UInt64.toNat_ofNat_of_lt' (gcd_lt a b)

/--
Postcondition (common divisor): the value returned by `gcd_rec a b` is a
common divisor of `a` and `b` — both inputs are exact multiples of the result
when interpreted in `Nat`.

Captures the property tested by `result_divides_both_inputs` in the Rust
source. The boundary case `gcd_rec 0 0 = 0` is admitted automatically because
`0 ∣ 0` holds in `Nat` (trivially: every number divides 0).
-/
theorem gcd_rec_common_divisor (a b : u64) :
    ⦃ ⌜ True ⌝ ⦄
      gcd_rec.gcd_rec a b
    ⦃ ⇓ r => ⌜ r.toNat ∣ a.toNat ∧ r.toNat ∣ b.toNat ⌝ ⦄ := by
  rw [gcd_rec_eq]
  apply Spec.pure'
  refine SPred.pure_intro ?_
  rw [gcd_toNat_ofNat]
  exact ⟨Nat.gcd_dvd_right b.toNat a.toNat, Nat.gcd_dvd_left b.toNat a.toNat⟩

/--
Postcondition (greatest): every common divisor of `a` and `b` divides the
result of `gcd_rec a b`. This is the divisibility-order characterization of
"greatest" — equivalent to `≤` whenever the gcd is nonzero, and uniformly
correct in the boundary `(0, 0)` case (where every natural divides the
result, forcing it to be `0`).

Captures the property tested by `result_is_greatest_common_divisor` in the
Rust source: the result cannot be merely *some* common divisor (e.g. always
`1`); it is the maximal one.
-/
theorem gcd_rec_greatest (a b d : u64) :
    ⦃ ⌜ d.toNat ∣ a.toNat ∧ d.toNat ∣ b.toNat ⌝ ⦄
      gcd_rec.gcd_rec a b
    ⦃ ⇓ r => ⌜ d.toNat ∣ r.toNat ⌝ ⦄ := by
  rw [gcd_rec_eq]
  apply Spec.pure'
  refine SPred.pure_mono ?_
  rintro ⟨hda, hdb⟩
  rw [gcd_toNat_ofNat]
  exact Nat.dvd_gcd hdb hda

end Gcd_recObligations
