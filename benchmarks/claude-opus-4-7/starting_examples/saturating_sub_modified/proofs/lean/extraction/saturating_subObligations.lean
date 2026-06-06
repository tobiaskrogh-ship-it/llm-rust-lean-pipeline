-- Obligations for the `saturating_sub` crate.
-- Each theorem captures one independent clause of the function's contract.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import saturating_sub

open Std.Do
open Std.Tactic
open saturating_sub

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace saturating_subObligations

/-- Postcondition (normal case): when `b < a`, the function returns `a - b`
    successfully (no underflow, no panic). -/
theorem saturating_sub_postcondition_normal (a b : u8) (h : b < a) :
    saturating_sub a b = pure (a - b) := by
  -- Unfold the function and the comparison; the do-bind on a `pure` collapses,
  -- and the inner subtraction unfolds to its `if BitVec.usubOverflow…` form.
  simp only [saturating_sub, rust_primitives.cmp.gt,
             rust_primitives.ops.arith.Sub.sub]
  -- `a > b` holds, so the outer `if` selects the subtraction branch.
  have hgt : a > b := h
  -- The subtraction does not underflow: from `b < a` for `UInt8` we have
  -- `b.toNat < a.toNat`, hence `¬ (a.toNat < b.toNat)`. Pre-rewrite the goal’s
  -- `BitVec.usubOverflow a.toBitVec b.toBitVec` into the `UInt8.subOverflow a b`
  -- form so that `UInt8.subOverflow_iff` applies cleanly.
  have hno_overflow : ¬ (BitVec.usubOverflow a.toBitVec b.toBitVec = true) := by
    show ¬ (UInt8.subOverflow a b = true)
    rw [UInt8.subOverflow_iff]
    have hlt : b.toNat < a.toNat := UInt8.lt_iff_toNat_lt.mp h
    omega
  simp [hgt, hno_overflow]

/-- Postcondition (saturation case): when `a ≤ b`, the function returns `0`
    (saturating instead of underflowing). -/
theorem saturating_sub_postcondition_saturating (a b : u8) (h : a ≤ b) :
    saturating_sub a b = pure (0 : u8) := by
  -- Unfold the function and the comparison; the do-bind on `pure (decide (a > b))`
  -- collapses, and `a > b` is false from `h : a ≤ b`.
  simp only [saturating_sub, rust_primitives.cmp.gt]
  have hngt : ¬ (a > b) := by
    -- `a > b` is by definition `b < a`; combined with `a ≤ b` it forces `a < a` on toNat.
    intro hgt
    have hba : b < a := hgt
    have hltN : b.toNat < a.toNat := UInt8.lt_iff_toNat_lt.mp hba
    have hleN : a.toNat ≤ b.toNat := UInt8.le_iff_toNat_le.mp h
    omega
  simp [hngt]

/-- Totality / no-panic: for every pair of `u8` inputs, the function returns
    a value (it never panics). Saturating arithmetic's defining feature is
    that it has no failure mode. -/
theorem saturating_sub_total (a b : u8) :
    ∃ v : u8, saturating_sub a b = pure v := by
  by_cases h : b < a
  · exact ⟨a - b, saturating_sub_postcondition_normal a b h⟩
  · -- `¬ (b < a)` together with totality of `≤` on `UInt8` gives `a ≤ b`.
    have hle : a ≤ b := by
      have hb : ¬ (b.toNat < a.toNat) := by
        intro hlt; exact h (UInt8.lt_iff_toNat_lt.mpr hlt)
      apply UInt8.le_iff_toNat_le.mpr; omega
    exact ⟨0, saturating_sub_postcondition_saturating a b hle⟩

end saturating_subObligations
