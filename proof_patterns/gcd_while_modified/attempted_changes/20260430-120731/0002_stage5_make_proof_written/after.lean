-- Companion obligations file for the `gcd_while` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import gcd_while

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Gcd_whileObligations

/-- Internal Hoare triple capturing termination + no-panic.

    The function `gcd_while.gcd_while a b` cannot panic and cannot diverge:
    the only panic site is `a %? b`, guarded by the loop condition `b ≠ 0`,
    and the `loop_decreases!(b)` measure forces termination. We prove this
    via `hax_mvcgen`, which discharges the loop spec given the user-supplied
    invariant (which is `True` in this function) and termination measure
    (`b.toNat`). -/
private theorem gcd_while_triple_true (a b : u64) :
    ⦃ ⌜ True ⌝ ⦄ gcd_while.gcd_while a b ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  hax_mvcgen [gcd_while.gcd_while] <;> grind

/-- Totality / no-panic.
    For every pair of `u64` inputs, `gcd_while` returns a value (it never
    panics and never diverges in the `RustM` sense).

    The only Rust operation in the body that could panic is `a % b`,
    which would fail with `divisionByZero` if `b = 0`. The loop guard
    `b !=? 0` excludes that case, so the modulo is always well-defined.
    Termination is witnessed by the `loop_decreases!(b)` measure: after
    one iteration, the new `b` equals `a % b₀ < b₀` whenever `b₀ > 0`. -/
theorem gcd_while_total (a b : u64) :
    ∃ r : u64, gcd_while.gcd_while a b = pure r := by
  have htriple := gcd_while_triple_true a b
  rw [RustM.Triple_iff_BitVec] at htriple
  -- htriple now says: True implies that the result is .ok
  simp only [decide_True, Bool.not_true, Bool.false_or, decide_eq_true_eq,
    Bool.and_true] at htriple
  -- Extract the witness from `(gcd_while a b).toBVRustM.ok = true`.
  generalize hg : gcd_while.gcd_while a b = g at *
  cases g using RustM.toBVRustM.match_1 with
  | h_1 v =>
    exact ⟨v, rfl⟩
  | _ => simp [RustM.toBVRustM] at htriple

/-- Postcondition (common divisor).
    Whenever `gcd_while a b` returns a value `r`, that value divides both
    inputs (taken as `Nat`s via `.toNat`). At the boundary `a = b = 0`
    the result is `0` and the claim `0 ∣ 0` holds trivially.

    UNPROVED: This obligation requires a strengthened loop invariant
    `∀ d, d ∣ a ∧ d ∣ b ↔ d ∣ a₀ ∧ d ∣ b₀` that links the loop's
    iterating state to the original inputs. The current Rust source has
    only `loop_decreases!(b)` and no `loop_invariant!()`, so the
    user-supplied invariant in the extracted function is `True`. To
    discharge this obligation, one would either (a) add a
    `loop_invariant!()` annotation to the Rust source, or (b) inline the
    loop in Lean and prove a custom Hoare triple via
    `Spec.MonoLoopCombinator.while_loop` with the strengthened invariant. -/
theorem gcd_while_divides_both (a b r : u64)
    (h : gcd_while.gcd_while a b = pure r) :
    r.toNat ∣ a.toNat ∧ r.toNat ∣ b.toNat := by
  sorry

/-- Postcondition (greatest, in the divides ordering).
    Any common divisor `d` of the two inputs also divides the returned
    result `r`. This is the strongest form of "greatest common divisor"
    and it is well-defined even at the `(0, 0)` boundary (where `r = 0`
    and `d ∣ 0` holds for every `d`).

    UNPROVED: Same obstacle as `gcd_while_divides_both`. The proof
    requires a strengthened loop invariant relating the iterated state
    to the original inputs (specifically, the divisor-set equivalence
    of `Euclid`'s algorithm). The Rust source lacks the
    `loop_invariant!()` annotation that would supply this invariant
    to the extracted Lean spec. -/
theorem gcd_while_greatest (a b r : u64)
    (h : gcd_while.gcd_while a b = pure r)
    (d : u64) (hda : d.toNat ∣ a.toNat) (hdb : d.toNat ∣ b.toNat) :
    d.toNat ∣ r.toNat := by
  sorry

end Gcd_whileObligations
