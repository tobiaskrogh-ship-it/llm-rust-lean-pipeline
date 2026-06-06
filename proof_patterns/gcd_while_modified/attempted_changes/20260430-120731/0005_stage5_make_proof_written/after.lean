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

    `gcd_while.gcd_while a b` cannot panic and cannot diverge: the only
    panic site is `a %? b`, guarded by the loop condition `b ≠ 0`, and
    the `loop_decreases!(b)` measure forces termination. -/
private theorem gcd_while_triple_true (a b : u64) :
    ⦃ ⌜ True ⌝ ⦄ gcd_while.gcd_while a b ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  hax_mvcgen [gcd_while.gcd_while]
  all_goals first
    | (subst_eqs; simp_all)
    | (have hb : (_ : u64).toNat ≠ 0 := by simp_all
       have := Nat.mod_lt _ (Nat.pos_of_ne_zero hb)
       simp_all [UInt64.toNat_mod]
       omega)
    | grind
    | omega

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
  simp only [decide_true, Bool.not_true, Bool.false_or, Bool.and_true] at htriple
  generalize hg : gcd_while.gcd_while a b = g at htriple
  cases g using RustM.toBVRustM.match_1 with
  | h_1 v => exact ⟨v, rfl⟩
  | h_2 => simp [RustM.toBVRustM] at htriple
  | h_3 => simp [RustM.toBVRustM] at htriple
  | h_4 => simp [RustM.toBVRustM] at htriple
  | h_5 => simp [RustM.toBVRustM] at htriple
  | h_6 => simp [RustM.toBVRustM] at htriple
  | h_7 => simp [RustM.toBVRustM] at htriple
  | h_8 => simp [RustM.toBVRustM] at htriple
  | h_9 => simp [RustM.toBVRustM] at htriple

/-- Postcondition (common divisor).
    Whenever `gcd_while a b` returns a value `r`, that value divides both
    inputs (taken as `Nat`s via `.toNat`). At the boundary `a = b = 0`
    the result is `0` and the claim `0 ∣ 0` holds trivially.

    ADMITTED. The Rust source has only `loop_decreases!(b)` and no
    `loop_invariant!()`. Consequently the user-supplied `inv` argument
    in the extracted `rust_primitives.hax.while_loop` reduces — via
    `hax_construct_pure` — to `fun _ => True`, so the strongest
    Hoare-triple postcondition the loop spec lemma yields is `True ∧
    ¬(b !=? 0)`, i.e., the exit value `r` satisfies `b = 0` but nothing
    is known about `a`. This is too weak to prove that `r` divides
    either input. Closing this obligation requires either:

      (a) Adding a `loop_invariant!(|(a, b)| ∀ d, d ∣ a₀ ∧ d ∣ b₀ ↔
          d ∣ a ∧ d ∣ b)` to the Rust source so that the extracted
          `inv` carries the gcd divisor-set invariant.
      (b) Inlining the loop in Lean and applying
          `Spec.MonoLoopCombinator.while_loop` directly with that
          invariant — non-trivial because none of the reference
          examples demonstrate this pattern. -/
theorem gcd_while_divides_both (a b r : u64)
    (h : gcd_while.gcd_while a b = pure r) :
    r.toNat ∣ a.toNat ∧ r.toNat ∣ b.toNat := by
  sorry

/-- Postcondition (greatest, in the divides ordering).
    Any common divisor `d` of the two inputs also divides the returned
    result `r`. This is the strongest form of "greatest common divisor"
    and it is well-defined even at the `(0, 0)` boundary (where `r = 0`
    and `d ∣ 0` holds for every `d`).

    ADMITTED. Same obstacle as `gcd_while_divides_both`: the source
    function lacks the `loop_invariant!()` annotation that would
    propagate the divisor-set invariant from the original inputs to
    the loop's iterating state. -/
theorem gcd_while_greatest (a b r : u64)
    (h : gcd_while.gcd_while a b = pure r)
    (d : u64) (hda : d.toNat ∣ a.toNat) (hdb : d.toNat ∣ b.toNat) :
    d.toNat ∣ r.toNat := by
  sorry

end Gcd_whileObligations
