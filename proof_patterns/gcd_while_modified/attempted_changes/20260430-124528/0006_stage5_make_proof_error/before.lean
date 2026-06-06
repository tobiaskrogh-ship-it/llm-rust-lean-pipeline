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
    panic site is `a %? b`, guarded by the loop condition `b !=? 0`, and
    the `loop_decreases!(b)` measure forces termination. We derive this
    via `hax_mvcgen`, which emits the `while_loop`'s step obligation; the
    residual goal is `(a %? b).toNat < b.toNat` under the loop guard
    `b ≠ 0`, dispatched by `Nat.mod_lt`. -/
private theorem gcd_while_triple_true (a b : u64) :
    ⦃ ⌜ True ⌝ ⦄ gcd_while.gcd_while a b ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  hax_mvcgen [gcd_while.gcd_while]
  all_goals first
    | (subst_eqs; simp_all; done)
    | (simp only [UInt64.toNat_mod]
       refine Nat.mod_lt _ ?_
       simp_all
       omega)
    | grind
    | omega

/-- Totality / panic-freedom.
    For every pair of `u64` inputs, `gcd_while` returns a value
    successfully. The function has two potential failure modes:
      * the modulo `a %? b` panics on `b = 0`, which is prevented by
        the loop's `b !=? 0` exit condition (the loop body only runs
        when `b ≠ 0`);
      * the `while_loop` combinator could diverge, which is prevented
        by the `loop_decreases!(b)` measure — `b` decreases strictly
        on each iteration (the new `b` is `a % old_b`, which is
        strictly less than `old_b`).
    Combined, these guarantee `gcd_while a b = pure v` for some `v`.

    Proof: route the trivial Hoare triple `⦃True⦄ … ⦃⇓ _ => True⌝⦄`
    through `RustM.Triple_iff_BitVec` to extract `(gcd_while a b).toBVRustM.ok`.
    A case-split on `gcd_while a b` then collapses every failure /
    divergence branch by contradiction, leaving the `RustM.ok` branch. -/
theorem gcd_while_total (a b : u64) :
    ∃ v : u64, gcd_while.gcd_while a b = pure v := by
  have htriple := gcd_while_triple_true a b
  rw [RustM.Triple_iff_BitVec] at htriple
  simp only [decide_true, Bool.not_true, Bool.false_or, Bool.and_true,
             decide_true] at htriple
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

/-- Postcondition (loop-exit base case):
    when `b = 0`, the loop's exit condition `b !=? 0` is false on entry,
    so the loop body never executes. The function therefore returns `a`
    successfully. -/
theorem gcd_while_b_zero (a : u64) :
    gcd_while.gcd_while a 0 = pure a := by
  sorry

end Gcd_whileObligations
