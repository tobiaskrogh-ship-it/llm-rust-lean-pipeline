-- Companion obligations file for the `clever_056_monotonic` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_056_monotonic

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_056_monotonicObligations

/-! ## Specification: pairwise predicates on the underlying `i64` list. -/

/-- `l` is non-decreasing: every adjacent pair `(l[j], l[j+1])` is `≤`. -/
private def is_nondec (l : RustSlice i64) : Prop :=
  ∀ j : Nat, ∀ (hj1 : j + 1 < l.val.size),
    l.val[j]'(Nat.lt_of_succ_lt hj1) ≤ l.val[j+1]'hj1

/-- `l` is non-increasing: every adjacent pair `(l[j+1], l[j])` is `≤`. -/
private def is_noninc (l : RustSlice i64) : Prop :=
  ∀ j : Nat, ∀ (hj1 : j + 1 < l.val.size),
    l.val[j+1]'hj1 ≤ l.val[j]'(Nat.lt_of_succ_lt hj1)

/-! ## Top-level contract clauses. -/

/-- Boundary clause (from `small_lists_are_monotonic`):
    a list of length 0 or 1 is vacuously monotonic. -/
theorem monotonic_small_lists (l : RustSlice i64) (h : l.val.size ≤ 1) :
    clever_056_monotonic.monotonic l = RustM.ok true := by
  sorry

/-- Forward direction of the main postcondition (from `matches_brute_force`):
    if the underlying list is non-decreasing or non-increasing, `monotonic`
    returns `true`. Together with `monotonic_returns_false` this pins down
    the brute-force oracle. -/
theorem monotonic_returns_true (l : RustSlice i64)
    (h : is_nondec l ∨ is_noninc l) :
    clever_056_monotonic.monotonic l = RustM.ok true := by
  sorry

/-- Backward direction of the main postcondition (from `matches_brute_force`):
    if the underlying list is neither non-decreasing nor non-increasing, then
    `monotonic` returns `false`. A correct implementation must not return
    `true` for a list with a strictly-up and a strictly-down adjacent pair. -/
theorem monotonic_returns_false (l : RustSlice i64)
    (h : ¬ is_nondec l ∧ ¬ is_noninc l) :
    clever_056_monotonic.monotonic l = RustM.ok false := by
  sorry

/-- Plateau clause (from `constant_list_is_monotonic`):
    a constant list is monotonic. This is the independent test that pins
    down strict `>` / `<` comparisons in the helpers (a buggy `≥` / `≤`
    implementation would fail this on any non-empty constant list). -/
theorem monotonic_constant (l : RustSlice i64) (c : i64)
    (hconst : ∀ i : Nat, ∀ (hi : i < l.val.size), l.val[i]'hi = c) :
    clever_056_monotonic.monotonic l = RustM.ok true := by
  sorry

end Clever_056_monotonicObligations
