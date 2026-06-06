-- Companion obligations file for the `clever_000_has_close_elements` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_000_has_close_elements

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_000_has_close_elementsObligations

open clever_000_has_close_elements

/-- **Guarded special case (failure-like guard on `threshold`).**

    Mirrors the Rust property test `prop_nonpositive_threshold_returns_false`.
    For any non-positive `threshold`, no pair of `f64` values can satisfy the
    strict inequality `|a - b| < threshold` (because `|·| ≥ 0`), so the
    function must return `false` regardless of `numbers`.

    Stated as an equation (precondition is the only constraint, no failure
    branch involved). -/
theorem nonpositive_threshold_returns_false
    (numbers : RustSlice f64) (threshold : f64)
    (h : threshold ≤ 0) :
    has_close_elements numbers threshold = RustM.ok false := by
  sorry

/-- **Soundness (postcondition, `true` branch).**

    Mirrors the Rust property test `prop_soundness_true_implies_witness`.
    If `has_close_elements numbers threshold` evaluates to `true`, then a
    distinct pair of in-bounds indices `i, j` whose values lie strictly
    within `threshold` of each other actually exists in `numbers`. -/
theorem soundness_true_implies_witness
    (numbers : RustSlice f64) (threshold : f64)
    (h : has_close_elements numbers threshold = RustM.ok true) :
    ∃ i j : Nat, ∃ (hi : i < numbers.val.size) (hj : j < numbers.val.size),
      i ≠ j ∧ (numbers.val[i] - numbers.val[j]).abs < threshold := by
  sorry

/-- **Completeness (postcondition, `false` branch).**

    Mirrors the Rust property test `prop_completeness_false_implies_no_witness`.
    If `has_close_elements numbers threshold` evaluates to `false`, then
    *every* distinct pair of in-bounds indices satisfies the negation of the
    strict inequality, i.e. `¬ (|numbers[i] - numbers[j]| < threshold)`. -/
theorem completeness_false_implies_no_witness
    (numbers : RustSlice f64) (threshold : f64)
    (h : has_close_elements numbers threshold = RustM.ok false) :
    ∀ (i j : Nat) (hi : i < numbers.val.size) (hj : j < numbers.val.size),
      i ≠ j → ¬ ((numbers.val[i] - numbers.val[j]).abs < threshold) := by
  sorry

end Clever_000_has_close_elementsObligations
