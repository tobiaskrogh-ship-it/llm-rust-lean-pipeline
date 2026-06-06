-- Companion obligations file for the `clever_101_choose_num` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_101_choose_num

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_101_choose_numObligations

open clever_101_choose_num

/-- An `i64` value is even, interpreted at the `Int` level (sign-agnostic).
    Bridges Rust's `y % 2 == 0` check to a clean mathematical statement. -/
private abbrev isEven (z : i64) : Prop := z.toInt % 2 = 0

/-! ## Contract clauses

`choose_num` is total in the Lean model: the only partial operations on
the path are `y %? 2` (safe because `2 ≠ 0, -1`) and `y -? 1` (only
reached when `y` is odd, and `Int64.minValue` is even, so `y ≠ minValue`
and the signed subtraction does not underflow). No precondition is
required for any of the postcondition theorems below. -/

/-- Failure characterization (sentinel iff): `choose_num x y` returns the
    `-1` sentinel exactly when no even integer exists in `[x, y]`. No even
    exists iff `x > y` (empty range) or `x = y` with `x` odd
    (single-odd range). Corresponds to Rust proptest
    `returns_neg1_iff_no_even_in_range`. -/
theorem choose_num_returns_neg1_iff (x y : i64) :
    ∃ r : i64, choose_num x y = RustM.ok r ∧
      (r = (-1 : i64) ↔ y < x ∨ (x = y ∧ ¬ isEven x)) := by
  sorry

/-- Postcondition (evenness): a non-sentinel result is an even integer.
    Corresponds to Rust proptest `result_is_even_when_valid`. -/
theorem choose_num_result_is_even (x y : i64) :
    ∃ r : i64, choose_num x y = RustM.ok r ∧
      (r ≠ (-1 : i64) → isEven r) := by
  sorry

/-- Postcondition (range, lower bound): a non-sentinel result is at least `x`.
    Sub-clause of Rust proptest `result_in_range_when_valid`. -/
theorem choose_num_result_ge_x (x y : i64) :
    ∃ r : i64, choose_num x y = RustM.ok r ∧
      (r ≠ (-1 : i64) → x ≤ r) := by
  sorry

/-- Postcondition (range, upper bound): a non-sentinel result is at most `y`.
    Sub-clause of Rust proptest `result_in_range_when_valid`. -/
theorem choose_num_result_le_y (x y : i64) :
    ∃ r : i64, choose_num x y = RustM.ok r ∧
      (r ≠ (-1 : i64) → r ≤ y) := by
  sorry

/-- Postcondition (maximality): for a non-sentinel result, the next even
    candidate `r + 2` (at the `Int` level) exceeds `y`, so no larger even
    integer exists in `[x, y]`. Stated at `Int` level because for
    `r = i64::MAX - 1` the i64-level `r + 2` would overflow even though
    the mathematical maximality property holds. Corresponds to Rust
    proptest `result_is_maximal_when_valid`. -/
theorem choose_num_result_is_maximal (x y : i64) :
    ∃ r : i64, choose_num x y = RustM.ok r ∧
      (r ≠ (-1 : i64) → r.toInt + 2 > y.toInt) := by
  sorry

end Clever_101_choose_numObligations
