-- Companion obligations file for the `clever_020_find_closest_elements` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_020_find_closest_elements

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_020_find_closest_elementsObligations

/-! ## Pairwise-difference fit hypothesis

`abs_diff` (called twice per recursive step of `scan_at`) signed-subtracts
two `i64` values and propagates `Error.integerOverflow` on overflow. For the
top-level postconditions to be provable we need that every pairwise
`numbers[i] - numbers[j]` fits in `i64`. The natural symmetric form is:
both directions stay strictly inside the `i64` range, equivalently
`|numbers[i].toInt - numbers[j].toInt| < 2^63` for every pair `(i, j)`.

This precondition is consistent with the proptest range
`-10^9 ≤ numbers[k] ≤ 10^9`, which keeps differences in `[-2·10^9, 2·10^9]`
— well inside `[-(2^63), 2^63)`. We state the broader Lean-truthful version
because the universal statement is the strongest honest contract. -/

private abbrev pairwise_diff_fits (numbers : RustSlice i64) : Prop :=
  ∀ (i j : Nat) (hi : i < numbers.val.size) (hj : j < numbers.val.size),
    -(2^63 : Int) ≤ (numbers.val[i]'hi).toInt - (numbers.val[j]'hj).toInt
    ∧ (numbers.val[i]'hi).toInt - (numbers.val[j]'hj).toInt < 2^63

/-! ## Top-level theorems. -/

/-- Failure / defensive boundary: when the documented precondition
    `numbers.size ≥ 2` is violated, the function returns `(0, 0)`
    successfully. Captures the unit test `short_input_returns_zero_zero`
    (`find_closest_elements(&[]) == (0, 0)` and
    `find_closest_elements(&[42]) == (0, 0)`). -/
theorem short_input_returns_zero_zero
    (numbers : RustSlice i64)
    (hshort : numbers.val.size < 2) :
    clever_020_find_closest_elements.find_closest_elements numbers
      = RustM.ok (rust_primitives.hax.Tuple2.mk (0 : i64) (0 : i64)) := by
  sorry

/-- Postcondition 1 (ordered output): the returned pair `(a, b)` satisfies
    `a ≤ b`. Captures the proptest `result_is_ordered`. -/
theorem result_is_ordered
    (numbers : RustSlice i64)
    (hlen : 2 ≤ numbers.val.size)
    (hfit : pairwise_diff_fits numbers) :
    ∃ a b : i64,
      clever_020_find_closest_elements.find_closest_elements numbers
        = RustM.ok (rust_primitives.hax.Tuple2.mk a b)
      ∧ a.toInt ≤ b.toInt := by
  sorry

/-- Postcondition 2 (values drawn from input): both components of the
    returned pair appear in the input slice, at two distinct positions.
    Captures the proptest `result_elements_drawn_from_input`. -/
theorem result_elements_drawn_from_input
    (numbers : RustSlice i64)
    (hlen : 2 ≤ numbers.val.size)
    (hfit : pairwise_diff_fits numbers) :
    ∃ a b : i64,
      clever_020_find_closest_elements.find_closest_elements numbers
        = RustM.ok (rust_primitives.hax.Tuple2.mk a b)
      ∧ ∃ (i j : Nat) (hi : i < numbers.val.size) (hj : j < numbers.val.size),
          i ≠ j ∧ (numbers.val[i]'hi) = a ∧ (numbers.val[j]'hj) = b := by
  sorry

/-- Postcondition 3 (minimum difference): the difference `b - a` of the
    returned pair is the minimum, over all distinct index pairs `(i, j)`,
    of `|numbers[i] - numbers[j]|`. Captures the proptest
    `result_difference_is_minimum`. -/
theorem result_difference_is_minimum
    (numbers : RustSlice i64)
    (hlen : 2 ≤ numbers.val.size)
    (hfit : pairwise_diff_fits numbers) :
    ∃ a b : i64,
      clever_020_find_closest_elements.find_closest_elements numbers
        = RustM.ok (rust_primitives.hax.Tuple2.mk a b)
      ∧ a.toInt ≤ b.toInt
      ∧ ∀ (i j : Nat) (hi : i < numbers.val.size) (hj : j < numbers.val.size),
          i ≠ j →
          b.toInt - a.toInt
            ≤ (((numbers.val[i]'hi).toInt - (numbers.val[j]'hj).toInt).natAbs : Int) := by
  sorry

end Clever_020_find_closest_elementsObligations
