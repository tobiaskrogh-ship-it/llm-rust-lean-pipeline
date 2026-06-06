-- Companion obligations file for the `clever_113_minSubArraySum` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_113_minSubArraySum

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_113_minSubArraySumObligations

/-! ## Specification oracle: integer-valued prefix sums.

The sum of the contiguous subarray `nums[a..b]` (zero-based half-open,
`a < b`) is `prefix_sum_int nums b - prefix_sum_int nums a`. We work in
`Int` so the spec itself never overflows; obligations whose conclusion
talks about the result already condition on `minSubArraySum nums =
RustM.ok r`, which carries the no-overflow side condition implicitly.

The `dite` keeps the definition total; every theorem below quantifies the
index so that it stays `≤ nums.val.size`, keeping `k < size` in scope
wherever the index actually matters. -/

private def prefix_sum_int (nums : RustSlice i64) : Nat → Int
  | 0     => 0
  | k + 1 =>
      prefix_sum_int nums k +
        (if h : k < nums.val.size then (nums.val[k]'h).toInt else 0)

/-! ## Top-level contract obligations. -/

/-- Boundary clause: on the empty slice the sentinel `0` is returned.
    Captures the property test `empty_input_returns_zero`. -/
theorem empty_returns_zero (nums : RustSlice i64) (hempty : nums.val.size = 0) :
    clever_113_minSubArraySum.minSubArraySum nums = RustM.ok (0 : i64) := by
  sorry

/-- Boundary clause: on a length-1 slice the sole element is returned.
    Captures the property test `singleton_returns_element`. -/
theorem singleton_returns_element (nums : RustSlice i64)
    (hsingle : nums.val.size = 1) :
    clever_113_minSubArraySum.minSubArraySum nums
      = RustM.ok (nums.val[0]'(by omega)) := by
  sorry

/-- Achievability postcondition: the returned value is the integer sum of
    some non-empty contiguous subarray `nums[a..b]` with `a < b ≤ size`.
    Captures the property test `result_is_achieved_by_some_subarray`. -/
theorem result_is_achieved_by_some_subarray
    (nums : RustSlice i64) (r : i64)
    (hnonempty : 0 < nums.val.size)
    (h : clever_113_minSubArraySum.minSubArraySum nums = RustM.ok r) :
    ∃ a b : Nat, a < b ∧ b ≤ nums.val.size ∧
      r.toInt = prefix_sum_int nums b - prefix_sum_int nums a := by
  sorry

/-- Minimality postcondition: the returned value is a lower bound on every
    non-empty contiguous-subarray sum `nums[a..b]` with `a < b ≤ size`.
    Captures the property test `result_lower_bounds_all_subarrays`.

    Note: on the empty slice (`size = 0`), the universal premise `a < b ≤ 0`
    is unsatisfiable, so the statement is vacuously true — consistent with
    the empty-returns-0 boundary clause. -/
theorem result_lower_bounds_all_subarrays
    (nums : RustSlice i64) (r : i64)
    (h : clever_113_minSubArraySum.minSubArraySum nums = RustM.ok r) :
    ∀ a b : Nat, a < b → b ≤ nums.val.size →
      r.toInt ≤ prefix_sum_int nums b - prefix_sum_int nums a := by
  sorry

end Clever_113_minSubArraySumObligations
