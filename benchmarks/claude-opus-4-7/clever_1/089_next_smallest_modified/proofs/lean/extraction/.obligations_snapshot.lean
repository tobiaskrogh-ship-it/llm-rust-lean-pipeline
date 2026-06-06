-- Companion obligations file for the `clever_089_next_smallest` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_089_next_smallest

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_089_next_smallestObligations

/-! ## Contract obligations for `next_smallest`.

The Rust function `next_smallest(lst)` returns the second-smallest *unique*
element of `lst` (i.e. the smallest value strictly greater than `min(lst)`),
or `None` if no such element exists (empty list, single element, or all
values equal).

The Rust property tests in `src/lib.rs` express six contract clauses, each
captured here as a separate `theorem`. Proofs are deferred to a later
pipeline stage (`sorry` placeholders).

All statements are universal: the proptests' `-50..=50` and `0..12` bounds
are just bounded sampling; the function is total on every `RustSlice i64`
(the recursive helpers' `i +? 1` increment is safe because `i ≤ l.val.size`
and `l.val.size < USize64.size = 2^64`), and the contract clauses are
true at the model's edges. -/

/-- Failure / None clause (test `empty_is_none`):
    when the input slice is empty, the result is `None`. -/
theorem empty_returns_none
    (l : RustSlice i64)
    (hempty : l.val.size = 0) :
    clever_089_next_smallest.next_smallest l
      = RustM.ok core_models.option.Option.None := by
  sorry

/-- Failure / None clause (proptest `all_equal_is_none`):
    when every element of `l` is the same value, the result is `None`
    (there's no element strictly above the minimum). -/
theorem all_equal_returns_none
    (l : RustSlice i64) (x : i64)
    (h_size_pos : 0 < l.val.size)
    (h_all : ∀ (i : Nat) (hi : i < l.val.size), (l.val[i]'hi) = x) :
    clever_089_next_smallest.next_smallest l
      = RustM.ok core_models.option.Option.None := by
  sorry

/-- Converse / None-implies clause (proptest `none_implies_fewer_than_two_unique`):
    if the result is `None`, then `l` contains fewer than two distinct values
    (i.e. every pair of elements is equal). -/
theorem none_implies_fewer_than_two_unique
    (l : RustSlice i64)
    (h_res : clever_089_next_smallest.next_smallest l
              = RustM.ok core_models.option.Option.None) :
    ∀ (i j : Nat) (hi : i < l.val.size) (hj : j < l.val.size),
      (l.val[i]'hi) = (l.val[j]'hj) := by
  sorry

/-- Success / membership clause (proptest `some_result_is_in_list`):
    when the result is `Some x`, then `x` appears at some index of `l`. -/
theorem some_result_is_in_list
    (l : RustSlice i64) (x : i64)
    (h_res : clever_089_next_smallest.next_smallest l
              = RustM.ok (core_models.option.Option.Some x)) :
    ∃ (i : Nat) (hi : i < l.val.size), (l.val[i]'hi) = x := by
  sorry

/-- Success / not-minimum clause (proptest `some_result_exceeds_some_element`):
    when the result is `Some x`, some element of `l` is strictly less than `x`
    (i.e. `x` is not the overall minimum). -/
theorem some_result_exceeds_some_element
    (l : RustSlice i64) (x : i64)
    (h_res : clever_089_next_smallest.next_smallest l
              = RustM.ok (core_models.option.Option.Some x)) :
    ∃ (i : Nat) (hi : i < l.val.size), (l.val[i]'hi).toInt < x.toInt := by
  sorry

/-- Success / next-smallest clause (proptest
    `nothing_strictly_between_min_and_result`):
    when the result is `Some x`, no element of `l` lies strictly between
    a minimum of `l` and `x`. Stated for any `i` whose value is a minimum
    of the slice (`l[i] ≤ l[k]` for all `k`): no other element `l[j]`
    satisfies `l[i] < l[j] < x`. -/
theorem nothing_strictly_between_min_and_result
    (l : RustSlice i64) (x : i64)
    (h_res : clever_089_next_smallest.next_smallest l
              = RustM.ok (core_models.option.Option.Some x)) :
    ∀ (i j : Nat) (hi : i < l.val.size) (hj : j < l.val.size),
      (∀ (k : Nat) (hk : k < l.val.size),
          (l.val[i]'hi).toInt ≤ (l.val[k]'hk).toInt) →
      (l.val[i]'hi).toInt < (l.val[j]'hj).toInt →
      x.toInt ≤ (l.val[j]'hj).toInt := by
  sorry

end Clever_089_next_smallestObligations
