-- Companion obligations file for the `clever_134_can_arrange` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_134_can_arrange

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_134_can_arrangeObligations

/-! ## Helper predicate. -/

/-- The slice has no descending adjacent pair (i.e., it is non-decreasing
    in the `arr[j] ≤ arr[j+1]` sense). -/
private def is_nondec (arr : RustSlice i64) : Prop :=
  ∀ j : Nat, ∀ (hj1 : j + 1 < arr.val.size),
    arr.val[j]'(Nat.lt_of_succ_lt hj1) ≤ arr.val[j+1]'hj1

/-! ## Theorem obligations. -/

/-- Claim 1 (witness): when the result is not `-1`, it encodes a valid index
    `k + 1 ∈ [1, arr.size)` at which the slice descends (`arr[k+1] < arr[k]`).

    Captures the proptest `result_is_a_descending_position`: `r ≥ 1`,
    `(r as usize) < arr.len()`, and `arr[r] < arr[r-1]`. The precondition
    `arr.val.size < 2^63` ensures the `i as i64` cast performed inside
    `scan_at` faithfully encodes the recursion index as a non-negative
    `i64`, so the returned `r` actually corresponds to a usize index. -/
theorem result_is_descending_position
    (arr : RustSlice i64) (r : i64)
    (h_size : arr.val.size < 2^63)
    (h_res : clever_134_can_arrange.can_arrange arr = RustM.ok r)
    (h_ne : r ≠ (-1 : i64)) :
    ∃ k : Nat, ∃ (hk1 : k + 1 < arr.val.size),
      r.toInt = ((k : Int) + 1) ∧
      arr.val[k+1]'hk1 < arr.val[k]'(Nat.lt_of_succ_lt hk1) := by
  sorry

/-- Claim 2 (maximality): when the result is not `-1`, no descending adjacent
    pair exists strictly past the encoded index. Equivalently, the suffix
    starting at index `r.toInt.toNat + 1` is non-decreasing.

    Captures the proptest `result_is_the_largest_descending_position`:
    `for j in (r+1)..arr.len() { prop_assert!(arr[j] >= arr[j-1]) }`, which
    in pair-by-first-index form is `∀ k ≥ r, arr[k] ≤ arr[k+1]`. -/
theorem result_is_largest_descending_position
    (arr : RustSlice i64) (r : i64)
    (h_size : arr.val.size < 2^63)
    (h_res : clever_134_can_arrange.can_arrange arr = RustM.ok r)
    (h_ne : r ≠ (-1 : i64)) :
    ∀ k : Nat, r.toInt.toNat ≤ k → ∀ (hk1 : k + 1 < arr.val.size),
      arr.val[k]'(Nat.lt_of_succ_lt hk1) ≤ arr.val[k+1]'hk1 := by
  sorry

/-- Claim 3a (sentinel completeness): a non-decreasing slice returns `-1`.

    Captures the forward direction of `minus_one_iff_non_decreasing`:
    when every adjacent pair satisfies `arr[j] ≥ arr[j-1]`, `scan_at`
    never updates `best`, so the returned sentinel is the initial `-1`.
    No size precondition is needed: the only path where `best` could
    change is taken zero times. -/
theorem non_decreasing_returns_minus_one
    (arr : RustSlice i64) (h_nondec : is_nondec arr) :
    clever_134_can_arrange.can_arrange arr = RustM.ok (-1 : i64) := by
  sorry

/-- Claim 3b (sentinel soundness): returning `-1` implies the slice is
    non-decreasing.

    Captures the backward direction of `minus_one_iff_non_decreasing`.
    No size precondition is needed: because `arr.val.size < 2^64`, every
    in-scope index `i` satisfies `i < 2^64 - 1`, so the cast `i as i64`
    never produces `-1`. Hence the result equals `-1` only if `best` was
    never updated, which forces every adjacent pair to be non-descending. -/
theorem minus_one_implies_non_decreasing
    (arr : RustSlice i64)
    (h_res : clever_134_can_arrange.can_arrange arr = RustM.ok (-1 : i64)) :
    is_nondec arr := by
  sorry

end Clever_134_can_arrangeObligations
