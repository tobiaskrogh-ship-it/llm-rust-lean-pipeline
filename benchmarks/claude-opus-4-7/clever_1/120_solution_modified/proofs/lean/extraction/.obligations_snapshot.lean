-- Companion obligations file for the `clever_120_solution` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_120_solution

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_120_solutionObligations

/-! ## Integer-valued specification

The Rust source `solution(lst)` returns the sum of `lst[i]` over indices
`i` such that `i` is even AND `lst[i]` is odd.  We mirror this at the
`Int` level via a primitive-recursive prefix oracle so the spec side
cannot overflow on any input the Lean model permits.

The Rust test `reference` is
  `lst.iter().enumerate().filter(|(i,v)| i%2==0 && **v%2!=0).map(|(_,v)| *v).sum()`,
which is exactly `cond_sum_int lst lst.val.size` below. -/

/-- Integer-valued conditional prefix sum:
    `cond_sum_int lst k = Σ_{j<k, j%2=0, (lst.val[j]).toInt%2≠0} (lst.val[j]).toInt`.

    The outer `dite` keeps the function total — every theorem below
    quantifies `k` with `k ≤ lst.val.size`, so the index stays in
    range. -/
private def cond_sum_int (lst : RustSlice i64) : Nat → Int
  | 0     => 0
  | k + 1 =>
      cond_sum_int lst k +
        (if h : k < lst.val.size then
           (if k % 2 = 0 ∧ (lst.val[k]'h).toInt % 2 ≠ 0
            then (lst.val[k]'h).toInt
            else 0)
         else 0)

/-! ## Top-level theorems. -/

/-- Boundary clause (from Rust test `empty_is_zero`): the empty slice
    yields `0`. -/
theorem empty_returns_zero
    (lst : RustSlice i64) (hempty : lst.val.size = 0) :
    clever_120_solution.solution lst = RustM.ok (0 : i64) := by
  sorry

/-- Main postcondition (from Rust test `matches_reference`): under a
    no-overflow precondition on every prefix of the conditional sum,
    `solution lst` succeeds and its result equals the `Int`-valued spec
    `cond_sum_int` evaluated at the full slice length.

    The `hfit` hypothesis states that every running accumulator value
    `cond_sum_int lst k` (for `0 ≤ k ≤ lst.val.size`) fits in `i64`.
    This is the natural Lean generalisation of the proptest's bounded
    element range (`-1_000_000..1_000_000` × length `0..64` keeps every
    running sum well below `2^63`); the universal claim without `hfit`
    is false in the model because for sufficiently large i64-valued
    inputs the `+?` step can overflow and the function fails. -/
theorem matches_spec
    (lst : RustSlice i64)
    (hfit : ∀ k : Nat, k ≤ lst.val.size →
              -(2^63 : Int) ≤ cond_sum_int lst k ∧ cond_sum_int lst k < 2^63) :
    ∃ r : i64,
      clever_120_solution.solution lst = RustM.ok r ∧
      r.toInt = cond_sum_int lst lst.val.size := by
  sorry

/-- Independence clause (from Rust test `ignores_odd_indices`): the
    result depends only on the values at even indices.  Two slices of
    equal length that agree at every even index produce the same result
    (assuming both satisfy the no-overflow precondition).

    The Rust proptest explicitly treats this as an orthogonal claim
    distinct from `matches_reference`: even though it follows from the
    spec (because `cond_sum_int` only consults entries at even indices),
    pinning it down separately rules out the possibility of the function
    accidentally agreeing with the reference on the proptest's bounded
    domain while still depending on odd-indexed values. -/
theorem ignores_odd_indices
    (lst lst' : RustSlice i64)
    (h_size : lst.val.size = lst'.val.size)
    (h_even : ∀ (k : Nat) (h : k < lst.val.size) (h' : k < lst'.val.size),
                k % 2 = 0 → (lst.val[k]'h) = (lst'.val[k]'h'))
    (hfit  : ∀ k : Nat, k ≤ lst.val.size →
              -(2^63 : Int) ≤ cond_sum_int lst  k ∧ cond_sum_int lst  k < 2^63)
    (hfit' : ∀ k : Nat, k ≤ lst'.val.size →
              -(2^63 : Int) ≤ cond_sum_int lst' k ∧ cond_sum_int lst' k < 2^63) :
    ∃ r : i64,
      clever_120_solution.solution lst  = RustM.ok r ∧
      clever_120_solution.solution lst' = RustM.ok r := by
  sorry

end Clever_120_solutionObligations
