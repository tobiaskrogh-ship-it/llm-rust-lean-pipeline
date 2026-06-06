-- Companion obligations file for the `clever_084_solve` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_084_solve

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_084_solveObligations

/-! ## Integer-valued specification

The Rust source `solve(n)` returns the sum of `n[i]` over indices `i` such
that `i` is odd and `n[i]` is even.  We mirror this at the `Int` level via
a primitive-recursive prefix oracle, so the spec side cannot overflow on
any input the Lean model permits.

The Rust test `naive` is `n.iter().enumerate().filter(|(i,v)| i%2==1 && *v%2==0).map(|(_,v)| *v).sum()`,
which is exactly `cond_sum_int n n.val.size` below. -/

/-- Integer-valued conditional prefix sum:
    `cond_sum_int n k = Σ_{j<k, j%2=1, n[j].toInt%2=0} (n.val[j]).toInt`.

    The outer `dite` keeps the function total — every theorem below
    quantifies `k` with `k ≤ n.val.size`, so the index stays in range. -/
private def cond_sum_int (n : RustSlice i64) : Nat → Int
  | 0     => 0
  | k + 1 =>
      cond_sum_int n k +
        (if h : k < n.val.size then
           (if k % 2 = 1 ∧ (n.val[k]'h).toInt % 2 = 0
            then (n.val[k]'h).toInt
            else 0)
         else 0)

/-! ## Top-level theorems

Each obligation captures one contract clause from the Rust property tests:

  * `empty_returns_zero` — proptest `empty_returns_zero`
    (boundary: `solve(&[]) == 0`).
  * `singleton_returns_zero` — proptest `singleton_returns_zero`
    (boundary: a one-element list has no odd index, so the result is `0`
    regardless of the element).
  * `matches_spec` — proptest `matches_spec`
    (main postcondition: the result equals the naive `Int`-valued spec,
    under a no-overflow precondition on every running conditional sum).

The unit test `known_examples` checks three concrete values; each is a
specialisation of `matches_spec` at a specific input and is therefore
classified as a derived fact (skipped per the obligations guidelines). -/

/-- Boundary clause: an empty slice yields `0`. -/
theorem empty_returns_zero
    (n : RustSlice i64) (hempty : n.val.size = 0) :
    clever_084_solve.solve n = RustM.ok (0 : i64) := by
  sorry

/-- Boundary clause: a one-element slice yields `0` regardless of the
    element's value, since index `0` is even (not odd). -/
theorem singleton_returns_zero
    (n : RustSlice i64) (hsingleton : n.val.size = 1) :
    clever_084_solve.solve n = RustM.ok (0 : i64) := by
  sorry

/-- Main postcondition: under a no-overflow precondition on every prefix
    of the conditional sum, `solve n` succeeds and its result equals the
    `Int`-valued spec `cond_sum_int` evaluated at the full slice length.

    The `hfit` hypothesis states that every running accumulator value
    `cond_sum_int n k` (for `0 ≤ k ≤ n.val.size`) fits in `i64`.  This is
    the natural Lean generalisation of the proptest's bounded element
    range (`-1000..=1000` × length `0..32` keeps every running sum well
    below `2^63`); the universal claim without `hfit` is false in the
    model because for sufficiently large i64-valued inputs the `+?` step
    can overflow and the function fails. -/
theorem matches_spec
    (n : RustSlice i64)
    (hfit : ∀ k : Nat, k ≤ n.val.size →
              -(2^63 : Int) ≤ cond_sum_int n k ∧ cond_sum_int n k < 2^63) :
    ∃ r : i64,
      clever_084_solve.solve n = RustM.ok r ∧
      r.toInt = cond_sum_int n n.val.size := by
  sorry

end Clever_084_solveObligations
