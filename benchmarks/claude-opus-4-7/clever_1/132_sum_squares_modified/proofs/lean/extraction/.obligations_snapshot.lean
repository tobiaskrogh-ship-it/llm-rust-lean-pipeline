-- Companion obligations file for the `clever_132_sum_squares` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_132_sum_squares

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_132_sum_squaresObligations

/-! ## Integer-valued specification of the sum of squares

The Rust source documents `sum_squares(lst)` as returning the sum of
squares of the elements of `lst`. We compute the spec in `Int` (matching
the proptest's `i64`-iterator sum on bounded inputs) so the specification
itself cannot overflow on any input the function under verification can
legally accept; overflow shows up as a precondition on the obligation
rather than a hidden assumption in the spec. -/

/-- Integer-valued prefix sum of squares:
    `sum_squares_int xs k = Σ_{j<k} ((xs.val[j]).toInt)^2`.

    The `dite` on `k < l.val.size` makes the definition total — every
    theorem below quantifies `k` so that `k ≤ l.val.size`, keeping the
    index in range. -/
private def sum_squares_int (l : RustSlice i64) : Nat → Int
  | 0     => 0
  | k + 1 =>
      sum_squares_int l k +
        (if h : k < l.val.size then
          (l.val[k]'h).toInt * (l.val[k]'h).toInt
        else 0)

/-! ## Top-level theorems

The Rust `#[test] fn known` asserts three pointwise values:
  `sum_squares(&[1,2,3]) = 14`, `sum_squares(&[]) = 0`,
  `sum_squares(&[-1,-2,-3]) = 14`.
The first and third are concrete instances subsumed by the general
`result_matches_sum_of_squares` postcondition below (the integer-valued
spec assigns 14 to both via `1+4+9`). The empty case is a meaningful
boundary contract — it pins down the seed accumulator `0`, which the
recursive postcondition would otherwise vacuously hold for any seed —
and gets its own theorem.

The proptest `matches` asserts the general functional-correctness
property and becomes `result_matches_sum_of_squares`. -/

/-- Empty-slice boundary contract.

    Captures the `known` test assertion `sum_squares(&[]) == 0`.
    Pins down the seed accumulator: without this, the general postcondition
    below would hold for any choice of initial accumulator. -/
theorem empty_returns_zero (lst : RustSlice i64) (hempty : lst.val.size = 0) :
    clever_132_sum_squares.sum_squares lst = RustM.ok (0 : i64) := by
  sorry

/-- General functional-correctness postcondition.

    Captures the proptest `matches`: under no-overflow preconditions, the
    result equals the integer-valued sum of squared elements.

    Feasibility / precondition. The natural universal statement is false
    in the Lean model: a `RustSlice i64` can hold any `i64` values with
    arbitrary `size < 2^64`, so both `l[i] * l[i]` (signed-mul on an
    `i64::MIN`-ish element) and the running `acc + l[i]^2` (sum of many
    large squares) can overflow. The proptest's `(-1000..=1000, 0..20)`
    bounds keep the sum under `2 · 10^7`, well inside `i64`; the
    corresponding hypothesis here is that every prefix sum of squares
    fits in `i64`. Because each squared term is non-negative, this single
    bound implies every individual `(l[i]).toInt * (l[i]).toInt < 2^63`
    too (the per-element multiplication overflow is dominated by the
    prefix bound at `k+1`). -/
theorem result_matches_sum_of_squares (lst : RustSlice i64)
    (hfit : ∀ k : Nat, k ≤ lst.val.size →
              -(2^63 : Int) ≤ sum_squares_int lst k
              ∧ sum_squares_int lst k < 2^63) :
    ∃ r : i64,
      clever_132_sum_squares.sum_squares lst = RustM.ok r ∧
      r.toInt = sum_squares_int lst lst.val.size := by
  sorry

end Clever_132_sum_squaresObligations
