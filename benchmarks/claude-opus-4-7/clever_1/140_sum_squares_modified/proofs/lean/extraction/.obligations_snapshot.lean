-- Companion obligations file for the `clever_140_sum_squares` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_140_sum_squares

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_140_sum_squaresObligations

/-! ## Integer-valued specification

The Rust source documents `sum_squares(lst)` as the elementwise sum after
applying an index-dependent transform: at index `i` with element `v`,
`v*v` if `i % 3 == 0`; otherwise `v*v*v` if `i % 4 == 0`; otherwise `v`.
We mirror this at the `Int` level so the spec side cannot overflow on any
input the Lean model permits.  Overflow shows up as a precondition on the
matches_spec obligation rather than a hidden assumption in the spec. -/

/-- Per-element transform on `Int`.  Mirrors the Rust
    `if i % 3 == 0 { v*v } else if i % 4 == 0 { v*v*v } else { v }`. -/
private def transform (v : Int) (i : Nat) : Int :=
  if i % 3 = 0 then v * v
  else if i % 4 = 0 then v * v * v
  else v

/-- Integer-valued prefix sum of the transformed elements:
    `transform_sum_int l k = Σ_{j<k} transform (l.val[j]).toInt j`.

    The `dite` on `k < l.val.size` makes the definition total — every
    theorem below quantifies `k` so that `k ≤ l.val.size`, keeping the
    index in range. -/
private def transform_sum_int (l : RustSlice i64) : Nat → Int
  | 0     => 0
  | k + 1 =>
      transform_sum_int l k +
        (if h : k < l.val.size then
          transform (l.val[k]'h).toInt k
        else 0)

/-! ## Top-level theorems

The Rust `#[test] fn known` asserts three pointwise values:
  `sum_squares(&[1,2,3,4,5,6,7,8]) = 210`, `sum_squares(&[]) = 0`,
  `sum_squares(&[5]) = 25`.
The first and third are concrete instances subsumed by the general
`matches_spec` postcondition below.  The empty case is a meaningful
boundary contract — it pins down the seed accumulator `0`, which the
general postcondition would otherwise need its full prefix-sum
machinery to discharge — and gets its own theorem.

The proptest `matches_spec` asserts the general functional-correctness
property and becomes the `matches_spec` theorem. -/

/-- Empty-slice boundary contract.

    Captures the `known` test assertion `sum_squares(&[]) == 0`.
    Pins down the seed accumulator: without this, the general
    postcondition below would hold for any choice of initial accumulator. -/
theorem empty_returns_zero (lst : RustSlice i64) (hempty : lst.val.size = 0) :
    clever_140_sum_squares.sum_squares lst = RustM.ok (0 : i64) := by
  sorry

/-- General functional-correctness postcondition.

    Captures the proptest `matches_spec`: under no-overflow preconditions,
    the result equals the integer-valued sum of transformed elements.

    Feasibility / preconditions.  The natural universal statement is false
    in the Lean model: a `RustSlice i64` can hold any `i64` values with
    arbitrary `size < 2^64`, so

    * the per-element transform `v*v` (square case) or `(v*v)*v` (cube
      case) can overflow on a single large element, and
    * the running accumulator `acc +? term` can overflow even when each
      term individually fits.

    The proptest's `(-1000..=1000, 0..20)` bounds keep both quantities
    well inside `i64` (per-element |v*v*v| ≤ 10^9, total |sum| ≤ 2·10^10);
    the corresponding hypotheses here are:

    * `hfit_elem`: every per-element transform fits in `i64`.  This is
      *not* derivable from the prefix-sum bound: the cube case can produce
      values like 10^25 that violate `i64` even when neighbouring prefix
      sums cancel to something small.  For the square case it implies the
      single multiplication doesn't overflow; for the cube case it
      implies *both* the intermediate `v*v` and the final `(v*v)*v` fit
      (if `|v*v*v| < 2^63` then `|v| < 2^21`, hence `|v*v| < 2^42 < 2^63`);
      for the passthrough else-arm it is trivially satisfied.
    * `hfit_sum`: every prefix sum fits in `i64`.  Bounds the running
      accumulator addition. -/
theorem matches_spec (lst : RustSlice i64)
    (hfit_elem : ∀ (k : Nat) (h : k < lst.val.size),
                   -(2^63 : Int) ≤ transform (lst.val[k]'h).toInt k ∧
                   transform (lst.val[k]'h).toInt k < 2^63)
    (hfit_sum : ∀ k : Nat, k ≤ lst.val.size →
                  -(2^63 : Int) ≤ transform_sum_int lst k ∧
                  transform_sum_int lst k < 2^63) :
    ∃ r : i64,
      clever_140_sum_squares.sum_squares lst = RustM.ok r ∧
      r.toInt = transform_sum_int lst lst.val.size := by
  sorry

end Clever_140_sum_squaresObligations
