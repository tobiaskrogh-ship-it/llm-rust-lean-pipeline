-- Companion obligations file for the `clever_061_derivative` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_061_derivative

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_061_derivativeObligations

/-! ## Obligations

Three independent contract clauses, one theorem each:

* `derivative_empty`            — boundary: empty input → empty output.
                                  Captures the `empty_and_constant` proptest
                                  (the `&[]` assertion). The `&[7]` (constant
                                  polynomial → empty) assertion is subsumed by
                                  `derivative_length` evaluated at `size = 1`.
* `derivative_length`           — closed-form length: `max(0, n - 1)`.
                                  Captures the `length_drops_by_one` proptest.
* `derivative_coefficient_formula` — elementwise contract: `result[k] = (k+1) * c[k+1]`.
                                  Captures the `coefficient_formula` proptest.

Preconditions on `derivative_length` and `derivative_coefficient_formula`:

* `hsize_fits : numbers.val.size ≤ 2^63` — ensures the partial cast
  `(i as i64)` is non-wrapping for every loop index `1 ≤ i < size`. For
  `size > 2^63` the cast wraps to negative, the multiplication can flip
  sign, and the elementwise formula stated against the raw Int product
  fails in the model. The proptest bound `0..12` is a (very) bounded slice
  of this honest domain; we state the maximal honest domain here.
* `hmul_fit` — per-element overflow bound: for every `1 ≤ i < size`,
  `(i : Int) * c[i].toInt` fits in i64. Without this, the `(i as i64) *? c[i]`
  in `build_at` panics (`integerOverflow`) and the function does not
  terminate with `RustM.ok _`. The proptest's `-100..=100` × small index
  values stay well inside this bound, but the universal Lean statement
  needs it as an assumption.

The precondition shape mirrors `sum_product`'s `hfit_prod` (per-element
overflow bound for `*?`) and `rescale_to_unit`'s pairwise-fit pattern
(per-pair bound for `-?`). -/

/-- Boundary case: when the input slice is empty, the function returns the
    empty `Vec`. Captures the `derivative(&[]) == Vec::new()` assertion of
    the `empty_and_constant` property test. -/
theorem derivative_empty
    (numbers : RustSlice i64) (hempty : numbers.val.size = 0) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_061_derivative.derivative numbers = RustM.ok v ∧
      v.val.size = 0 := by
  sorry

/-- Length postcondition: the output Vec has length `max(0, n - 1)`, where
    `n = numbers.val.size`. Captures the `length_drops_by_one` property
    test. -/
theorem derivative_length
    (numbers : RustSlice i64)
    (hsize_fits : numbers.val.size ≤ 2 ^ 63)
    (hmul_fit : ∀ (i : Nat) (h1 : 1 ≤ i) (h2 : i < numbers.val.size),
        -(2 ^ 63 : Int) ≤ (i : Int) * (numbers.val[i]'h2).toInt ∧
        (i : Int) * (numbers.val[i]'h2).toInt < 2 ^ 63) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_061_derivative.derivative numbers = RustM.ok v ∧
      v.val.size =
        (if numbers.val.size = 0 then 0 else numbers.val.size - 1) := by
  sorry

/-- Coefficient formula: for every index `k` of the output, the value
    equals `(k + 1) * c[k + 1]` (as `Int`s). Captures the
    `coefficient_formula` property test. -/
theorem derivative_coefficient_formula
    (numbers : RustSlice i64)
    (hsize_fits : numbers.val.size ≤ 2 ^ 63)
    (hmul_fit : ∀ (i : Nat) (h1 : 1 ≤ i) (h2 : i < numbers.val.size),
        -(2 ^ 63 : Int) ≤ (i : Int) * (numbers.val[i]'h2).toInt ∧
        (i : Int) * (numbers.val[i]'h2).toInt < 2 ^ 63) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_061_derivative.derivative numbers = RustM.ok v ∧
      ∀ (k : Nat) (hk_n : k + 1 < numbers.val.size) (hk_v : k < v.val.size),
        (v.val[k]'hk_v).toInt = (k + 1 : Int) * (numbers.val[k + 1]'hk_n).toInt := by
  sorry

end Clever_061_derivativeObligations
