-- Companion obligations file for the `clever_004_mean_absolute_deviation` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_004_mean_absolute_deviation

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_004_mean_absolute_deviationObligations

/-! ## Integer-valued oracles

The function under verification computes the mean absolute deviation
`MAD(xs) = (Σ |x_i - mean|) / n` with `mean = (Σ x_i) / n` using `i64`
arithmetic that truncates toward zero. The oracles below specify the
intended values in `Int`, where overflow cannot occur — overflow shows
up as a precondition on the obligation rather than a hidden assumption
in the spec.

Lean's `(/)` on `Int` is `Int.div`, which truncates toward zero, matching
Rust's `i64 /` semantics. -/

/-- Integer-valued prefix sum:
    `prefix_sum_int numbers k = Σ_{j<k} numbers[j].toInt`.

    The `dite` keeps the function total — every theorem below quantifies
    `k ≤ numbers.val.size`, keeping the index in range. -/
private def prefix_sum_int (numbers : RustSlice i64) : Nat → Int
  | 0     => 0
  | k + 1 =>
      prefix_sum_int numbers k +
        (if h : k < numbers.val.size then (numbers.val[k]'h).toInt else 0)

/-- Int-valued mean: `total_sum / n` using Rust-matching T-division.
    On the empty slice this is `0 / 0 = 0` (Lean's convention for
    division by zero), and the function's empty-input path never
    consults `mean_int` anyway. -/
private def mean_int (numbers : RustSlice i64) : Int :=
  prefix_sum_int numbers numbers.val.size / (numbers.val.size : Int)

/-- Integer-valued prefix sum of absolute deviations from `mean`:
    `prefix_abs_dev_sum_int numbers mean k = Σ_{j<k} |numbers[j].toInt - mean|`.

    The `(·.natAbs : Int)` casts the `Nat` absolute value back to `Int`
    so it can be summed alongside the running `Int` accumulator. -/
private def prefix_abs_dev_sum_int (numbers : RustSlice i64) (mean : Int) : Nat → Int
  | 0     => 0
  | k + 1 =>
      prefix_abs_dev_sum_int numbers mean k +
        (if h : k < numbers.val.size then
           (((numbers.val[k]'h).toInt - mean).natAbs : Int)
         else 0)

/-! ## Obligations -/

/-- Empty-slice boundary contract.

    Captures the property test `empty_returns_zero`:
    `mean_absolute_deviation(&[]) == 0`. The empty case is the
    short-circuit branch (`n == 0`) of the function and returns `0` with
    no further computation, so the obligation is purely equational. -/
theorem empty_returns_zero
    (numbers : RustSlice i64) (hempty : numbers.val.size = 0) :
    clever_004_mean_absolute_deviation.mean_absolute_deviation numbers
      = RustM.ok (0 : i64) := by
  sorry

/-- Main correctness postcondition.

    Captures the property test `matches_reference_formula`: under
    no-overflow preconditions, the result equals the closed-form MAD
    computed in `Int`:
        `(Σ |x_i - ⌊(Σ x_j) / n⌋|) / n`.

    Preconditions:
    * `hsize_fits`     — `n = numbers.len() as i64` is positive, i.e.
      `numbers.val.size < 2^63`. Without this the unsigned-to-signed
      cast wraps and the top-level zero-check / division behave
      differently from the closed form.
    * `hsum_fit`       — every intermediate suffix sum produced by
      `sum_from` (equivalently `total − prefix(i)`) fits in `i64`,
      keeping `numbers[i] + sum_from(numbers, i+1)` overflow-free at
      every recursive step.
    * `hdev_bounded`   — each per-element deviation `numbers[i] - mean`
      fits in `(-2^63, 2^63)`. The strict lower bound covers both the
      subtraction `numbers[i] - mean` and the unary negation `-d`
      taken when `d < 0` (which would overflow exactly at `d = i64::MIN`).
    * `habs_sum_fit`   — every intermediate suffix sum produced by
      `abs_dev_sum_from` fits in `i64`. -/
theorem mad_matches_formula
    (numbers : RustSlice i64)
    (hsize_fits : (numbers.val.size : Int) < 2^63)
    (hsum_fit : ∀ i, i ≤ numbers.val.size →
        -(2^63 : Int) ≤
            prefix_sum_int numbers numbers.val.size - prefix_sum_int numbers i ∧
        prefix_sum_int numbers numbers.val.size - prefix_sum_int numbers i
          < 2^63)
    (hdev_bounded : ∀ (k : Nat) (h : k < numbers.val.size),
        (((numbers.val[k]'h).toInt - mean_int numbers).natAbs : Int) < 2^63)
    (habs_sum_fit : ∀ i, i ≤ numbers.val.size →
        -(2^63 : Int) ≤
            prefix_abs_dev_sum_int numbers (mean_int numbers) numbers.val.size
              - prefix_abs_dev_sum_int numbers (mean_int numbers) i ∧
        prefix_abs_dev_sum_int numbers (mean_int numbers) numbers.val.size
              - prefix_abs_dev_sum_int numbers (mean_int numbers) i
            < 2^63) :
    ∃ r : i64,
      clever_004_mean_absolute_deviation.mean_absolute_deviation numbers
        = RustM.ok r ∧
      r.toInt =
        (prefix_abs_dev_sum_int numbers (mean_int numbers) numbers.val.size)
          / (numbers.val.size : Int) := by
  sorry

/-- Non-negativity of the result.

    Captures the property test `result_is_non_negative`: a mean absolute
    deviation is an average of absolute values, hence ≥ 0 by definition.
    Stated separately because — per the Rust comment on the test — it is
    a basic correctness property every implementation must satisfy, not
    just a derived fact of one particular implementation choice.

    Same preconditions as `mad_matches_formula` so the function actually
    returns successfully; the empty case is covered vacuously since the
    impl returns `0` and `0 ≤ 0`. -/
theorem mad_non_negative
    (numbers : RustSlice i64)
    (hsize_fits : (numbers.val.size : Int) < 2^63)
    (hsum_fit : ∀ i, i ≤ numbers.val.size →
        -(2^63 : Int) ≤
            prefix_sum_int numbers numbers.val.size - prefix_sum_int numbers i ∧
        prefix_sum_int numbers numbers.val.size - prefix_sum_int numbers i
          < 2^63)
    (hdev_bounded : ∀ (k : Nat) (h : k < numbers.val.size),
        (((numbers.val[k]'h).toInt - mean_int numbers).natAbs : Int) < 2^63)
    (habs_sum_fit : ∀ i, i ≤ numbers.val.size →
        -(2^63 : Int) ≤
            prefix_abs_dev_sum_int numbers (mean_int numbers) numbers.val.size
              - prefix_abs_dev_sum_int numbers (mean_int numbers) i ∧
        prefix_abs_dev_sum_int numbers (mean_int numbers) numbers.val.size
              - prefix_abs_dev_sum_int numbers (mean_int numbers) i
            < 2^63) :
    ∃ r : i64,
      clever_004_mean_absolute_deviation.mean_absolute_deviation numbers
        = RustM.ok r ∧
      0 ≤ r.toInt := by
  sorry

end Clever_004_mean_absolute_deviationObligations
