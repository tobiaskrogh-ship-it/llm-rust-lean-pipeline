-- Companion obligations file for the `clever_149_double_the_difference` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_149_double_the_difference

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_149_double_the_differenceObligations

/-! ## Integer-valued specification

The Rust source `double_the_difference(numbers)` returns the sum of
squares of the positive odd integers in `numbers` (negative values and
even values are ignored).  We mirror this at the `Int` level via a
primitive-recursive prefix-sum oracle so the specification itself
cannot overflow on any input the Lean model permits; overflow shows
up as a precondition on the obligation rather than a hidden
assumption in the spec.

The Rust proptests check:
  * non-positive elements contribute nothing
    (`singleton_non_positive` — the `> 0` guard),
  * even elements contribute nothing
    (`singleton_even` — the `% 2 == 1` guard),
  * positive odd elements contribute their square
    (`singleton_positive_odd` — the take-arm arithmetic),
  * the function is additive over list concatenation
    (`additive_over_concat`, classified below as a derived fact).
-/

/-- Integer-valued prefix sum of squares of positive-odd elements:
    `dtd_int l k = Σ_{j<k, l[j].toInt>0, l[j].toInt%2=1} (l.val[j]).toInt * (l.val[j]).toInt`.

    The outer `dite` keeps the function total — every theorem below
    quantifies `k` with `k ≤ l.val.size`, so the index stays in
    range. -/
private def dtd_int (l : RustSlice i64) : Nat → Int
  | 0     => 0
  | k + 1 =>
      dtd_int l k +
        (if h : k < l.val.size then
           (if 0 < (l.val[k]'h).toInt ∧ (l.val[k]'h).toInt % 2 = 1
            then (l.val[k]'h).toInt * (l.val[k]'h).toInt
            else 0)
         else 0)

/-! ## Top-level theorems. -/

/-- Empty-slice boundary contract.

    Captures the `known` test assertion `double_the_difference(&[]) == 0`.
    Pins down the seed accumulator: without this, the general
    `matches_spec` postcondition below would hold for any choice of
    initial accumulator. -/
theorem empty_returns_zero
    (numbers : RustSlice i64) (hempty : numbers.val.size = 0) :
    clever_149_double_the_difference.double_the_difference numbers
      = RustM.ok (0 : i64) := by
  sorry

/-- Singleton positivity-fail clause: a singleton whose only element is
    non-positive returns `0`.

    Captures the proptest `singleton_non_positive` — verifies the
    `l[i] > 0` guard is present and effective.  No precondition is
    needed because the function never performs arithmetic on the
    element on this branch. -/
theorem singleton_non_positive_returns_zero
    (numbers : RustSlice i64) (n : i64)
    (h_size : numbers.val.size = 1)
    (h_first : ∀ (h : 0 < numbers.val.size), numbers.val[0]'h = n)
    (h_nonpos : n.toInt ≤ 0) :
    clever_149_double_the_difference.double_the_difference numbers
      = RustM.ok (0 : i64) := by
  sorry

/-- Singleton parity-fail clause: a singleton whose only element is
    even returns `0`, regardless of sign.

    Captures the proptest `singleton_even` — verifies the
    `l[i] % 2 == 1` guard is present and effective.  No precondition
    is needed because the function never performs arithmetic on the
    element on this branch. -/
theorem singleton_even_returns_zero
    (numbers : RustSlice i64) (n : i64)
    (h_size : numbers.val.size = 1)
    (h_first : ∀ (h : 0 < numbers.val.size), numbers.val[0]'h = n)
    (h_even : n.toInt % 2 = 0) :
    clever_149_double_the_difference.double_the_difference numbers
      = RustM.ok (0 : i64) := by
  sorry

/-- Singleton positive-odd take clause: a singleton whose only element
    is positive and odd returns its square.

    Captures the proptest `singleton_positive_odd` — verifies the
    take arm uses `l[i] * l[i]` (not `l[i]`, `2 * l[i]`, `|l[i]|`, …).

    Feasibility / precondition.  The natural universal claim
    "`double_the_difference [n] = n*n` for positive odd `n`" is false
    in the model: `n.toInt * n.toInt` overflows for
    `|n| ≥ 2^32`, and the function then fails with `integerOverflow`.
    The proptest's bound `k ∈ [0, 4999]` (so `n = 2k+1 ≤ 9999`,
    `n*n ≤ 10^8`) is the test-domain analogue; the corresponding
    Lean precondition is `n.toInt * n.toInt < 2^63`. -/
theorem singleton_positive_odd_returns_square
    (numbers : RustSlice i64) (n : i64)
    (h_size : numbers.val.size = 1)
    (h_first : ∀ (h : 0 < numbers.val.size), numbers.val[0]'h = n)
    (h_pos : 0 < n.toInt) (h_odd : n.toInt % 2 = 1)
    (h_fit : n.toInt * n.toInt < 2 ^ 63) :
    ∃ r : i64,
      clever_149_double_the_difference.double_the_difference numbers
        = RustM.ok r ∧
      r.toInt = n.toInt * n.toInt := by
  sorry

/-- Main functional-correctness postcondition.

    Captures the general case of the `known` test plus the proptest
    `singleton_positive_odd` (with the singleton clauses giving the
    direct selection checks).  Under a no-overflow precondition on
    every prefix of the conditional sum-of-squares,
    `double_the_difference numbers` succeeds and its result equals the
    `Int`-valued spec `dtd_int` evaluated at the full slice length.

    Feasibility / precondition.  The universal claim without `hfit` is
    false in the Lean model: a `RustSlice i64` can hold any `i64`
    values with arbitrary `size < 2^64`, so both each per-element
    square `l[i] * l[i]` (when `|l[i]|` is sufficiently large) and the
    running `acc + l[i]^2` (over many positive-odd elements) can
    overflow.  The proptest's `(-10000..=10000, 0..=100)` bounds keep
    the worst-case sum well under `2^63`; the corresponding hypothesis
    here is that every prefix sum of squares of positive odd elements
    fits in `i64`.  Because every selected contribution is the square
    of a positive integer (hence non-negative), this single upper
    bound on `dtd_int` at every prefix implies every individual
    `(l[i]).toInt * (l[i]).toInt < 2^63` too — the per-element
    multiplication overflow is dominated by the prefix bound at `k+1`. -/
theorem matches_spec
    (numbers : RustSlice i64)
    (hfit : ∀ k : Nat, k ≤ numbers.val.size →
              -(2 ^ 63 : Int) ≤ dtd_int numbers k
              ∧ dtd_int numbers k < 2 ^ 63) :
    ∃ r : i64,
      clever_149_double_the_difference.double_the_difference numbers
        = RustM.ok r ∧
      r.toInt = dtd_int numbers numbers.val.size := by
  sorry

/-! ## Tests classified as derived facts (skipped)

The proptest `additive_over_concat` asserts
`double_the_difference(xs ++ ys) = double_the_difference(xs) + double_the_difference(ys)`.
This is a structural-algebraic consequence of the integer-valued
spec — specifically, of the arithmetic identity
`dtd_int (xs ++ ys) = dtd_int xs + dtd_int ys` on the prefix-sum
oracle — lifted through `matches_spec`.  It is in the same family as
the rule-listed "operation is commutative" example: it follows from
functional correctness plus algebra and adds no verification value
over `matches_spec`.  Per the stage rules' derived-fact exception, no
explicit theorem is emitted for it.

The three concrete cases inside the `known` test
(`[1,3,2,0] ↦ 10`, `[-1,-2,0] ↦ 0`, `[9,-2] ↦ 81`) are concrete
instances directly subsumed by `matches_spec` on the corresponding
inputs; no separate theorem is emitted for them. -/

end Clever_149_double_the_differenceObligations
