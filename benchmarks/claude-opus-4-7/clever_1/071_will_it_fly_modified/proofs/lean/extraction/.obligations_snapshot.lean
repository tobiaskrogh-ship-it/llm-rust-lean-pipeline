-- Companion obligations file for the `clever_071_will_it_fly` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_071_will_it_fly

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_071_will_it_flyObligations

/-! ## Specifications: integer-valued prefix sum and palindrome predicate

The Rust function `will_it_fly q w` returns `true` iff `q` is palindromic
*and* its `i64` sum is `≤ w`.  The integer-valued prefix sum is used to
state the contract without depending on `i64` overflow behaviour, and to
expose the "no overflow during summation" precondition needed for the
function to evaluate to `RustM.ok _` at all. -/

/-- Integer-valued prefix sum of `q`. -/
private def prefix_sum_int (q : RustSlice i64) : Nat → Int
  | 0     => 0
  | k + 1 =>
      prefix_sum_int q k +
        (if h : k < q.val.size then (q.val[k]'h).toInt else 0)

/-- `q` is a palindrome: every pair of indices summing to `size - 1`
    holds equal values.  Vacuously true for `size = 0`; trivially true
    for `size = 1`. -/
private def is_palindrome (q : RustSlice i64) : Prop :=
  ∀ i j : Nat, i + j + 1 = q.val.size →
    ∀ (hi : i < q.val.size) (hj : j < q.val.size),
      q.val[i]'hi = q.val[j]'hj

/-! ## Contract clauses

For every clause we require that all prefix sums of `q` fit in `i64`;
without this precondition `sum_at` would already `fail` on integer
overflow and the function would not return `ok _`.  This is the
strongest natural precondition: the proptest's bound (`q` values in
`-100..=100`, `len < 10`) is one bounded slice of the full domain on
which the contract is meaningful. -/

/-- **Clause 1** (necessity of weight bound): if the integer sum of `q`
    strictly exceeds `w`, then `will_it_fly q w` returns `ok false`.

    Captures the proptest `sum_exceeds_w_means_false`. -/
theorem sum_exceeds_w_returns_false (q : RustSlice i64) (w : i64)
    (hfit : ∀ k : Nat, k ≤ q.val.size →
              -(2^63 : Int) ≤ prefix_sum_int q k ∧ prefix_sum_int q k < 2^63)
    (hexceeds : w.toInt < prefix_sum_int q q.val.size) :
    clever_071_will_it_fly.will_it_fly q w = RustM.ok false := by
  sorry

/-- **Clause 2** (necessity of palindrome): if `q` is not a palindrome,
    then `will_it_fly q w` returns `ok false`.

    Captures the proptest `nonpalindrome_means_false`.  A non-palindromic
    slice has `size ≥ 2` (the empty and singleton slices are palindromes
    by definition); on such inputs either the sum check or the palindrome
    check rejects `q`, in both cases returning `ok false`. -/
theorem nonpalindrome_returns_false (q : RustSlice i64) (w : i64)
    (hfit : ∀ k : Nat, k ≤ q.val.size →
              -(2^63 : Int) ≤ prefix_sum_int q k ∧ prefix_sum_int q k < 2^63)
    (hnp : ¬ is_palindrome q) :
    clever_071_will_it_fly.will_it_fly q w = RustM.ok false := by
  sorry

/-- **Clause 3** (sufficiency): if `q` is a palindrome and its integer
    sum does not exceed `w`, then `will_it_fly q w` returns `ok true`.

    Captures the proptest `palindrome_with_room_is_true`.  Specialises
    naturally to the empty-slice boundary case from `small_cases`:
    `q = []` is vacuously palindromic and has sum `0`, so for any
    `0 ≤ w` the function returns `ok true`. -/
theorem palindrome_with_room_returns_true (q : RustSlice i64) (w : i64)
    (hfit : ∀ k : Nat, k ≤ q.val.size →
              -(2^63 : Int) ≤ prefix_sum_int q k ∧ prefix_sum_int q k < 2^63)
    (hpal : is_palindrome q)
    (hsum_le : prefix_sum_int q q.val.size ≤ w.toInt) :
    clever_071_will_it_fly.will_it_fly q w = RustM.ok true := by
  sorry

end Clever_071_will_it_flyObligations
