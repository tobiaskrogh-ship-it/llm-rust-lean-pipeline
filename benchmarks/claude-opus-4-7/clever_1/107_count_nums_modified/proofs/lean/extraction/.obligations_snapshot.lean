-- Companion obligations file for the `clever_107_count_nums` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_107_count_nums

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_107_count_numsObligations

/-! ## Contract clauses

The Rust source contains five property tests plus a `known` unit test
that together describe the contract for `count_nums`:

  * `count_is_bounded` — `0 ≤ count_nums arr` *and* `count_nums arr ≤ arr.len()`.
    Split into two theorems below: `count_nums_nonneg` and `count_nums_le_size`.
  * `all_positives_counted` — strictly-positive elements always make the cut.
  * `zeros_never_counted` — zeros never make the cut.
  * `small_negatives_never_counted` — single-digit negatives never make the cut.
  * `count_is_additive` — counts add over slice concatenation.
  * `known` — three pinned values, two of which are subsumed by the
    boundary / all-positives clauses; the third (`[-1, 11, -11] ↦ 1`)
    pins the mixed-sign sign-branching and is captured separately.

### Feasibility preconditions

The proptest bounds each element to `[-10^6, 10^6]` and the slice
length to `< 30`.  The natural Lean generalisation quantifies over the
full i64 element range and arbitrary `RustSlice` sizes (`< 2^64`), but
the universal statement is false in those wider domains:

  * **Counter overflow.** `count_at` increments an `i64` counter per
    element, so for `arr.val.size ≥ 2^63` the running `acc +? 1` would
    overflow and the function would fail.  We add the precondition
    `arr.val.size < 2^63` (strictly stronger than the model's slice
    size bound `< 2^64`).
  * **`-n` overflow inside `signed_digit_sum`.** For `n = i64::MIN`
    the negation `-n` overflows and the function fails.  We exclude
    `Int64.minValue` from every element.

These are exactly the safety preconditions the proptest's bounded
ranges implicitly satisfy. -/

/-! ## Boundary clauses (no spec oracle required) -/

/-- Empty-slice boundary: `count_nums []` returns 0.  Captures the
    `known` test's `assert_eq!(count_nums(&[]), 0)` and the
    `arr.val.size = 0` corner of every other property. -/
theorem count_nums_empty
    (arr : RustSlice i64) (h_empty : arr.val.size = 0) :
    clever_107_count_nums.count_nums arr = RustM.ok (0 : i64) := by
  sorry

/-- All-zero boundary: if every element is `0` then `signed_digit_sum`
    is `0` and the predicate `> 0` never fires.  Captures the proptest
    `zeros_never_counted`. -/
theorem count_nums_all_zero
    (arr : RustSlice i64)
    (h_all_zero : ∀ (i : Nat) (h : i < arr.val.size), arr.val[i]'h = (0 : i64)) :
    clever_107_count_nums.count_nums arr = RustM.ok (0 : i64) := by
  sorry

/-- Small-negatives boundary: for every element `n ∈ [-9, -1]`,
    `signed_digit_sum n = -|n| < 0`, so the predicate `> 0` never
    fires.  Captures the proptest `small_negatives_never_counted`.
    The element-range hypothesis implicitly rules out `i64::MIN` and
    keeps `-n` from overflowing in `signed_digit_sum`. -/
theorem count_nums_small_negatives
    (arr : RustSlice i64)
    (h_small_neg : ∀ (i : Nat) (h : i < arr.val.size),
                     (-9 : Int) ≤ (arr.val[i]'h).toInt
                     ∧ (arr.val[i]'h).toInt ≤ -1) :
    clever_107_count_nums.count_nums arr = RustM.ok (0 : i64) := by
  sorry

/-! ## Bounded result (proptest `count_is_bounded`)

Split into two independent contract clauses — non-negativity and
upper-bound by slice length — per the per-clause-one-theorem rule. -/

/-- Lower bound: `count_nums arr ≥ 0`.  Captures the
    `prop_assert!(c >= 0)` half of `count_is_bounded`. -/
theorem count_nums_nonneg
    (arr : RustSlice i64)
    (h_size : (arr.val.size : Int) < 2^63)
    (h_no_min : ∀ (i : Nat) (h : i < arr.val.size),
                  arr.val[i]'h ≠ Int64.minValue) :
    ∃ r : i64,
      clever_107_count_nums.count_nums arr = RustM.ok r
      ∧ 0 ≤ r.toInt := by
  sorry

/-- Upper bound: `count_nums arr ≤ arr.val.size`.  Captures the
    `prop_assert!(c <= arr.len() as i64)` half of `count_is_bounded`. -/
theorem count_nums_le_size
    (arr : RustSlice i64)
    (h_size : (arr.val.size : Int) < 2^63)
    (h_no_min : ∀ (i : Nat) (h : i < arr.val.size),
                  arr.val[i]'h ≠ Int64.minValue) :
    ∃ r : i64,
      clever_107_count_nums.count_nums arr = RustM.ok r
      ∧ r.toInt ≤ (arr.val.size : Int) := by
  sorry

/-! ## Functional contract clauses -/

/-- All-positives postcondition: a slice of strictly-positive `i64`
    values is counted in full, i.e. the result equals the slice length.
    Captures the proptest `all_positives_counted`.  The `< 2^63`
    precondition keeps the counter in `i64`; positive elements are
    automatically `≠ i64::MIN`. -/
theorem count_nums_all_positives
    (arr : RustSlice i64)
    (h_size : (arr.val.size : Int) < 2^63)
    (h_all_pos : ∀ (i : Nat) (h : i < arr.val.size),
                   0 < (arr.val[i]'h).toInt) :
    ∃ r : i64,
      clever_107_count_nums.count_nums arr = RustM.ok r
      ∧ r.toInt = (arr.val.size : Int) := by
  sorry

/-- Additivity: `count_nums (a ++ b) = count_nums a + count_nums b`,
    where `c` is a slice whose underlying array is `a.val ++ b.val`.
    Captures the proptest `count_is_additive`.  The precondition
    `c.val.size < 2^63` is the natural overflow bound; it implies the
    per-half bounds since `a.val.size, b.val.size ≤ c.val.size`. -/
theorem count_nums_additive
    (a b c : RustSlice i64)
    (h_concat : c.val = a.val ++ b.val)
    (h_c_size : (c.val.size : Int) < 2^63)
    (h_no_min_a : ∀ (i : Nat) (h : i < a.val.size),
                    a.val[i]'h ≠ Int64.minValue)
    (h_no_min_b : ∀ (i : Nat) (h : i < b.val.size),
                    b.val[i]'h ≠ Int64.minValue) :
    ∃ ra rb rc : i64,
      clever_107_count_nums.count_nums a = RustM.ok ra
      ∧ clever_107_count_nums.count_nums b = RustM.ok rb
      ∧ clever_107_count_nums.count_nums c = RustM.ok rc
      ∧ rc.toInt = ra.toInt + rb.toInt := by
  sorry

/-! ## Unit pin: mixed-sign slice from the `known` test

The slice `[-1, 11, -11]` has signed digit sums `[-1, 2, 0]`:
  * `signed_digit_sum (-1) = digit_sum 1 - 2*first_digit 1 = 1 - 2 = -1`
  * `signed_digit_sum 11   = 1 + 1 = 2`
  * `signed_digit_sum (-11) = digit_sum 11 - 2*first_digit 11 = 2 - 2*1 = 0`
Only `11` clears `> 0`, so the count is `1`.  Exercises the negative
branch of `signed_digit_sum`, which the boundary / all-positives /
all-negatives theorems above do not jointly cover. -/
theorem count_nums_at_neg_mix :
    clever_107_count_nums.count_nums
        { val := #[(-1 : i64), 11, -11], size_lt_usizeSize := by decide }
      = RustM.ok (1 : i64) := by
  sorry

end Clever_107_count_numsObligations
