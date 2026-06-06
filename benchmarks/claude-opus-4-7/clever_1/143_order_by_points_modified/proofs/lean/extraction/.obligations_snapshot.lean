-- Companion obligations file for the `clever_143_order_by_points` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_143_order_by_points

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_143_order_by_pointsObligations

/-! ## Specification oracles.

These are pure (non-`RustM`) functions used to state the contract.  The proof
stage is responsible for bridging them to the extracted definitions. -/

/-- Count occurrences of `target` among the first `k` entries of `s`. -/
private def vec_count (s : Array i64) (target : i64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      if h : k < s.size then
        (if (s[k]'h) = target then 1 else 0) + vec_count s target k
      else
        vec_count s target k

/-- Leading decimal digit of `n` (for `n = 0`, returns 0). -/
private def first_digit_nat (n : Nat) : Nat :=
  if n < 10 then n else first_digit_nat (n / 10)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

/-- Sum of the decimal digits of `n`, added to `acc`. -/
private def digit_sum_nat (n acc : Nat) : Nat :=
  if h : 0 < n then digit_sum_nat (n / 10) (acc + n % 10)
  else acc
termination_by n
decreasing_by exact Nat.div_lt_self h (by decide)

/-- Integer-level oracle for the sort key.  Matches the Rust
    `signed_digit_sum` semantics:
    * `n = 0`             → `0`
    * `n > 0`             → digit sum of `n`
    * `n < 0`             → digit sum of `|n|` with the leading digit's
                             contribution negated (i.e. `digit_sum − 2·first_digit`).
-/
private def signed_digit_sum_int (n : Int) : Int :=
  if n = 0 then 0
  else if 0 < n then (digit_sum_nat n.toNat 0 : Int)
  else
    let m := (-n).toNat
    (digit_sum_nat m 0 : Int) - 2 * (first_digit_nat m : Int)

/-- Subsequence of the first `n` entries of `s` whose key (under
    `signed_digit_sum_int`) equals `k`.  Used for the stability clause. -/
private def filter_by_key (s : Array i64) (k : Int) : Nat → Array i64
  | 0     => #[]
  | n + 1 =>
      if h : n < s.size then
        let rest := filter_by_key s k n
        if signed_digit_sum_int (s[n]'h).toInt = k then rest.push (s[n]'h)
        else rest
      else
        filter_by_key s k n

/-! ## Obligation theorems.

Each clause of the Rust contract becomes one theorem.  The success
predicate `order_by_points l = RustM.ok v` already excludes the
`Int64.minValue` failure path (negation in `signed_digit_sum` panics
there), so no separate no-overflow precondition is needed. -/

/-- Anchor: an empty input slice yields a successful empty output. -/
theorem empty_input_yields_empty_output
    (l : RustSlice i64) (hempty : l.val.size = 0) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_143_order_by_points.order_by_points l = RustM.ok v ∧
      v.val.size = 0 := by
  sorry

/-- Postcondition 1 — Permutation: the multiset of output entries equals
    the multiset of input entries (witnessed by `vec_count`). -/
theorem output_is_permutation_of_input
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_143_order_by_points.order_by_points l = RustM.ok v)
    (target : i64) :
    vec_count v.val target v.val.size
      = vec_count l.val target l.val.size := by
  sorry

/-- Postcondition 2 — Sorted by key: consecutive output entries are
    non-decreasing under `signed_digit_sum_int`. -/
theorem output_is_sorted_by_signed_digit_sum
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_143_order_by_points.order_by_points l = RustM.ok v)
    (k : Nat) (hk : k + 1 < v.val.size) :
    signed_digit_sum_int (v.val[k]'(Nat.lt_of_succ_lt hk)).toInt
      ≤ signed_digit_sum_int (v.val[k + 1]'hk).toInt := by
  sorry

/-- Postcondition 3 — Stability: for every key value `k`, the subsequence
    of input elements whose key equals `k` is preserved verbatim in the
    output.  This is the standard "filter-by-key" formulation of stable
    sorting and is independent of the multiset and sortedness clauses. -/
theorem output_is_stable
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_143_order_by_points.order_by_points l = RustM.ok v)
    (k : Int) :
    filter_by_key l.val k l.val.size
      = filter_by_key v.val k v.val.size := by
  sorry

/-- Unit pin (mirrors the Rust `known` test): the documented sample input
    produces the documented sample output. -/
theorem order_by_points_known :
    clever_143_order_by_points.order_by_points
        { val := #[(1 : i64), 11, -1, -11, 0], size_lt_usizeSize := by decide }
      = RustM.ok ⟨#[(-1 : i64), -11, 0, 1, 11], by decide⟩ := by
  sorry

end Clever_143_order_by_pointsObligations
