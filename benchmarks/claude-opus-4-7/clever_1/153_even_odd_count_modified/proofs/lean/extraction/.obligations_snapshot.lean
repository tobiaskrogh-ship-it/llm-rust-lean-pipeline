-- Companion obligations file for the `clever_153_even_odd_count` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_153_even_odd_count

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_153_even_odd_countObligations

/-! ## Nat-level oracle for the contract -/

/-- Walk through the decimal digits of `n` (low to high via `/ 10`),
    incrementing the even-counter `e` for each even digit and the
    odd-counter `o` for each odd digit. Mirrors the Rust `count_at`
    helper exactly. -/
private def count_at_nat (n e o : Nat) : Nat × Nat :=
  if h : 0 < n then
    if (n % 10) % 2 = 0 then count_at_nat (n / 10) (e + 1) o
    else count_at_nat (n / 10) e (o + 1)
  else (e, o)
termination_by n
decreasing_by all_goals exact Nat.div_lt_self h (by decide)

/-- Specification of `even_odd_count(n)` — for `n = 0` we count one digit
    `0` (which is even), giving `(1, 0)`. Otherwise the result is the
    digit-by-digit count produced by `count_at_nat` starting from
    `(e, o) = (0, 0)`. -/
private def even_odd_count_nat (n : Nat) : Nat × Nat :=
  if n = 0 then (1, 0) else count_at_nat n 0 0

/-! ## Contract clauses

The Rust source carries one `known` block with five unit pins and one
proptest `matches_reference` that checks the closed-form digit-count
postcondition on every `u64`.  Each becomes one theorem below.

Feasibility note for `matches_reference`: a `u64` value has at most 20
decimal digits (since `2^64 < 10^20`), so the accumulators
`e + o ≤ 20 ≪ 2^64` and no overflow is possible. The universal
statement is therefore true in the Lean model without any precondition.
-/

/-- Unit pin from `known`: `even_odd_count(0) = (1, 0)` (the lone digit
    `0` is counted as one even digit). -/
theorem even_odd_count_at_0 :
    clever_153_even_odd_count.even_odd_count 0
      = RustM.ok (rust_primitives.hax.Tuple2.mk (1 : u64) (0 : u64)) := by
  native_decide

/-- Unit pin from `known`: `even_odd_count(7) = (0, 1)`. -/
theorem even_odd_count_at_7 :
    clever_153_even_odd_count.even_odd_count 7
      = RustM.ok (rust_primitives.hax.Tuple2.mk (0 : u64) (1 : u64)) := by
  native_decide

/-- Unit pin from `known`: `even_odd_count(12) = (1, 1)`. -/
theorem even_odd_count_at_12 :
    clever_153_even_odd_count.even_odd_count 12
      = RustM.ok (rust_primitives.hax.Tuple2.mk (1 : u64) (1 : u64)) := by
  native_decide

/-- Unit pin from `known`: `even_odd_count(123) = (1, 2)`. -/
theorem even_odd_count_at_123 :
    clever_153_even_odd_count.even_odd_count 123
      = RustM.ok (rust_primitives.hax.Tuple2.mk (1 : u64) (2 : u64)) := by
  native_decide

/-- Unit pin from `known`: `even_odd_count(246) = (3, 0)`. -/
theorem even_odd_count_at_246 :
    clever_153_even_odd_count.even_odd_count 246
      = RustM.ok (rust_primitives.hax.Tuple2.mk (3 : u64) (0 : u64)) := by
  native_decide

/-- Main postcondition (`matches_reference`): for every `u64 num`,
    `even_odd_count num` succeeds and returns the digit-by-digit even/odd
    counts of `num` (with the `n = 0` special case counting one even
    digit).  Holds universally because the digit count of any `u64` is
    at most 20, far below `2^64`. -/
theorem even_odd_count_matches_reference (num : u64) :
    clever_153_even_odd_count.even_odd_count num
      = RustM.ok (rust_primitives.hax.Tuple2.mk
          (UInt64.ofNat (even_odd_count_nat num.toNat).1)
          (UInt64.ofNat (even_odd_count_nat num.toNat).2)) := by
  sorry

end Clever_153_even_odd_countObligations
