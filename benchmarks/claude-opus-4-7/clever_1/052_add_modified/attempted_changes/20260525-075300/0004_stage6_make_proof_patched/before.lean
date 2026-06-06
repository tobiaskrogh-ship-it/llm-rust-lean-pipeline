-- Companion obligations file for the `clever_046_add_two` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_046_add_two

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_046_add_twoObligations

/-- Postcondition: when the signed addition `x + y` does not overflow `i64`,
    `add_two x y` returns `x + y` successfully (no panic).

    Corresponds to the proptest `equals_mathematical_sum`:
    `prop_assert_eq!(add_two(x, y), x + y)` under bounded
    `x, y ∈ [-2^31, 2^31]` (which encodes the no-overflow precondition on
    `x + y`).  The bound `2^31` in the proptest is the sampling slice; the
    real Lean-model precondition is `¬ Int64.addOverflow x y`, which is the
    strongest honest contract here. -/
theorem add_two_ok (x y : i64) (hno : ¬ Int64.addOverflow x y) :
    clever_046_add_two.add_two x y = RustM.ok (x + y) := by
  simp only [Int64.addOverflow] at hno
  unfold clever_046_add_two.add_two
  simp only [rust_primitives.ops.arith.Add.add, if_neg hno]
  rfl

/-- Failure condition: when the signed addition `x + y` overflows `i64`,
    `add_two x y` panics with `Error.integerOverflow`.

    Sourced from the doc comment ("In debug builds the addition panics on
    overflow"), which the proptest's bounded domain avoids exercising.
    The Rust panic is modelled by `RustM.fail Error.integerOverflow`. -/
theorem add_two_overflow (x y : i64) (hov : Int64.addOverflow x y) :
    clever_046_add_two.add_two x y = RustM.fail Error.integerOverflow := by
  sorry

end Clever_046_add_twoObligations
