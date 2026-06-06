-- Companion obligations file for the `clever_052_add` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_052_add

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_052_addObligations

/-! ## Definitional helper

    Unfolds `+?` on `i64` so the two contract theorems can dispatch the
    overflow branch by `if_pos` / `if_neg`. Mirrors `hax_add_def_u8` from
    the `add_one` reference but for the signed 64-bit operator. -/
private theorem hax_add_def_i64 (x y : i64) :
    x +? y = if Int64.addOverflow x y
             then RustM.fail Error.integerOverflow
             else pure (x + y) := rfl

/-! ## Postcondition (no overflow)

    Corresponds to the property test `equals_mathematical_sum` in the
    Rust source:

      prop_assert_eq!(add(x, y), x + y);

    The proptest bounds `x, y ∈ [-2^31, 2^31]` encode the no-overflow
    precondition on `x + y`; in Lean this is the universal hypothesis
    `¬ Int64.addOverflow x y`, which is the strongest claim that's
    actually true in the model. -/
theorem add_postcondition (x y : i64) (h : ¬ Int64.addOverflow x y) :
    clever_052_add.add x y = RustM.ok (x + y) := by
  sorry

/-! ## Failure condition (overflow)

    The doc-comment notes: "In debug builds the addition panics on
    overflow". Hax models this panic as `RustM.fail Error.integerOverflow`.
    No proptest exercises this branch directly, but it is the second half
    of the function's behavioural contract and the obligation must exist
    so the model surface is fully constrained. -/
theorem add_overflow_failure (x y : i64) (h : Int64.addOverflow x y) :
    clever_052_add.add x y = RustM.fail Error.integerOverflow := by
  sorry

/-! ## Postcondition, bridged to the mathematical sum

    The doc-comment phrases the contract as: "the result equals the
    mathematical sum `x + y`". The proptest checks this at the wrapping
    i64 level (`add(x, y) == x + y`); the bridged form here states it
    at the `Int` level, which is the natural "mathematical" reading and
    the form callers want for any downstream reasoning. -/
theorem add_toInt_postcondition (x y : i64) (h : ¬ Int64.addOverflow x y) :
    ∃ r : i64,
      clever_052_add.add x y = RustM.ok r ∧
      r.toInt = x.toInt + y.toInt := by
  sorry

end Clever_052_addObligations
