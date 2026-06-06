-- Companion obligations file for the `min` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import min

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace MinObligations

/-- Postcondition (lower bound): `min a b` is ≤ both inputs.
    A buggy impl that always returns `a` would fail this whenever `b < a`. -/
theorem min_is_lower_bound (a b : u8) :
    ⦃ ⌜ True ⌝ ⦄ min.min a b ⦃ ⇓ r => ⌜ r ≤ a ∧ r ≤ b ⌝ ⦄ := by
  hax_mvcgen [min.min]
  <;> bv_decide

/-- Postcondition (achieved): `min a b` equals one of the two inputs.
    A buggy impl that always returns 0 would fail this whenever neither input is 0. -/
theorem min_equals_one_input (a b : u8) :
    ⦃ ⌜ True ⌝ ⦄ min.min a b ⦃ ⇓ r => ⌜ r = a ∨ r = b ⌝ ⦄ := by
  hax_mvcgen [min.min]
  · exact Or.inl trivial
  · exact Or.inr trivial

end MinObligations
