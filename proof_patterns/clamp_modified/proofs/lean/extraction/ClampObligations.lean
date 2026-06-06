-- Companion obligations file for the `clamp` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clamp

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace ClampObligations

open clamp

-- Postcondition: when x is strictly below the lower bound, clamp pins to lo.
theorem clamp_returns_lo (x lo hi : u8) :
    ⦃ ⌜ x < lo ⌝ ⦄ clamp x lo hi ⦃ ⇓ r => ⌜ r = lo ⌝ ⦄ := by
  mvcgen [clamp]
  all_goals grind

-- Postcondition: when x is within [lo, hi], clamp returns x unchanged.
theorem clamp_returns_x (x lo hi : u8) :
    ⦃ ⌜ lo ≤ x ∧ x ≤ hi ⌝ ⦄ clamp x lo hi ⦃ ⇓ r => ⌜ r = x ⌝ ⦄ := by
  mvcgen [clamp]
  all_goals grind

-- Postcondition: when x is strictly above hi (and at least lo), clamp pins to hi.
theorem clamp_returns_hi (x lo hi : u8) :
    ⦃ ⌜ lo ≤ x ∧ hi < x ⌝ ⦄ clamp x lo hi ⦃ ⇓ r => ⌜ r = hi ⌝ ⦄ := by
  mvcgen [clamp]
  all_goals grind

end ClampObligations
