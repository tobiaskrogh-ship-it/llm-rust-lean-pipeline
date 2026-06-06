-- Companion obligations file for the `sqrt_u64` extraction.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import sqrt_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Sqrt_u64Obligations

/-- Postcondition (lower bound). -/
theorem sqrt_lower_bound (x : u64) :
    ⦃ ⌜ True ⌝ ⦄
      sqrt_u64.sqrt x
    ⦃ ⇓ r => ⌜ r.toNat * r.toNat ≤ x.toNat ⌝ ⦄ := by
  hax_mvcgen [sqrt_u64.sqrt, sqrt_u64.log2]
  -- See how many goals are left
  all_goals first | (skip; sorry) | sorry

end Sqrt_u64Obligations
