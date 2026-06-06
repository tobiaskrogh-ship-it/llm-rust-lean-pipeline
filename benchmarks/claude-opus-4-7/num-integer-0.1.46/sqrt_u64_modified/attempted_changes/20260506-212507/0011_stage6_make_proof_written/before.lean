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

/-- Postcondition (lower bound): the result `r` of `sqrt x` satisfies `r² ≤ x`. -/
theorem sqrt_lower_bound (x : u64) :
    ⦃ ⌜ True ⌝ ⦄
      sqrt_u64.sqrt x
    ⦃ ⇓ r => ⌜ r.toNat * r.toNat ≤ x.toNat ⌝ ⦄ := by
  hax_mvcgen [sqrt_u64.sqrt, sqrt_u64.log2]
  case' vc1.isTrue.isTrue => sorry
  all_goals (trace_state; sorry)

end Sqrt_u64Obligations
