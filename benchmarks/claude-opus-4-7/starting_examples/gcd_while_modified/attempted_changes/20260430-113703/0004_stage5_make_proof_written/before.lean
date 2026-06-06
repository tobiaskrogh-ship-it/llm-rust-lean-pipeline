-- Companion obligations file for the `gcd_while` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import gcd_while

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Gcd_whileObligations

/-- Try a Hoare-triple-style attack on totality. -/
theorem gcd_while_total_triple (a b : u64) :
    ⦃ ⌜ True ⌝ ⦄ gcd_while.gcd_while a b ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  hax_mvcgen [gcd_while.gcd_while]
  · exact ⟨fun _ => True, by intros; mvcgen⟩
  · exact ⟨fun ⟨_, b⟩ => b.toNat, by intros; mvcgen⟩
  · exact ⟨fun ⟨_, b⟩ => decide (b ≠ 0), by intros; mvcgen⟩
  · sorry
  · sorry

end Gcd_whileObligations
