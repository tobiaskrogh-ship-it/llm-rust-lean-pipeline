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

/-- Boundary: when both inputs are 0, the loop's condition `b !=? 0` is
    immediately false, the loop returns `(0, 0)` without executing the
    body, and the function returns `0`. We try `native_decide` first;
    if the partial-fixpoint loop is not reducible by computation, we
    fall through to `sorry`. -/
theorem gcd_while_zero_zero :
    gcd_while.gcd_while (0 : u64) (0 : u64) = RustM.ok (0 : u64) := by
  native_decide

end Gcd_whileObligations
