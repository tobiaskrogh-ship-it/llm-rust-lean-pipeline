-- Companion obligations file for the `clever_124_minPath` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_124_minPath

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_124_minPathObligations

-- Postcondition (the entire contract of this degenerate stub):
-- for every pair of `u64` inputs the function returns `0` successfully.
-- The CLEVER signature discards the grid structure, so the constant-zero
-- sentinel *is* the specification; this also pins down totality / no-panic.
-- (No precondition: the function is total on all `u64` inputs.)
-- (No failure condition: there is no partial operation in the body.)
theorem minPath_returns_zero (grid k : u64) :
    clever_124_minPath.minPath grid k = RustM.ok 0 := rfl

end Clever_124_minPathObligations
