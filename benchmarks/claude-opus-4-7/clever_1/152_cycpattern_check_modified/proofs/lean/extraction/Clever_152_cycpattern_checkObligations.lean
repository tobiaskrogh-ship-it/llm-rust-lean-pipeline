-- Companion obligations file for the `clever_152_cycpattern_check` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_152_cycpattern_check

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_152_cycpattern_checkObligations

-- Postcondition / totality / input-independence: the degenerate stub returns
-- `false` successfully for every pair of `i64` inputs. This single equation
-- simultaneously captures
--   * totality (no panic, no overflow on any `i64`),
--   * the constant-`false` return value,
--   * input-independence (both arguments are ignored).
-- (No precondition: the function is total on all `i64` pairs.)
-- (No failure condition: the body performs no fallible operation.)
theorem cycpattern_check_spec (a b : i64) :
    clever_152_cycpattern_check.cycpattern_check a b = RustM.ok false := rfl

end Clever_152_cycpattern_checkObligations
