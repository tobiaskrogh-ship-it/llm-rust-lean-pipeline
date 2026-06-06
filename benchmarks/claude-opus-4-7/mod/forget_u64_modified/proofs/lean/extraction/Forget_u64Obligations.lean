-- Companion obligations file for the `forget_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import forget_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Forget_u64Obligations

-- Postcondition + totality + no-failure (all three clauses collapse into one
-- equation because `rust_primitives.hax.Tuple0` is a singleton type, so the
-- only non-failing `RustM rust_primitives.hax.Tuple0` value is
-- `RustM.ok Tuple0.mk`). The property test
-- `forget_returns_unit_on_representative_values` asserts exactly this for a
-- representative cover of `u64` boundaries and interior points; the
-- universally-quantified equation discharges every such instance.
--   * Pre:   None (every `u64` is a valid argument).
--   * Post:  the result is `()` (i.e. `Tuple0.mk`).
--   * Fail:  the function does not return `RustM.fail …`.
theorem forget_returns_unit (t : u64) :
    forget_u64.forget t = RustM.ok rust_primitives.hax.Tuple0.mk := rfl

end Forget_u64Obligations
