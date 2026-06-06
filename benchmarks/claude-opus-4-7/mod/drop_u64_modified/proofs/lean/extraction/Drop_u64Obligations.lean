-- Companion obligations file for the `drop_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import drop_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Drop_u64Obligations

-- Postcondition + totality: `drop x` always succeeds and yields the unique
-- inhabitant of `Tuple0`.
--
-- Captures Rust property tests:
--   * `prop_drop_is_total_and_returns_unit` — (P1) totality and (P2) the
--     returned value is `()`. Since `Tuple0` is a singleton inhabited only
--     by `Tuple0.mk`, "returns `()`" and "always succeeds" collapse to one
--     equation: `drop x = RustM.ok Tuple0.mk`.
--   * `prop_drop_can_be_called_repeatedly` — restates totality on a single
--     value; subsumed by the universal statement here.
--   * `doctest_basic_call`, `drop_returns_unit` — instances of the same
--     equation.
--
-- (No precondition: the function is total on all `u64` inputs.)
-- (No failure condition: the body is empty and cannot panic.)
theorem drop_spec (x : u64) :
    drop_u64.drop x = RustM.ok rust_primitives.hax.Tuple0.mk := rfl

end Drop_u64Obligations
