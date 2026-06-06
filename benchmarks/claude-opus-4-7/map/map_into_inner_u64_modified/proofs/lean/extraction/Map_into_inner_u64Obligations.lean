-- Companion obligations file for the `map_into_inner_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import map_into_inner_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Map_into_inner_u64Obligations

open map_into_inner_u64

-- Postcondition: `into_inner` returns the inner `Range<u64>` unchanged.
-- The result equals `self.iter` exactly (same `start`, same `end`).
-- Note: independence from `f` is automatic — the RHS does not mention `self.f`.
-- (No precondition: the function is total on every `Map` value.)
-- (No failure condition: a pure field projection cannot panic.)
theorem into_inner_returns_iter (self : Map) :
    Impl.into_inner self = RustM.ok self.iter := rfl

end Map_into_inner_u64Obligations
