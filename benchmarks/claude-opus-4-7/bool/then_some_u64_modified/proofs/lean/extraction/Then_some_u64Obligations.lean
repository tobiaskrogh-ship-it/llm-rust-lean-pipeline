-- Companion obligations file for the `then_some_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import then_some_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Then_some_u64Obligations

-- Postcondition (true branch): when `b = true`, `then_some` returns `Some t`,
-- preserving the payload exactly. Mirrors the Rust property test
-- `then_some_true_preserves_value`.
-- (No precondition: function is total on all (Bool, u64) inputs.)
-- (No failure condition: branching + pure construction can never panic.)
theorem then_some_true_preserves_value (t : u64) :
    then_some_u64.then_some true t
      = RustM.ok (core_models.option.Option.Some t) := rfl

-- Postcondition (false branch): when `b = false`, `then_some` returns `None`,
-- regardless of `t`. Mirrors the Rust property test `then_some_false_is_none`.
theorem then_some_false_is_none (t : u64) :
    then_some_u64.then_some false t
      = RustM.ok core_models.option.Option.None := rfl

end Then_some_u64Obligations
