-- Companion obligations file for the `ok_or_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import ok_or_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Ok_or_u64Obligations

-- Postcondition (true branch): for every `err`, `ok_or true err` returns
-- `Ok(())`. The `err` argument must not appear in the result.
-- (No precondition: the function is total on all (Bool, u64) inputs.)
-- (No failure condition: a pure if/else on a `Bool` can never panic.)
theorem ok_or_true_yields_ok_unit (err : u64) :
    ok_or_u64.ok_or true err
      = RustM.ok (core_models.result.Result.Ok rust_primitives.hax.Tuple0.mk) := rfl

-- Postcondition (false branch): for every `err`, `ok_or false err` returns
-- `Err(err)` — the payload is propagated unchanged (not zeroed, not transformed).
theorem ok_or_false_preserves_err (err : u64) :
    ok_or_u64.ok_or false err
      = RustM.ok (core_models.result.Result.Err err) := rfl

end Ok_or_u64Obligations
