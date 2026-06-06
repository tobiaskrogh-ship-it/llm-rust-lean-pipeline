-- Companion obligations file for the `copy_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import copy_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Copy_u64Obligations

-- Postcondition: `copy x` returns `x` unchanged, for every `u64` input.
-- This is the function's entire contract — the property test `prop_copy_returns_input`
-- (and the value-specific tests `doctest_basic_copy`, `copy_various_u64_values`,
-- `copy_usable_as_fn_pointer`) all assert this single semantic claim.
-- (No precondition: the function is total on all u64 inputs.)
-- (No failure condition: dereferencing a `&u64` and returning it cannot panic.)
theorem copy_spec (x : u64) :
    copy_u64.copy x = RustM.ok x := rfl

end Copy_u64Obligations
