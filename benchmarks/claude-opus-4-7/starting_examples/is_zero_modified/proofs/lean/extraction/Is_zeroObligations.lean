-- Companion obligations file for the `is_zero` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import is_zero

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Is_zeroObligations

-- Postcondition: is_zero returns ok true exactly when x = 0, and ok false otherwise.
-- Equivalently, the returned value equals the Boolean equality (x == 0).
-- (No precondition: the function is total on all u8 inputs.)
-- (No failure condition: equality comparison on u8 can never panic.)
theorem is_zero_spec (x : u8) :
    is_zero.is_zero x = RustM.ok (x == 0) := rfl

end Is_zeroObligations
