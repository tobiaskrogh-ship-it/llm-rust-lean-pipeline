
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace from_mut_u64

--  Converts a mutable reference to `T` into a mutable reference to an array of length 1 (without copying).
@[spec]
def from_mut (s : u64) : RustM sorry := do (pure sorry)

end from_mut_u64

