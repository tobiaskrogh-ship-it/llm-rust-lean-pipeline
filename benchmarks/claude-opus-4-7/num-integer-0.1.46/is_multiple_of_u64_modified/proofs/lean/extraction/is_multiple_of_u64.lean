
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


namespace is_multiple_of_u64

@[spec]
def is_multiple_of (a : u64) (b : u64) : RustM Bool := do
  if (← (b ==? (0 : u64))) then do
    (a ==? (0 : u64))
  else do
    ((← (a %? b)) ==? (0 : u64))

end is_multiple_of_u64

