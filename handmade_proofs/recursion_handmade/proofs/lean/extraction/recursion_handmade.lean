
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


namespace recursion_handmade

@[spec]
def count_to (n : u64) : RustM u64 := do
  if (← (n ==? (0 : u64))) then do
    (pure (0 : u64))
  else do
    ((← (count_to (← (n -? (1 : u64))))) +? (1 : u64))
partial_fixpoint

end recursion_handmade

