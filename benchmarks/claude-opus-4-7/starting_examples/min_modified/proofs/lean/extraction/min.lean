
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


namespace min

@[spec]
def min (a : u8) (b : u8) : RustM u8 := do
  if (← (a <=? b)) then do (pure a) else do (pure b)

end min

