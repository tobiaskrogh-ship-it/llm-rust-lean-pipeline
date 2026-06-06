
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


namespace saturating_sub

@[spec]
def saturating_sub (a : u8) (b : u8) : RustM u8 := do
  if (← (a >? b)) then do (a -? b) else do (pure (0 : u8))

end saturating_sub

