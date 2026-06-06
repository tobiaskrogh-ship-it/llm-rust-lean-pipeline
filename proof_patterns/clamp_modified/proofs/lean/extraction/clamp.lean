
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


namespace clamp

@[spec]
def clamp (x : u8) (lo : u8) (hi : u8) : RustM u8 := do
  if (← (x <? lo)) then do
    (pure lo)
  else do
    if (← (x >? hi)) then do (pure hi) else do (pure x)

end clamp

