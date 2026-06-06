
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


namespace gcd_rec

@[spec]
def gcd_rec (a : u64) (b : u64) : RustM u64 := do
  if (← (b ==? (0 : u64))) then do (pure a) else do (gcd_rec b (← (a %? b)))
partial_fixpoint

end gcd_rec

