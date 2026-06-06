
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


namespace contains_nonascii_usize

def NONASCII_MASK : usize := (9259542123273814144 : usize)

@[spec]
def contains_nonascii (x : usize) : RustM Bool := do
  ((← (x &&&? NONASCII_MASK)) !=? (0 : usize))

end contains_nonascii_usize

