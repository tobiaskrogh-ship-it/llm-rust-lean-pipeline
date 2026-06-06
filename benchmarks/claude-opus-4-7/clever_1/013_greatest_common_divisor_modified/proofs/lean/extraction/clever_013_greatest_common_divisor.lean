
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


namespace clever_013_greatest_common_divisor

--  Return the greatest common divisor of two non-negative integers.
@[spec]
def greatest_common_divisor (a : u64) (b : u64) : RustM u64 := do
  if (← (b ==? (0 : u64))) then do
    (pure a)
  else do
    (greatest_common_divisor b (← (a %? b)))
partial_fixpoint

end clever_013_greatest_common_divisor

