
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


namespace div_floor_u64

--  Floored integer division for `u64`.
-- 
--  Equivalent to the original generic `num_integer::div_floor::<u64>(x, y)`.
@[spec]
def div_floor (x : u64) (y : u64) : RustM u64 := do (x /? y)

end div_floor_u64

