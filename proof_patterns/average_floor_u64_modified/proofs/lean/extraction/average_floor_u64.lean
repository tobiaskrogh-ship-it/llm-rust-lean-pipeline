
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


namespace average_floor_u64

--  Returns the floor value of the average of `x` and `y` -- `⌊(x + y)/2⌋`.
-- 
--  Equivalent to `num_integer::average_floor::<u64>(x, y)`.
@[spec]
def average_floor (x : u64) (y : u64) : RustM u64 := do
  ((← (x &&&? y)) +? (← ((← (x ^^^? y)) >>>? (1 : i32))))

end average_floor_u64

