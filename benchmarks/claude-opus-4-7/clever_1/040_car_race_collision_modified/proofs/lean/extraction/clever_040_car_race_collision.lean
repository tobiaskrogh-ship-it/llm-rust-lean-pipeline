
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


namespace clever_040_car_race_collision

--  n cars going each direction; every left-to-right car eventually crosses
--  every right-to-left car ⇒ n × n total "collisions".
@[spec]
def car_race_collision (x : u64) : RustM u64 := do (x *? x)

end clever_040_car_race_collision

