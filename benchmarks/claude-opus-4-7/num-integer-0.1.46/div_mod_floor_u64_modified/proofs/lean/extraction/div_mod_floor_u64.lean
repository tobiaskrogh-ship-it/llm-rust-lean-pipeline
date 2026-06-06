
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


namespace div_mod_floor_u64

--  Simultaneous floored integer division and modulus, monomorphized to `u64`.
-- 
--  Equivalent to `num_integer::div_mod_floor::<u64>(x, y)`.
@[spec]
def my_div_mod_floor (x : u64) (y : u64) :
    RustM (rust_primitives.hax.Tuple2 u64 u64) := do
  (pure (rust_primitives.hax.Tuple2.mk (← (x /? y)) (← (x %? y))))

end div_mod_floor_u64

