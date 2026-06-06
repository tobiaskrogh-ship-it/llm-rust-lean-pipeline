
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


namespace div_rem_u64

--  Simultaneous truncated integer division and remainder for `u64`.
-- 
--  Returns `(quotient, remainder)` where `quotient = x / y` and
--  `remainder = x % y`. Panics on `y == 0`, matching the behavior of the
--  underlying `u64` operators (and of the original `num_integer::div_rem`).
@[spec]
def div_rem (x : u64) (y : u64) :
    RustM (rust_primitives.hax.Tuple2 u64 u64) := do
  (pure (rust_primitives.hax.Tuple2.mk (← (x /? y)) (← (x %? y))))

end div_rem_u64

