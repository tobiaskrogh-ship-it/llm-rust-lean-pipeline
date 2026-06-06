
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


namespace average_ceil_u64

--  Returns ⌈(x + y) / 2⌉ without overflow, for `u64`.
-- 
--  Monomorphic version of `num_integer::average_ceil::<u64>`.
@[spec]
def average_ceil (x : u64) (y : u64) : RustM u64 := do
  ((← (x |||? y)) -? (← ((← (x ^^^? y)) >>>? (1 : i32))))

end average_ceil_u64

