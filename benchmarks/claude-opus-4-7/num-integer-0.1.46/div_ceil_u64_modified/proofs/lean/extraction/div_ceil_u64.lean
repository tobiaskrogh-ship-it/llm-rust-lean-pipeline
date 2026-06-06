
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


namespace div_ceil_u64

--  Ceiled integer division for `u64`.
-- 
--  Equivalent to `num_integer::div_ceil::<u64>(x, y)`. Panics when `y == 0`,
--  matching the source crate's behavior (the `/` and `%` operators panic on
--  division by zero).
@[spec]
def div_ceil (x : u64) (y : u64) : RustM u64 := do
  let q : u64 ← (x /? y);
  let r : u64 ← (x %? y);
  if (← (r ==? (0 : u64))) then do (pure q) else do (q +? (1 : u64))

end div_ceil_u64

