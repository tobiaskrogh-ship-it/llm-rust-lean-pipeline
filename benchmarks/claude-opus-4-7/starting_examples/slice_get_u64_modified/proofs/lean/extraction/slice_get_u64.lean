
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


namespace slice_get_u64

--  Returns `numbers[index]` if `index < numbers.len()`, else 0.
-- 
--  Minimal demonstration of slice indexing with explicit bound discharge:
--  the `numbers[index]` access extracts (via Hax) to the partial operator
--  `numbers[index]_?`, and the proof has to show the index is in bounds
--  in the then-branch.
@[spec]
def slice_get (numbers : (RustSlice u64)) (index : usize) : RustM u64 := do
  if (← (index <? (← (core_models.slice.Impl.len u64 numbers)))) then do
    numbers[index]_?
  else do
    (pure (0 : u64))

end slice_get_u64

