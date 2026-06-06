
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


namespace clever_034_max_element

--  Return the maximum element in the list. For the empty list, returns 0.
@[spec]
def max_at (l : (RustSlice i64)) (i : usize) (m : i64) : RustM i64 := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 l)))) then do
    (pure m)
  else do
    if (← ((← l[i]_?) >? m)) then do
      (max_at l (← (i +? (1 : usize))) (← l[i]_?))
    else do
      (max_at l (← (i +? (1 : usize))) m)
partial_fixpoint

@[spec]
def max_element (l : (RustSlice i64)) : RustM i64 := do
  if (← (core_models.slice.Impl.is_empty i64 l)) then do
    (pure (0 : i64))
  else do
    (max_at l (1 : usize) (← l[(0 : usize)]_?))

end clever_034_max_element

