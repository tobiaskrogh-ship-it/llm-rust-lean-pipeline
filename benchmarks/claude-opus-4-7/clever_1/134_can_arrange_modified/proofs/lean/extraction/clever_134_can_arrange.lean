
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


namespace clever_134_can_arrange

--  HumanEval/135 / CLEVER 134 — `can_arrange(arr)`.  Return the largest
--  index `i` such that `arr[i] <= arr[i-1]`, or `-1` if no such index
--  exists.  Note the spec says "not greater than or equal to the
--  element immediately preceding it" → arr[i] < arr[i-1].  i64 because
--  of the -1 sentinel.
@[spec]
def scan_at (arr : (RustSlice i64)) (i : usize) (best : i64) : RustM i64 := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 arr)))) then do
    (pure best)
  else do
    if (← ((← arr[i]_?) <? (← arr[(← (i -? (1 : usize)))]_?))) then do
      (scan_at
        arr
        (← (i +? (1 : usize)))
        (← (rust_primitives.hax.cast_op i : RustM i64)))
    else do
      (scan_at arr (← (i +? (1 : usize))) best)
partial_fixpoint

@[spec]
def can_arrange (arr : (RustSlice i64)) : RustM i64 := do
  if (← ((← (core_models.slice.Impl.len i64 arr)) <? (2 : usize))) then do
    (pure (-1 : i64))
  else do
    (scan_at arr (1 : usize) (-1 : i64))

end clever_134_can_arrange

