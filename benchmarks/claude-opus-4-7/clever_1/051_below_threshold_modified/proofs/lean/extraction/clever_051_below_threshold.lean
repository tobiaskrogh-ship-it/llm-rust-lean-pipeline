
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


namespace clever_051_below_threshold

--  HumanEval/52 — `below_threshold(l, t)`.  Return true iff every
--  element of `l` is strictly less than `t`.  The empty list vacuously
--  satisfies the property.
@[spec]
def all_below_at (l : (RustSlice i64)) (t : i64) (i : usize) : RustM Bool := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 l)))) then do
    (pure true)
  else do
    if (← ((← l[i]_?) >=? t)) then do
      (pure false)
    else do
      (all_below_at l t (← (i +? (1 : usize))))
partial_fixpoint

@[spec]
def below_threshold (l : (RustSlice i64)) (t : i64) : RustM Bool := do
  (all_below_at l t (0 : usize))

end clever_051_below_threshold

