
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


namespace clever_089_next_smallest

--  HumanEval/90 / CLEVER 089 — `next_smallest(lst)`.  Return the
--  second-smallest *unique* element of `lst`, or `None` if there's no
--  such element (empty, single element, or all values equal).
@[spec]
def min_at (l : (RustSlice i64)) (i : usize) (best : i64) (found : Bool) :
    RustM (rust_primitives.hax.Tuple2 i64 Bool) := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 l)))) then do
    (pure (rust_primitives.hax.Tuple2.mk best found))
  else do
    if (← ((← (!? found)) ||? (← ((← l[i]_?) <? best)))) then do
      (min_at l (← (i +? (1 : usize))) (← l[i]_?) true)
    else do
      (min_at l (← (i +? (1 : usize))) best found)
partial_fixpoint

@[spec]
def min_above_at
    (l : (RustSlice i64))
    (floor : i64)
    (i : usize)
    (best : i64)
    (found : Bool) :
    RustM (rust_primitives.hax.Tuple2 i64 Bool) := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 l)))) then do
    (pure (rust_primitives.hax.Tuple2.mk best found))
  else do
    if
    (← ((← ((← l[i]_?) >? floor))
      &&? (← ((← (!? found)) ||? (← ((← l[i]_?) <? best)))))) then do
      (min_above_at l floor (← (i +? (1 : usize))) (← l[i]_?) true)
    else do
      (min_above_at l floor (← (i +? (1 : usize))) best found)
partial_fixpoint

@[spec]
def next_smallest (lst : (RustSlice i64)) :
    RustM (core_models.option.Option i64) := do
  let ⟨m1, f1⟩ ← (min_at lst (0 : usize) (0 : i64) false);
  if (← (!? f1)) then do
    (pure core_models.option.Option.None)
  else do
    let ⟨m2, f2⟩ ← (min_above_at lst m1 (0 : usize) (0 : i64) false);
    if f2 then do
      (pure (core_models.option.Option.Some m2))
    else do
      (pure core_models.option.Option.None)

end clever_089_next_smallest

