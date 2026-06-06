
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


namespace clever_108_move_one_ball

--  HumanEval/109 / CLEVER 108 — `move_one_ball(arr)`.  Can `arr` be
--  sorted in non-decreasing order via right rotations?  Empty list
--  returns true.  Spec assumes distinct elements but the algorithm
--  works generally.
@[spec]
def is_sorted_split_at (l : (RustSlice i64)) (k : usize) (i : usize) :
    RustM Bool := do
  let n : usize ← (core_models.slice.Impl.len i64 l);
  if (← ((← (i +? (1 : usize))) >=? n)) then do
    (pure true)
  else do
    let a : i64 ← l[(← ((← (i +? k)) %? n))]_?;
    let b : i64 ← l[(← ((← ((← (i +? (1 : usize))) +? k)) %? n))]_?;
    if (← (a >? b)) then do
      (pure false)
    else do
      (is_sorted_split_at l k (← (i +? (1 : usize))))
partial_fixpoint

@[spec]
def try_at (l : (RustSlice i64)) (k : usize) : RustM Bool := do
  if (← (k >=? (← (core_models.slice.Impl.len i64 l)))) then do
    (pure false)
  else do
    if (← (is_sorted_split_at l k (0 : usize))) then do
      (pure true)
    else do
      (try_at l (← (k +? (1 : usize))))
partial_fixpoint

@[spec]
def move_one_ball (arr : (RustSlice i64)) : RustM Bool := do
  if (← (core_models.slice.Impl.is_empty i64 arr)) then do
    (pure true)
  else do
    (try_at arr (0 : usize))

end clever_108_move_one_ball

