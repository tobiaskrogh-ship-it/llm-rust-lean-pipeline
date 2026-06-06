
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


namespace clever_125_is_sorted

--  HumanEval/126 / CLEVER 125 — `is_sorted(lst)`.  True iff `lst` is in
--  non-decreasing order AND no value appears more than twice.  Override
--  to `u64` per docstring's "no negative numbers".
@[spec]
def count_at (l : (RustSlice u64)) (v : u64) (i : usize) (acc : u64) :
    RustM u64 := do
  if (← (i >=? (← (core_models.slice.Impl.len u64 l)))) then do
    (pure acc)
  else do
    if (← ((← l[i]_?) ==? v)) then do
      (count_at l v (← (i +? (1 : usize))) (← (acc +? (1 : u64))))
    else do
      (count_at l v (← (i +? (1 : usize))) acc)
partial_fixpoint

@[spec]
def check_at (l : (RustSlice u64)) (i : usize) : RustM Bool := do
  if (← (i >=? (← (core_models.slice.Impl.len u64 l)))) then do
    (pure true)
  else do
    let order_violation : Bool ←
      if
      (← ((← (i +? (1 : usize))) >=? (← (core_models.slice.Impl.len u64 l))))
      then do
        (pure false)
      else do
        ((← l[i]_?) >? (← l[(← (i +? (1 : usize)))]_?));
    if order_violation then do
      (pure false)
    else do
      if
      (← ((← (count_at l (← l[i]_?) (0 : usize) (0 : u64))) >? (2 : u64))) then
      do
        (pure false)
      else do
        (check_at l (← (i +? (1 : usize))))
partial_fixpoint

@[spec]
def is_sorted (lst : (RustSlice u64)) : RustM Bool := do
  (check_at lst (0 : usize))

end clever_125_is_sorted

