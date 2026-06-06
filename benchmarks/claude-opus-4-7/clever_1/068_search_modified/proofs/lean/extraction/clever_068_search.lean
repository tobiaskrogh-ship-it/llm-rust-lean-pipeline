
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


namespace clever_068_search

--  HumanEval/69 / CLEVER 068 — `search(numbers)`.  Return the largest
--  integer that is greater than zero and whose frequency in `numbers`
--  is at least its own value.  If no such integer exists, return `0`
--  (since the spec requires the answer to be `> 0`, `0` is a safe
--  sentinel for "no answer").
@[spec]
def count_occurrences (l : (RustSlice u64)) (v : u64) (i : usize) :
    RustM u64 := do
  if (← (i >=? (← (core_models.slice.Impl.len u64 l)))) then do
    (pure (0 : u64))
  else do
    if (← ((← l[i]_?) ==? v)) then do
      ((1 : u64) +? (← (count_occurrences l v (← (i +? (1 : usize))))))
    else do
      (count_occurrences l v (← (i +? (1 : usize))))
partial_fixpoint

@[spec]
def search_at (l : (RustSlice u64)) (i : usize) (best : u64) : RustM u64 := do
  if (← (i >=? (← (core_models.slice.Impl.len u64 l)))) then do
    (pure best)
  else do
    let v : u64 ← l[i]_?;
    if (← ((← (v >? (0 : u64))) &&? (← (v >? best)))) then do
      let c : u64 ← (count_occurrences l v (0 : usize));
      if (← (c >=? v)) then do
        (search_at l (← (i +? (1 : usize))) v)
      else do
        (search_at l (← (i +? (1 : usize))) best)
    else do
      (search_at l (← (i +? (1 : usize))) best)
partial_fixpoint

@[spec]
def search (numbers : (RustSlice u64)) : RustM u64 := do
  (search_at numbers (0 : usize) (0 : u64))

end clever_068_search

