
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


namespace contains_u64

--  Returns `true` iff some element of `arr` equals `target`.
-- 
--  Minimal demonstration of an existential postcondition extracted from
--  a tail-recursive linear scan. The two proof clauses are:
--    - Soundness   :  contains(arr, t) = true  →  ∃ i, i < arr.len ∧ arr[i] = t
--    - Completeness: (∃ i, i < arr.len ∧ arr[i] = t)  →  contains(arr, t) = true
--  Each direction is proved by induction on the recursion index, with the
--  existential witness in soundness extracted from the `true`-branch.
@[spec]
def contains_at (arr : (RustSlice u64)) (target : u64) (i : usize) :
    RustM Bool := do
  if (← (i >=? (← (core_models.slice.Impl.len u64 arr)))) then do
    (pure false)
  else do
    if (← ((← arr[i]_?) ==? target)) then do
      (pure true)
    else do
      (contains_at arr target (← (i +? (1 : usize))))
partial_fixpoint

@[spec]
def contains (arr : (RustSlice u64)) (target : u64) : RustM Bool := do
  (contains_at arr target (0 : usize))

end contains_u64

