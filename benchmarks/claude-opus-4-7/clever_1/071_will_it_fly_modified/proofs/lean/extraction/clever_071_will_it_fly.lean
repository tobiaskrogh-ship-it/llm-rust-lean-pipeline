
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


namespace clever_071_will_it_fly

--  HumanEval/72 / CLEVER 071 — `will_it_fly(q, w)`.  Return true iff
--  `q` is a palindromic list AND `sum(q) ≤ w`.  Empty list is trivially
--  palindromic; its sum is 0.
@[spec]
def sum_at (l : (RustSlice i64)) (i : usize) (acc : i64) : RustM i64 := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 l)))) then do
    (pure acc)
  else do
    (sum_at l (← (i +? (1 : usize))) (← (acc +? (← l[i]_?))))
partial_fixpoint

@[spec]
def is_palindrome_at (q : (RustSlice i64)) (i : usize) (j : usize) :
    RustM Bool := do
  if (← (i >=? j)) then do
    (pure true)
  else do
    if (← ((← q[i]_?) !=? (← q[j]_?))) then do
      (pure false)
    else do
      (is_palindrome_at q (← (i +? (1 : usize))) (← (j -? (1 : usize))))
partial_fixpoint

@[spec]
def will_it_fly (q : (RustSlice i64)) (w : i64) : RustM Bool := do
  if (← ((← (sum_at q (0 : usize) (0 : i64))) >? w)) then do
    (pure false)
  else do
    if (← (core_models.slice.Impl.is_empty i64 q)) then do
      (pure true)
    else do
      (is_palindrome_at
        q
        (0 : usize)
        (← ((← (core_models.slice.Impl.len i64 q)) -? (1 : usize))))

end clever_071_will_it_fly

