
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


namespace clever_120_solution

--  HumanEval/121 / CLEVER 120 — `solution(lst)`.  Sum of all odd
--  elements at even indices.
@[spec]
def sum_at (l : (RustSlice i64)) (i : usize) (acc : i64) : RustM i64 := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 l)))) then do
    (pure acc)
  else do
    if
    (← ((← ((← (i %? (2 : usize))) ==? (0 : usize)))
      &&? (← ((← ((← l[i]_?) %? (2 : i64))) !=? (0 : i64))))) then do
      (sum_at l (← (i +? (1 : usize))) (← (acc +? (← l[i]_?))))
    else do
      (sum_at l (← (i +? (1 : usize))) acc)
partial_fixpoint

@[spec]
def solution (lst : (RustSlice i64)) : RustM i64 := do
  (sum_at lst (0 : usize) (0 : i64))

end clever_120_solution

