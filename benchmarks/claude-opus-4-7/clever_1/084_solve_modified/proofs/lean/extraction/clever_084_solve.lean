
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


namespace clever_084_solve

--  HumanEval/85 / CLEVER 084 — `solve(n)`.  Sum the even values at odd
--  indices of `n`.  Empty list yields 0.
@[spec]
def sum_at (n : (RustSlice i64)) (i : usize) (acc : i64) : RustM i64 := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 n)))) then do
    (pure acc)
  else do
    if
    (← ((← ((← (i %? (2 : usize))) ==? (1 : usize)))
      &&? (← ((← ((← n[i]_?) %? (2 : i64))) ==? (0 : i64))))) then do
      (sum_at n (← (i +? (1 : usize))) (← (acc +? (← n[i]_?))))
    else do
      (sum_at n (← (i +? (1 : usize))) acc)
partial_fixpoint

@[spec]
def solve (n : (RustSlice i64)) : RustM i64 := do
  (sum_at n (0 : usize) (0 : i64))

end clever_084_solve

