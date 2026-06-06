
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


namespace clever_149_double_the_difference

--  HumanEval/151 / CLEVER 149 — `double_the_difference(numbers)`.  Sum
--  of squares of the positive odd integers in `numbers`.  Negative
--  values are ignored.  (All inputs are already integers here.)
@[spec]
def sum_at (l : (RustSlice i64)) (i : usize) (acc : i64) : RustM i64 := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 l)))) then do
    (pure acc)
  else do
    if
    (← ((← ((← l[i]_?) >? (0 : i64)))
      &&? (← ((← ((← l[i]_?) %? (2 : i64))) ==? (1 : i64))))) then do
      (sum_at
        l
        (← (i +? (1 : usize)))
        (← (acc +? (← ((← l[i]_?) *? (← l[i]_?))))))
    else do
      (sum_at l (← (i +? (1 : usize))) acc)
partial_fixpoint

@[spec]
def double_the_difference (numbers : (RustSlice i64)) : RustM i64 := do
  (sum_at numbers (0 : usize) (0 : i64))

end clever_149_double_the_difference

