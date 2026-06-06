
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


namespace clever_144_specialFilter

--  HumanEval/146 / CLEVER 144 — `specialFilter(nums)`.  Count elements
--  > 10 whose first AND last decimal digits are both odd (1, 3, 5, 7, 9).
@[spec]
def first_digit_at (n : i64) : RustM i64 := do
  if (← (n <? (10 : i64))) then do
    (pure n)
  else do
    (first_digit_at (← (n /? (10 : i64))))
partial_fixpoint

@[spec]
def count_at (l : (RustSlice i64)) (i : usize) (acc : i64) : RustM i64 := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 l)))) then do
    (pure acc)
  else do
    let v : i64 ← l[i]_?;
    if (← (v >? (10 : i64))) then do
      let first : i64 ← (first_digit_at v);
      let last : i64 ← (v %? (10 : i64));
      if
      (← ((← ((← (first %? (2 : i64))) ==? (1 : i64)))
        &&? (← ((← (last %? (2 : i64))) ==? (1 : i64))))) then do
        (count_at l (← (i +? (1 : usize))) (← (acc +? (1 : i64))))
      else do
        (count_at l (← (i +? (1 : usize))) acc)
    else do
      (count_at l (← (i +? (1 : usize))) acc)
partial_fixpoint

@[spec]
def specialFilter (nums : (RustSlice i64)) : RustM i64 := do
  (count_at nums (0 : usize) (0 : i64))

end clever_144_specialFilter

