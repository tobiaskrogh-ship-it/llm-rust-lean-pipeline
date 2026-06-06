
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


namespace clever_072_smallest_change

--  HumanEval/73 / CLEVER 072 — `smallest_change(arr)`.  Return the
--  minimum number of single-element changes needed to make `arr` a
--  palindrome.  Each mismatch at position `(i, n-1-i)` (for `i < n/2`)
--  can be fixed with one change of either element.
@[spec]
def count_mismatches_at (arr : (RustSlice i64)) (i : usize) (acc : i64) :
    RustM i64 := do
  let n : usize ← (core_models.slice.Impl.len i64 arr);
  if (← (i >=? (← (n /? (2 : usize))))) then do
    (pure acc)
  else do
    if
    (← ((← arr[i]_?) !=? (← arr[(← ((← (n -? (1 : usize))) -? i))]_?))) then do
      (count_mismatches_at arr (← (i +? (1 : usize))) (← (acc +? (1 : i64))))
    else do
      (count_mismatches_at arr (← (i +? (1 : usize))) acc)
partial_fixpoint

@[spec]
def smallest_change (arr : (RustSlice i64)) : RustM i64 := do
  (count_mismatches_at arr (0 : usize) (0 : i64))

end clever_072_smallest_change

