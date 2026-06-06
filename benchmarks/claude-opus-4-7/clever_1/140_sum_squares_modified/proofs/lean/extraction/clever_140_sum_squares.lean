
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


namespace clever_140_sum_squares

--  HumanEval/142 / CLEVER 140 — `sum_squares(lst)`.  Sum the elements
--  after transforming: square if index `i % 3 == 0`; cube if `i % 4 == 0`
--  and not `i % 3 == 0`; otherwise unchanged.
@[spec]
def sum_at (l : (RustSlice i64)) (i : usize) (acc : i64) : RustM i64 := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 l)))) then do
    (pure acc)
  else do
    let v : i64 ← l[i]_?;
    let term : i64 ←
      if (← ((← (i %? (3 : usize))) ==? (0 : usize))) then do
        (v *? v)
      else do
        if (← ((← (i %? (4 : usize))) ==? (0 : usize))) then do
          ((← (v *? v)) *? v)
        else do
          (pure v);
    (sum_at l (← (i +? (1 : usize))) (← (acc +? term)))
partial_fixpoint

@[spec]
def sum_squares (lst : (RustSlice i64)) : RustM i64 := do
  (sum_at lst (0 : usize) (0 : i64))

end clever_140_sum_squares

