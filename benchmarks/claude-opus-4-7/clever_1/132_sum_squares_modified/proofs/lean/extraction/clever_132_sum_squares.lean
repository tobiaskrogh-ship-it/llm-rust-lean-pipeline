
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


namespace clever_132_sum_squares

--  HumanEval/133 / CLEVER 132 — `sum_squares(lst)`.  Return the sum of
--  squares of the elements of `lst` (already integers; the "round up
--  to ceiling" step is a no-op).
@[spec]
def sum_at (l : (RustSlice i64)) (i : usize) (acc : i64) : RustM i64 := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 l)))) then do
    (pure acc)
  else do
    (sum_at
      l
      (← (i +? (1 : usize)))
      (← (acc +? (← ((← l[i]_?) *? (← l[i]_?))))))
partial_fixpoint

@[spec]
def sum_squares (lst : (RustSlice i64)) : RustM i64 := do
  (sum_at lst (0 : usize) (0 : i64))

end clever_132_sum_squares

