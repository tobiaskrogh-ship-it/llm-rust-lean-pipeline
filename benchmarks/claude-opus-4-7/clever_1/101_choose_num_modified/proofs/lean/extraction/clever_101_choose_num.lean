
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


namespace clever_101_choose_num

--  HumanEval/102 / CLEVER 101 — `choose_num(x, y)`.  Return the largest
--  even integer in `[x, y]`, or `-1` if there is none.  Returns -1 if
--  `x > y`.  i64 chosen because of the -1 sentinel.
@[spec]
def choose_num (x : i64) (y : i64) : RustM i64 := do
  if (← (x >? y)) then do
    (pure (-1 : i64))
  else do
    if (← ((← (y %? (2 : i64))) ==? (0 : i64))) then do
      (pure y)
    else do
      if (← ((← (y -? (1 : i64))) >=? x)) then do
        (y -? (1 : i64))
      else do
        (pure (-1 : i64))

end clever_101_choose_num

