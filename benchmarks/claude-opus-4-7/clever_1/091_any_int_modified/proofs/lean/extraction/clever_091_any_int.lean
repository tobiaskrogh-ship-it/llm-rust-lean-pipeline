
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


namespace clever_091_any_int

--  HumanEval/92 / CLEVER 091 — `any_int(a, b, c)`.  Return true iff one
--  of `a, b, c` equals the sum of the other two.  Inputs are integers;
--  `i64` allows negative inputs the spec mentions ("all numbers are integers").
@[spec]
def any_int (a : i64) (b : i64) (c : i64) : RustM Bool := do
  ((← ((← (a ==? (← (b +? c)))) ||? (← (b ==? (← (a +? c))))))
    ||? (← (c ==? (← (a +? b)))))

end clever_091_any_int

