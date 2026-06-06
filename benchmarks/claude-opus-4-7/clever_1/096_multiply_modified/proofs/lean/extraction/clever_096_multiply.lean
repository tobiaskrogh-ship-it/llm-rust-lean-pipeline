
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


namespace clever_096_multiply

--  HumanEval/97 / CLEVER 096 — `multiply(a, b)`.  Product of the decimal
--  unit digits of `|a|` and `|b|`.  Inputs are arbitrary integers (i64).
@[spec]
def multiply (a : i64) (b : i64) : RustM i64 := do
  let aa : i64 ← if (← (a <? (0 : i64))) then do (-? a) else do (pure a);
  let bb : i64 ← if (← (b <? (0 : i64))) then do (-? b) else do (pure b);
  ((← (aa %? (10 : i64))) *? (← (bb %? (10 : i64))))

end clever_096_multiply

