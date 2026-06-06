
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


namespace clever_052_add

--  HumanEval/53 — `add(x, y)`.  Return `x + y`.
-- 
--  Note: CLEVER's reference uses arbitrary-precision `int`.  Mapped to
--  `i64` here.  In debug builds the addition panics on overflow; in
--  release it wraps.  Both behaviours are faithful to the spec on the
--  non-overflowing domain that the property tests exercise.
@[spec]
def add (x : i64) (y : i64) : RustM i64 := do (x +? y)

end clever_052_add

