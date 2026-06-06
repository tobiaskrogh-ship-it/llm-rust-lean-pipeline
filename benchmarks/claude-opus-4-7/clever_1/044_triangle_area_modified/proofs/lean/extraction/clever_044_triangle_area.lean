
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


namespace clever_044_triangle_area

--  Area of a triangle given base length `a` and height `h`.
--  Integer arithmetic — fractional results are truncated to floor.
@[spec]
def triangle_area (a : i64) (h : i64) : RustM i64 := do
  ((← (a *? h)) /? (2 : i64))

end clever_044_triangle_area

