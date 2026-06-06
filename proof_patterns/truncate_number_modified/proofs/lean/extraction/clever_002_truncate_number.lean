
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


namespace clever_002_truncate_number

--  Given a non-negative integer interpreted as a fixed-point number with
--  3 fractional digits (so `1000` represents the float `1.0`), return the
--  fractional part — i.e. the value strictly less than `1000`.
-- 
--  Note: CLEVER's reference signature is `(number: float) -> float`,
--  returning `number - floor(number)`. Translated to a `u64` fixed-point
--  formulation because the Hax Lean prelude has gaps in `f64` support
--  (missing `Impl.abs`, `PartialOrd`, `Neg`, and a broken `Sub.sub` for
--  non-integer types). The body has no iteration, so no recursive form
--  applies — the function is a single arithmetic expression.
@[spec]
def truncate_number (number : u64) : RustM u64 := do (number %? (1000 : u64))

end clever_002_truncate_number

