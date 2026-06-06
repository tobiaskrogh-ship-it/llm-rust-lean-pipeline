
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


namespace abs_diff_i64

--  Absolute difference of two signed integers.
-- 
--  Minimal demonstration of the conditional-subtraction pattern that avoids
--  `i64::abs` (unmodeled in the Hax Lean prelude) and `-i64::MIN` (which
--  would overflow). The proof obligation is:
--    - if branch `a > b`: show `a -? b = pure (a - b)` (no signed overflow).
--    - else branch:       show `b -? a = pure (b - a)` (no signed overflow).
--  Both subtractions are bounded by the branch condition, so the overflow
--  obligation discharges from the hypothesis.
@[spec]
def abs_diff (a : i64) (b : i64) : RustM i64 := do
  if (← (a >? b)) then do (a -? b) else do (b -? a)

end abs_diff_i64

