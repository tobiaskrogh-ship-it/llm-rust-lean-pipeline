
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


namespace clever_155_right_angle_triangle

--  HumanEval/157 / CLEVER 155 — `right_angle_triangle(a, b, c)`.
--  Return true iff one of the three squared-side equations holds:
--  `a² + b² == c²`, `a² + c² == b²`, or `b² + c² == a²`.
@[spec]
def right_angle_triangle (a : u64) (b : u64) (c : u64) : RustM Bool := do
  let a2 : u64 ← (a *? a);
  let b2 : u64 ← (b *? b);
  let c2 : u64 ← (c *? c);
  if (← ((← (a2 +? b2)) ==? c2)) then do
    (pure true)
  else do
    if (← ((← (a2 +? c2)) ==? b2)) then do
      (pure true)
    else do
      ((← (b2 +? c2)) ==? a2)

end clever_155_right_angle_triangle

