
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


namespace clever_076_iscube

--  HumanEval/77 — `iscube(n)`.  Return true iff `n` is a perfect cube.
--  Negative inputs map by `-n = m^3` ⇔ `n = (-m)^3`, so a negative
--  `n` is a cube iff `|n|` is.
@[spec]
def cube_walks_to (n : i64) (k : i64) : RustM Bool := do
  let cube : i64 ← ((← (k *? k)) *? k);
  if (← (cube ==? n)) then do
    (pure true)
  else do
    if (← (cube >? n)) then do
      (pure false)
    else do
      (cube_walks_to n (← (k +? (1 : i64))))
partial_fixpoint

@[spec]
def iscube (n : i64) : RustM Bool := do
  if (← (n <? (0 : i64))) then do
    (cube_walks_to (← (-? n)) (0 : i64))
  else do
    (cube_walks_to n (0 : i64))

end clever_076_iscube

