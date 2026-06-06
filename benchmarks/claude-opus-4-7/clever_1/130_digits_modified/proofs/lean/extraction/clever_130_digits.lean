
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


namespace clever_130_digits

--  HumanEval/131 / CLEVER 130 — `digits(n)`.  Product of the odd digits
--  of `n`.  Return `0` if all digits are even (or n == 0).
@[spec]
def walk_at (n : u64) (acc : u64) (any_odd : Bool) : RustM u64 := do
  if (← (n ==? (0 : u64))) then do
    if any_odd then do (pure acc) else do (pure (0 : u64))
  else do
    let d : u64 ← (n %? (10 : u64));
    if (← ((← (d %? (2 : u64))) ==? (1 : u64))) then do
      (walk_at (← (n /? (10 : u64))) (← (acc *? d)) true)
    else do
      (walk_at (← (n /? (10 : u64))) acc any_odd)
partial_fixpoint

@[spec]
def digits (n : u64) : RustM u64 := do
  if (← (n ==? (0 : u64))) then do
    (pure (0 : u64))
  else do
    (walk_at n (1 : u64) false)

end clever_130_digits

