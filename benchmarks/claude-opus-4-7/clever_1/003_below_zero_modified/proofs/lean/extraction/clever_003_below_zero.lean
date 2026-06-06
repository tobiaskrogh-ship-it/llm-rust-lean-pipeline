
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


namespace clever_003_below_zero

--  Given a list of deposit and withdrawal operations on an account that
--  starts at zero, return true iff the balance ever falls below zero.
@[spec]
def below_zero_at (operations : (RustSlice i64)) (i : usize) (balance : i64) :
    RustM Bool := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 operations)))) then do
    (pure false)
  else do
    let new_balance : i64 ← (balance +? (← operations[i]_?));
    if (← (new_balance <? (0 : i64))) then do
      (pure true)
    else do
      (below_zero_at operations (← (i +? (1 : usize))) new_balance)
partial_fixpoint

@[spec]
def below_zero (operations : (RustSlice i64)) : RustM Bool := do
  (below_zero_at operations (0 : usize) (0 : i64))

end clever_003_below_zero

