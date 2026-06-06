
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


namespace clever_023_largest_divisor

--  For a given number n ≥ 2, find the largest divisor of n that is
--  strictly less than n. For n ≤ 1 returns 0 (no proper divisor exists).
@[spec]
def largest_divisor_at (n : i64) (d : i64) : RustM i64 := do
  if (← (d <=? (0 : i64))) then do
    (pure (1 : i64))
  else do
    if (← ((← (n %? d)) ==? (0 : i64))) then do
      (pure d)
    else do
      (largest_divisor_at n (← (d -? (1 : i64))))
partial_fixpoint

@[spec]
def largest_divisor (n : i64) : RustM i64 := do
  if (← (n <=? (1 : i64))) then do
    (pure (0 : i64))
  else do
    (largest_divisor_at n (← (n -? (1 : i64))))

end clever_023_largest_divisor

