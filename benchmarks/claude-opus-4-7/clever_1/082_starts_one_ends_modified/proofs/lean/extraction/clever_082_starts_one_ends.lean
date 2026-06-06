
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


namespace clever_082_starts_one_ends

--  HumanEval/83 / CLEVER 082 — `starts_one_ends(n)`.  Return the count
--  of `n`-digit positive integers that start *or* end with `1`.
-- 
--  Closed form: for `n == 0` the convention is `0`; for `n == 1` only
--  `1` itself qualifies; for `n ≥ 2`, inclusion–exclusion gives
--  `18 * 10^(n-2)`.
@[spec]
def pow10_at (k : u64) (acc : u64) : RustM u64 := do
  if (← (k ==? (0 : u64))) then do
    (pure acc)
  else do
    (pow10_at (← (k -? (1 : u64))) (← (acc *? (10 : u64))))
partial_fixpoint

@[spec]
def starts_one_ends (n : u64) : RustM u64 := do
  if (← (n ==? (0 : u64))) then do
    (pure (0 : u64))
  else do
    if (← (n ==? (1 : u64))) then do
      (pure (1 : u64))
    else do
      ((18 : u64) *? (← (pow10_at (← (n -? (2 : u64))) (1 : u64))))

end clever_082_starts_one_ends

