
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


namespace clever_075_is_simple_power

--  HumanEval/76 / CLEVER 075 — `is_simple_power(x, n)`.  Return true iff
--  there exists `k ≥ 0` with `n^k == x`.  Conventions:
--  `is_simple_power(1, n) == true` (since `n^0 = 1`);
--  `is_simple_power(x, 1) == (x == 1)`.
-- 
--  Tail-recursively multiplies a running power of `n` until it meets
--  or exceeds `x`; `cur ≤ x` is the termination measure.
@[spec]
def power_walks_to (x : u64) (n : u64) (cur : u64) : RustM Bool := do
  if (← (cur ==? x)) then do
    (pure true)
  else do
    if (← (cur >? x)) then do
      (pure false)
    else do
      (power_walks_to x n (← (cur *? n)))
partial_fixpoint

@[spec]
def is_simple_power (x : u64) (n : u64) : RustM Bool := do
  if (← (x ==? (1 : u64))) then do
    (pure true)
  else do
    if (← ((← (x ==? (0 : u64))) ||? (← (n ==? (0 : u64))))) then do
      (pure false)
    else do
      if (← (n ==? (1 : u64))) then do
        (pure false)
      else do
        (power_walks_to x n n)

end clever_075_is_simple_power

