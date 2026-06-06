
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


namespace clever_048_modp

--  HumanEval/49 / CLEVER 048 — `modp(n, p)`.  Return `2^n mod p`.
--  `p == 0` is treated as a degenerate input and yields `0`.
-- 
--  Iterative O(n) tail recursion; the accumulator stays in `[0, p)` so
--  `acc * 2 < 2 * p`.  For `p < 2^63` no overflow.
@[spec]
def pow2_mod_at (n : u64) (p : u64) (acc : u64) (k : u64) : RustM u64 := do
  if (← (k >=? n)) then do
    (pure acc)
  else do
    (pow2_mod_at n p (← ((← (acc *? (2 : u64))) %? p)) (← (k +? (1 : u64))))
partial_fixpoint

@[spec]
def modp (n : u64) (p : u64) : RustM u64 := do
  if (← (p ==? (0 : u64))) then do
    (pure (0 : u64))
  else do
    (pow2_mod_at n p (← ((1 : u64) %? p)) (0 : u64))

end clever_048_modp

