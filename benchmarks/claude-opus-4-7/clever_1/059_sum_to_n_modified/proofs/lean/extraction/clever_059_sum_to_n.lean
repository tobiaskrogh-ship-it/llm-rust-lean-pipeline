
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


namespace clever_059_sum_to_n

--  HumanEval/60 / CLEVER 059 — `sum_to_n(n)`.  Return `1 + 2 + ... + n`.
--  By convention `sum_to_n(0) = 0`.
-- 
--  Tail-recursive accumulator (per the project's recursion-preference rule).
@[spec]
def sum_to_n_at (n : u64) (k : u64) (acc : u64) : RustM u64 := do
  if (← (k >? n)) then do
    (pure acc)
  else do
    (sum_to_n_at n (← (k +? (1 : u64))) (← (acc +? k)))
partial_fixpoint

@[spec]
def sum_to_n (n : u64) : RustM u64 := do
  if (← (n ==? (0 : u64))) then do
    (pure (0 : u64))
  else do
    (sum_to_n_at n (1 : u64) (0 : u64))

end clever_059_sum_to_n

