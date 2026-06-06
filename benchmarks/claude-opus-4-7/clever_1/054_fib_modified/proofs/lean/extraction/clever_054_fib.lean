
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


namespace clever_054_fib

--  HumanEval/55 / CLEVER 054 — `fib(n)`.  Standard Fibonacci:
--  `fib(0) = 0`, `fib(1) = 1`, `fib(n) = fib(n-1) + fib(n-2)` for `n ≥ 2`.
-- 
--  O(n) tail recursion sliding a 2-window (per the project's
--  recursion-preference rule).
@[spec]
def fib_at (n : u64) (a : u64) (b : u64) (k : u64) : RustM u64 := do
  if (← (k >=? n)) then do
    (pure a)
  else do
    (fib_at n b (← (a +? b)) (← (k +? (1 : u64))))
partial_fixpoint

@[spec]
def fib (n : u64) : RustM u64 := do (fib_at n (0 : u64) (1 : u64) (0 : u64))

end clever_054_fib

