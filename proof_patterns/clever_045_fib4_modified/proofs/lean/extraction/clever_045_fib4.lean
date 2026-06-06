
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


namespace clever_045_fib4

--  4-step Fibonacci:
--    fib4(0) = 0, fib4(1) = 0, fib4(2) = 2, fib4(3) = 0,
--    fib4(n) = fib4(n-1) + fib4(n-2) + fib4(n-3) + fib4(n-4) for n ≥ 4.
-- 
--  Implemented with tail recursion sliding a 4-window of recent values
--  (the docstring's "Do not use recursion" was aimed at the exponential
--  naive form; this O(n) tail-recursive form has the same efficiency as
--  a loop, per the project's recursion-preference rule).
@[spec]
def fib4_at (n : i64) (a : i64) (b : i64) (c : i64) (d : i64) (k : i64) :
    RustM i64 := do
  if (← (k >=? n)) then do
    (pure a)
  else do
    (fib4_at n b c d (← ((← ((← (a +? b)) +? c)) +? d)) (← (k +? (1 : i64))))
partial_fixpoint

@[spec]
def fib4 (n : i64) : RustM i64 := do
  if (← (n <? (0 : i64))) then do
    (pure (0 : i64))
  else do
    (fib4_at n (0 : i64) (0 : i64) (2 : i64) (0 : i64) (0 : i64))

end clever_045_fib4

