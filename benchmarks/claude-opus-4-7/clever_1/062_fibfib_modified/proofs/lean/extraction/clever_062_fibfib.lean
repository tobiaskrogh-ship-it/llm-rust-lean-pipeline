
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


namespace clever_062_fibfib

--  HumanEval/63 / CLEVER 062 — `fibfib(n)`.  3-step Fibonacci-like:
--    fibfib(0) = 0, fibfib(1) = 0, fibfib(2) = 1,
--    fibfib(n) = fibfib(n-1) + fibfib(n-2) + fibfib(n-3) for n ≥ 3.
-- 
--  Tail-recursive 3-window slide (per the recursion-preference rule).
@[spec]
def fibfib_at (n : u64) (a : u64) (b : u64) (c : u64) (k : u64) :
    RustM u64 := do
  if (← (k >=? n)) then do
    (pure a)
  else do
    (fibfib_at n b c (← ((← (a +? b)) +? c)) (← (k +? (1 : u64))))
partial_fixpoint

@[spec]
def fibfib (n : u64) : RustM u64 := do
  (fibfib_at n (0 : u64) (0 : u64) (1 : u64) (0 : u64))

end clever_062_fibfib

