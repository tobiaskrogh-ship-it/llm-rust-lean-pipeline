
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


namespace clever_137_special_factorial

--  HumanEval/139 / CLEVER 137 — `special_factorial(n)`.  Brazilian
--  factorial: `n! * (n-1)! * (n-2)! * ... * 1!` for `n >= 1`.
--  Convention: returns 1 for n == 0.
@[spec]
def factorial_at (k : u64) (cur : u64) (acc : u64) : RustM u64 := do
  if (← (cur >? k)) then do
    (pure acc)
  else do
    (factorial_at k (← (cur +? (1 : u64))) (← (acc *? cur)))
partial_fixpoint

@[spec]
def build_at (n : u64) (k : u64) (acc : u64) : RustM u64 := do
  if (← (k >? n)) then do
    (pure acc)
  else do
    (build_at
      n
      (← (k +? (1 : u64)))
      (← (acc *? (← (factorial_at k (1 : u64) (1 : u64))))))
partial_fixpoint

@[spec]
def special_factorial (n : u64) : RustM u64 := do
  if (← (n ==? (0 : u64))) then do
    (pure (1 : u64))
  else do
    (build_at n (1 : u64) (1 : u64))

end clever_137_special_factorial

