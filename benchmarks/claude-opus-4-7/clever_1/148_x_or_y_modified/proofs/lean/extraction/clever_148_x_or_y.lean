
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


namespace clever_148_x_or_y

--  HumanEval/150 / CLEVER 148 — `x_or_y(n, x, y)`.  Return `x` if `n` is
--  prime, else `y`.  Canonical CLEVER signature has a typo
--  (`int n: i64, int x: i64, int y: i64`); we interpret it as the
--  natural three-argument shape.  i64 to match canonical despite
--  non-negative spec for `n` (so we don't lose flexibility on x, y).
@[spec]
def is_prime_at (n : i64) (d : i64) : RustM Bool := do
  if (← ((← (d *? d)) >? n)) then do
    (pure true)
  else do
    if (← ((← (n %? d)) ==? (0 : i64))) then do
      (pure false)
    else do
      (is_prime_at n (← (d +? (1 : i64))))
partial_fixpoint

@[spec]
def is_prime (n : i64) : RustM Bool := do
  if (← (n <? (2 : i64))) then do (pure false) else do (is_prime_at n (2 : i64))

@[spec]
def x_or_y (n : i64) (x : i64) (y : i64) : RustM i64 := do
  if (← (is_prime n)) then do (pure x) else do (pure y)

end clever_148_x_or_y

