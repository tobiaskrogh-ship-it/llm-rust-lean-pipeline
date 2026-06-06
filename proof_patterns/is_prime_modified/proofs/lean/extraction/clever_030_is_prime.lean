
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


namespace clever_030_is_prime

--  Return true iff n is prime. (Return type corrected from CLEVER's
--  auto-defaulted `u64` to `bool` to match the docstring.)
@[spec]
def has_divisor_at (n : u64) (d : u64) : RustM Bool := do
  if (← ((← (d *? d)) >? n)) then do
    (pure false)
  else do
    if (← ((← (n %? d)) ==? (0 : u64))) then do
      (pure true)
    else do
      (has_divisor_at n (← (d +? (1 : u64))))
partial_fixpoint

@[spec]
def is_prime (n : u64) : RustM Bool := do
  if (← (n <? (2 : u64))) then do
    (pure false)
  else do
    (!? (← (has_divisor_at n (2 : u64))))

end clever_030_is_prime

