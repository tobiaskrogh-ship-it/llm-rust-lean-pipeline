
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


namespace clever_074_is_multiply_prime

--  HumanEval/75 / CLEVER 074 — `is_multiply_prime(a)`.  Return true iff
--  `a` is a product of exactly three primes (with repetition).
--  Examples: `8 = 2*2*2`, `30 = 2*3*5`, `12 = 2*2*3` → true;
--  `4 = 2*2`, `6 = 2*3`, `24 = 2*2*2*3` → false.
@[spec]
def smallest_prime_at (m : u64) (d : u64) : RustM u64 := do
  if (← ((← (d *? d)) >? m)) then do
    (pure m)
  else do
    if (← ((← (m %? d)) ==? (0 : u64))) then do
      (pure d)
    else do
      (smallest_prime_at m (← (d +? (1 : u64))))
partial_fixpoint

@[spec]
def is_multiply_prime (a : u64) : RustM Bool := do
  if (← (a <? (8 : u64))) then do
    (pure false)
  else do
    let p1 : u64 ← (smallest_prime_at a (2 : u64));
    let q1 : u64 ← (a /? p1);
    if (← (q1 <? (2 : u64))) then do
      (pure false)
    else do
      let p2 : u64 ← (smallest_prime_at q1 (2 : u64));
      let q2 : u64 ← (q1 /? p2);
      if (← (q2 <? (2 : u64))) then do
        (pure false)
      else do
        let p3 : u64 ← (smallest_prime_at q2 (2 : u64));
        (p3 ==? q2)

end clever_074_is_multiply_prime

