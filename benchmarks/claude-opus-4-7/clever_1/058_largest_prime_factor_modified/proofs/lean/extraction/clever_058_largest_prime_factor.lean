
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


namespace clever_058_largest_prime_factor

--  HumanEval/59 / CLEVER 058 — `largest_prime_factor(n)`.  Return the
--  largest prime factor of `n` (`n > 1`).  For `n ≤ 1` the function
--  returns `1` as a degenerate sentinel.
-- 
--  Strategy: repeatedly extract the smallest prime divisor and divide
--  it out fully.  When `n` reaches `1`, the last divisor extracted is
--  the largest prime factor.
@[spec]
def smallest_divisor_at (m : u64) (d : u64) : RustM u64 := do
  if (← ((← (d *? d)) >? m)) then do
    (pure m)
  else do
    if (← ((← (m %? d)) ==? (0 : u64))) then do
      (pure d)
    else do
      (smallest_divisor_at m (← (d +? (1 : u64))))
partial_fixpoint

@[spec]
def strip_factor (n : u64) (p : u64) : RustM u64 := do
  if (← ((← (n %? p)) ==? (0 : u64))) then do
    (strip_factor (← (n /? p)) p)
  else do
    (pure n)
partial_fixpoint

@[spec]
def largest_prime_at (n : u64) (current_largest : u64) : RustM u64 := do
  if (← (n <=? (1 : u64))) then do
    (pure current_largest)
  else do
    let p : u64 ← (smallest_divisor_at n (2 : u64));
    let stripped : u64 ← (strip_factor n p);
    (largest_prime_at stripped p)
partial_fixpoint

@[spec]
def largest_prime_factor (n : u64) : RustM u64 := do
  if (← (n <=? (1 : u64))) then do
    (pure (1 : u64))
  else do
    (largest_prime_at n (1 : u64))

end clever_058_largest_prime_factor

