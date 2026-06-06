
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


namespace clever_038_prime_fib

--  Return the n-th prime Fibonacci number (n is 0-indexed: 0 → 2, 1 → 3,
--  2 → 5, 3 → 13, …). CLEVER's Note(George) flags this depends on an
--  open conjecture about infinitely many prime Fibs.
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
def is_prime_u64 (n : u64) : RustM Bool := do
  if (← (n <? (2 : u64))) then do
    (pure false)
  else do
    (!? (← (has_divisor_at n (2 : u64))))

@[spec]
def prime_fib_at (target : u64) (a : u64) (b : u64) (count : u64) :
    RustM u64 := do
  let c : u64 ← (a +? b);
  if (← (is_prime_u64 c)) then do
    if (← (count ==? target)) then do
      (pure c)
    else do
      (prime_fib_at target b c (← (count +? (1 : u64))))
  else do
    (prime_fib_at target b c count)
partial_fixpoint

@[spec]
def prime_fib (n : u64) : RustM u64 := do
  (prime_fib_at n (1 : u64) (1 : u64) (0 : u64))

end clever_038_prime_fib

