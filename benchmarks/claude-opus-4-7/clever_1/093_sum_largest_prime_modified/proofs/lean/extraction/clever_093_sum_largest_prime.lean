
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


namespace clever_093_sum_largest_prime

--  HumanEval/94 / CLEVER 093 — `sum_largest_prime(lst)`.  Find the
--  largest prime in `lst`; return the sum of its decimal digits.
--  Return `0` for an empty list or no primes.
@[spec]
def is_prime_at (n : u64) (d : u64) : RustM Bool := do
  if (← ((← (d *? d)) >? n)) then do
    (pure true)
  else do
    if (← ((← (n %? d)) ==? (0 : u64))) then do
      (pure false)
    else do
      (is_prime_at n (← (d +? (1 : u64))))
partial_fixpoint

@[spec]
def digit_sum_at (n : u64) (acc : u64) : RustM u64 := do
  if (← (n ==? (0 : u64))) then do
    (pure acc)
  else do
    (digit_sum_at (← (n /? (10 : u64))) (← (acc +? (← (n %? (10 : u64))))))
partial_fixpoint

@[spec]
def is_prime (n : u64) : RustM Bool := do
  if (← (n <? (2 : u64))) then do (pure false) else do (is_prime_at n (2 : u64))

@[spec]
def largest_prime_at
    (l : (RustSlice u64))
    (i : usize)
    (best : u64)
    (found : Bool) :
    RustM (rust_primitives.hax.Tuple2 u64 Bool) := do
  if (← (i >=? (← (core_models.slice.Impl.len u64 l)))) then do
    (pure (rust_primitives.hax.Tuple2.mk best found))
  else do
    if
    (← ((← (is_prime (← l[i]_?)))
      &&? (← ((← (!? found)) ||? (← ((← l[i]_?) >? best)))))) then do
      (largest_prime_at l (← (i +? (1 : usize))) (← l[i]_?) true)
    else do
      (largest_prime_at l (← (i +? (1 : usize))) best found)
partial_fixpoint

@[spec]
def sum_largest_prime (lst : (RustSlice u64)) : RustM u64 := do
  let ⟨p, found⟩ ← (largest_prime_at lst (0 : usize) (0 : u64) false);
  if (← (!? found)) then do (pure (0 : u64)) else do (digit_sum_at p (0 : u64))

end clever_093_sum_largest_prime

