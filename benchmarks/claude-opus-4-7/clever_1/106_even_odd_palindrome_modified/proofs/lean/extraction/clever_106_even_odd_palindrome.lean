
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


namespace clever_106_even_odd_palindrome

--  HumanEval/107 / CLEVER 106 — `even_odd_palindrome(n)`.  Count the
--  number of palindromic integers in `1..=n` that are even and odd
--  respectively.  Returns `(even_count, odd_count)`.
@[spec]
def rev_at (n : u64) (acc : u64) : RustM u64 := do
  if (← (n ==? (0 : u64))) then do
    (pure acc)
  else do
    (rev_at
      (← (n /? (10 : u64)))
      (← ((← (acc *? (10 : u64))) +? (← (n %? (10 : u64))))))
partial_fixpoint

@[spec]
def is_palindrome (n : u64) : RustM Bool := do ((← (rev_at n (0 : u64))) ==? n)

@[spec]
def count_at (n : u64) (k : u64) (e : u64) (o : u64) :
    RustM (rust_primitives.hax.Tuple2 u64 u64) := do
  if (← (k >? n)) then do
    (pure (rust_primitives.hax.Tuple2.mk e o))
  else do
    if (← (is_palindrome k)) then do
      if (← ((← (k %? (2 : u64))) ==? (0 : u64))) then do
        (count_at n (← (k +? (1 : u64))) (← (e +? (1 : u64))) o)
      else do
        (count_at n (← (k +? (1 : u64))) e (← (o +? (1 : u64))))
    else do
      (count_at n (← (k +? (1 : u64))) e o)
partial_fixpoint

@[spec]
def even_odd_palindrome (n : u64) :
    RustM (rust_primitives.hax.Tuple2 u64 u64) := do
  (count_at n (1 : u64) (0 : u64) (0 : u64))

end clever_106_even_odd_palindrome

