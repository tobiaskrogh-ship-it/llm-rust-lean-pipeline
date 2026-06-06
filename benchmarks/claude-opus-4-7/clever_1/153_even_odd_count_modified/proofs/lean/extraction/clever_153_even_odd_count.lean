
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


namespace clever_153_even_odd_count

--  HumanEval/155 / CLEVER 153 — `even_odd_count(num)`.  Return
--  `(even_count, odd_count)` of the decimal digits of `num`.  For
--  `num == 0` we count one digit `0`, which is even → `(1, 0)`.
@[spec]
def count_at (n : u64) (e : u64) (o : u64) :
    RustM (rust_primitives.hax.Tuple2 u64 u64) := do
  if (← (n ==? (0 : u64))) then do
    (pure (rust_primitives.hax.Tuple2.mk e o))
  else do
    if (← ((← ((← (n %? (10 : u64))) %? (2 : u64))) ==? (0 : u64))) then do
      (count_at (← (n /? (10 : u64))) (← (e +? (1 : u64))) o)
    else do
      (count_at (← (n /? (10 : u64))) e (← (o +? (1 : u64))))
partial_fixpoint

@[spec]
def even_odd_count (num : u64) :
    RustM (rust_primitives.hax.Tuple2 u64 u64) := do
  if (← (num ==? (0 : u64))) then do
    (pure (rust_primitives.hax.Tuple2.mk (1 : u64) (0 : u64)))
  else do
    (count_at num (0 : u64) (0 : u64))

end clever_153_even_odd_count

