
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


namespace clever_095_count_up_to

--  HumanEval/96 / CLEVER 095 — `count_up_to(n)`.  Return the list of
--  primes strictly less than `n`, in ascending order.  Empty if n < 2.
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
def is_prime (n : u64) : RustM Bool := do
  if (← (n <? (2 : u64))) then do (pure false) else do (is_prime_at n (2 : u64))

@[spec]
def build_at
    (n : u64)
    (k : u64)
    (acc : (alloc.vec.Vec u64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  if (← (k >=? n)) then do
    (pure acc)
  else do
    if (← (is_prime k)) then do
      let acc : (alloc.vec.Vec u64 alloc.alloc.Global) := acc;
      let chunk : (RustArray u64 1) := (RustArray.ofVec #v[k]);
      let acc : (alloc.vec.Vec u64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global
          acc
          (← (rust_primitives.unsize chunk)));
      (build_at n (← (k +? (1 : u64))) acc)
    else do
      (build_at n (← (k +? (1 : u64))) acc)
partial_fixpoint

@[spec]
def count_up_to (n : u64) : RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  (build_at
    n
    (0 : u64)
    (← (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk)))

end clever_095_count_up_to

