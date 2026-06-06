
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


namespace clever_024_factorize

--  Return the list of prime factors of n in non-decreasing order,
--  repeated by multiplicity. (n ≥ 2; for n ≤ 1 returns an empty list.)
@[spec]
def factorize_at
    (n : i64)
    (p : i64)
    (acc : (alloc.vec.Vec i64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  if (← (n <=? (1 : i64))) then do
    (pure acc)
  else do
    if (← ((← (p *? p)) >? n)) then do
      let chunk : (RustArray i64 1) := (RustArray.ofVec #v[n]);
      let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
          acc
          (← (rust_primitives.unsize chunk)));
      (pure acc)
    else do
      if (← ((← (n %? p)) ==? (0 : i64))) then do
        let chunk : (RustArray i64 1) := (RustArray.ofVec #v[p]);
        let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
          (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
            acc
            (← (rust_primitives.unsize chunk)));
        (factorize_at (← (n /? p)) p acc)
      else do
        (factorize_at n (← (p +? (1 : i64))) acc)
partial_fixpoint

@[spec]
def factorize (n : i64) : RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  if (← (n <=? (1 : i64))) then do
    (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk)
  else do
    (factorize_at
      n
      (2 : i64)
      (← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk)))

end clever_024_factorize

