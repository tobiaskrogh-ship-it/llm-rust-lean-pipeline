
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


namespace clever_099_make_a_pile

--  HumanEval/100 / CLEVER 099 — `make_a_pile(n)`.  Return `[n, n+2,
--  n+4, ..., n + 2*(n-1)]` (n levels, each adds 2 to the previous).
@[spec]
def build_at
    (n : u64)
    (k : u64)
    (acc : (alloc.vec.Vec u64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  if (← (k >=? n)) then do
    (pure acc)
  else do
    let acc : (alloc.vec.Vec u64 alloc.alloc.Global) := acc;
    let chunk : (RustArray u64 1) :=
      (RustArray.ofVec #v[(← (n +? (← ((2 : u64) *? k))))]);
    let acc : (alloc.vec.Vec u64 alloc.alloc.Global) ←
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global
        acc
        (← (rust_primitives.unsize chunk)));
    (build_at n (← (k +? (1 : u64))) acc)
partial_fixpoint

@[spec]
def make_a_pile (n : u64) : RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  if (← (n ==? (0 : u64))) then do
    (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk)
  else do
    (build_at
      n
      (0 : u64)
      (← (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk)))

end clever_099_make_a_pile

