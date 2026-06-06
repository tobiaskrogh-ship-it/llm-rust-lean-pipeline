
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


namespace clever_105_f

--  HumanEval/106 / CLEVER 105 — `f(n)`.  Return a list of length `n`
--  where position `i` (1-indexed) is `i!` if `i` is even, else `1+2+...+i`.
@[spec]
def factorial_at (k : u64) (cur : u64) (acc : u64) : RustM u64 := do
  if (← (cur >? k)) then do
    (pure acc)
  else do
    (factorial_at k (← (cur +? (1 : u64))) (← (acc *? cur)))
partial_fixpoint

@[spec]
def sum_at (k : u64) (cur : u64) (acc : u64) : RustM u64 := do
  if (← (cur >? k)) then do
    (pure acc)
  else do
    (sum_at k (← (cur +? (1 : u64))) (← (acc +? cur)))
partial_fixpoint

@[spec]
def build_at
    (n : u64)
    (k : u64)
    (acc : (alloc.vec.Vec u64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  if (← (k >? n)) then do
    (pure acc)
  else do
    let v : u64 ←
      if (← ((← (k %? (2 : u64))) ==? (0 : u64))) then do
        (factorial_at k (1 : u64) (1 : u64))
      else do
        (sum_at k (1 : u64) (0 : u64));
    let chunk : (RustArray u64 1) := (RustArray.ofVec #v[v]);
    let acc : (alloc.vec.Vec u64 alloc.alloc.Global) ←
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global
        acc
        (← (rust_primitives.unsize chunk)));
    (build_at n (← (k +? (1 : u64))) acc)
partial_fixpoint

@[spec]
def f (n : u64) : RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  if (← (n ==? (0 : u64))) then do
    (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk)
  else do
    (build_at
      n
      (1 : u64)
      (← (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk)))

end clever_105_f

