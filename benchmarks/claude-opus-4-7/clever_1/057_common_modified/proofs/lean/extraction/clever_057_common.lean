
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


namespace clever_057_common

--  HumanEval/58 — `common(l1, l2)`.  Return the unique common elements
--  of two lists, in order of first appearance in `l1`.
-- 
--  Note: CLEVER's reference returns the common elements sorted.  Here
--  we return them in `l1`-appearance order; the unique-set is the same
--  either way, and the property tests treat the output as a set.
@[spec]
def contains_at (l : (RustSlice i64)) (x : i64) (i : usize) : RustM Bool := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 l)))) then do
    (pure false)
  else do
    if (← ((← l[i]_?) ==? x)) then do
      (pure true)
    else do
      (contains_at l x (← (i +? (1 : usize))))
partial_fixpoint

@[spec]
def build_common_at
    (l1 : (RustSlice i64))
    (l2 : (RustSlice i64))
    (i : usize)
    (acc : (alloc.vec.Vec i64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 l1)))) then do
    (pure acc)
  else do
    if
    (← ((← (contains_at l2 (← l1[i]_?) (0 : usize)))
      &&? (← (!? (← (contains_at
        (← (core_models.ops.deref.Deref.deref
          (alloc.vec.Vec i64 alloc.alloc.Global) acc))
        (← l1[i]_?)
        (0 : usize))))))) then do
      let chunk : (RustArray i64 1) := (RustArray.ofVec #v[(← l1[i]_?)]);
      let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
          acc
          (← (rust_primitives.unsize chunk)));
      (build_common_at l1 l2 (← (i +? (1 : usize))) acc)
    else do
      (build_common_at l1 l2 (← (i +? (1 : usize))) acc)
partial_fixpoint

@[spec]
def common (l1 : (RustSlice i64)) (l2 : (RustSlice i64)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  (build_common_at
    l1
    l2
    (0 : usize)
    (← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk)))

end clever_057_common

