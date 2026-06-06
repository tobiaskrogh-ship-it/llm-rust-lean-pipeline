
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


namespace clever_119_maximum

--  HumanEval/120 / CLEVER 119 — `maximum(arr, k)`.  Return a sorted-
--  ascending list of the `k` largest values in `arr`.  If `k == 0` or
--  `arr` is empty, return `[]`.  If `k >= arr.len()`, return a sorted
--  copy of `arr`.
@[spec]
def insert_asc_at
    (v : (RustSlice u64))
    (x : u64)
    (i : usize)
    (done : Bool)
    (acc : (alloc.vec.Vec u64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  if (← (i >=? (← (core_models.slice.Impl.len u64 v)))) then do
    if done then do
      (pure acc)
    else do
      let acc : (alloc.vec.Vec u64 alloc.alloc.Global) := acc;
      let chunk : (RustArray u64 1) := (RustArray.ofVec #v[x]);
      let acc : (alloc.vec.Vec u64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global
          acc
          (← (rust_primitives.unsize chunk)));
      (pure acc)
  else do
    let acc : (alloc.vec.Vec u64 alloc.alloc.Global) := acc;
    if (← ((← (!? done)) &&? (← ((← v[i]_?) >=? x)))) then do
      let chunk : (RustArray u64 2) := (RustArray.ofVec #v[x, (← v[i]_?)]);
      let acc : (alloc.vec.Vec u64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global
          acc
          (← (rust_primitives.unsize chunk)));
      (insert_asc_at v x (← (i +? (1 : usize))) true acc)
    else do
      let chunk : (RustArray u64 1) := (RustArray.ofVec #v[(← v[i]_?)]);
      let acc : (alloc.vec.Vec u64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global
          acc
          (← (rust_primitives.unsize chunk)));
      (insert_asc_at v x (← (i +? (1 : usize))) done acc)
partial_fixpoint

@[spec]
def tail_from
    (s : (RustSlice u64))
    (start : usize)
    (acc : (alloc.vec.Vec u64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  if (← (start >=? (← (core_models.slice.Impl.len u64 s)))) then do
    (pure acc)
  else do
    let acc : (alloc.vec.Vec u64 alloc.alloc.Global) := acc;
    let chunk : (RustArray u64 1) := (RustArray.ofVec #v[(← s[start]_?)]);
    let acc : (alloc.vec.Vec u64 alloc.alloc.Global) ←
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global
        acc
        (← (rust_primitives.unsize chunk)));
    (tail_from s (← (start +? (1 : usize))) acc)
partial_fixpoint

@[spec]
def insert_asc (v : (alloc.vec.Vec u64 alloc.alloc.Global)) (x : u64) :
    RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  (insert_asc_at
    (← (core_models.ops.deref.Deref.deref
      (alloc.vec.Vec u64 alloc.alloc.Global) v))
    x
    (0 : usize)
    false
    (← (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk)))

@[spec]
def sort_at
    (l : (RustSlice u64))
    (i : usize)
    (s : (alloc.vec.Vec u64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  if (← (i >=? (← (core_models.slice.Impl.len u64 l)))) then do
    (pure s)
  else do
    (sort_at l (← (i +? (1 : usize))) (← (insert_asc s (← l[i]_?))))
partial_fixpoint

@[spec]
def maximum (arr : (RustSlice u64)) (k : u64) :
    RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  if
  (← ((← (k ==? (0 : u64))) ||? (← (core_models.slice.Impl.is_empty u64 arr))))
  then do
    (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk)
  else do
    let sorted : (alloc.vec.Vec u64 alloc.alloc.Global) ←
      (sort_at
        arr
        (0 : usize)
        (← (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk)));
    let n : u64 ←
      (rust_primitives.hax.cast_op
        (← (alloc.vec.Impl_1.len u64 alloc.alloc.Global sorted)) :
        RustM u64);
    let start : usize ←
      if (← (k >=? n)) then do
        (pure (0 : usize))
      else do
        (rust_primitives.hax.cast_op (← (n -? k)) : RustM usize);
    (tail_from
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u64 alloc.alloc.Global) sorted))
      start
      (← (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk)))

end clever_119_maximum

