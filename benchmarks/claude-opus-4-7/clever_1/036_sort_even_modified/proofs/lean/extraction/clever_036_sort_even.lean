
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


namespace clever_036_sort_even

--  Return a list identical to `l` at odd indices, with values at even
--  indices replaced by those same values in ascending order. (Return type
--  widened to `Vec<i64>` to match the docstring.)
@[spec]
def insert_sorted_at
    (v : (RustSlice i64))
    (i : usize)
    (x : i64)
    (inserted : Bool)
    (acc : (alloc.vec.Vec i64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 v)))) then do
    let acc : (alloc.vec.Vec i64 alloc.alloc.Global) := acc;
    let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
      if (← (!? inserted)) then do
        let chunk : (RustArray i64 1) := (RustArray.ofVec #v[x]);
        let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
          (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
            acc
            (← (rust_primitives.unsize chunk)));
        (pure acc)
      else do
        (pure acc);
    (pure acc)
  else do
    if (← ((← (!? inserted)) &&? (← ((← v[i]_?) >=? x)))) then do
      let acc : (alloc.vec.Vec i64 alloc.alloc.Global) := acc;
      let chunk : (RustArray i64 2) := (RustArray.ofVec #v[x, (← v[i]_?)]);
      let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
          acc
          (← (rust_primitives.unsize chunk)));
      (insert_sorted_at v (← (i +? (1 : usize))) x true acc)
    else do
      let acc : (alloc.vec.Vec i64 alloc.alloc.Global) := acc;
      let chunk : (RustArray i64 1) := (RustArray.ofVec #v[(← v[i]_?)]);
      let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
          acc
          (← (rust_primitives.unsize chunk)));
      (insert_sorted_at v (← (i +? (1 : usize))) x inserted acc)
partial_fixpoint

@[spec]
def rebuild_at
    (l : (RustSlice i64))
    (sorted : (RustSlice i64))
    (i : usize)
    (j : usize)
    (acc : (alloc.vec.Vec i64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 l)))) then do
    (pure acc)
  else do
    if (← ((← (i %? (2 : usize))) ==? (0 : usize))) then do
      let acc : (alloc.vec.Vec i64 alloc.alloc.Global) := acc;
      let chunk : (RustArray i64 1) := (RustArray.ofVec #v[(← sorted[j]_?)]);
      let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
          acc
          (← (rust_primitives.unsize chunk)));
      (rebuild_at l sorted (← (i +? (1 : usize))) (← (j +? (1 : usize))) acc)
    else do
      let acc : (alloc.vec.Vec i64 alloc.alloc.Global) := acc;
      let chunk : (RustArray i64 1) := (RustArray.ofVec #v[(← l[i]_?)]);
      let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
          acc
          (← (rust_primitives.unsize chunk)));
      (rebuild_at l sorted (← (i +? (1 : usize))) j acc)
partial_fixpoint

@[spec]
def insert_sorted (v : (alloc.vec.Vec i64 alloc.alloc.Global)) (x : i64) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  (insert_sorted_at
    (← (core_models.ops.deref.Deref.deref
      (alloc.vec.Vec i64 alloc.alloc.Global) v))
    (0 : usize)
    x
    false
    (← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk)))

@[spec]
def collect_evens
    (l : (RustSlice i64))
    (i : usize)
    (acc : (alloc.vec.Vec i64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 l)))) then do
    (pure acc)
  else do
    if (← ((← (i %? (2 : usize))) ==? (0 : usize))) then do
      (collect_evens
        l
        (← (i +? (1 : usize)))
        (← (insert_sorted acc (← l[i]_?))))
    else do
      (collect_evens l (← (i +? (1 : usize))) acc)
partial_fixpoint

@[spec]
def sort_even (l : (RustSlice i64)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  let sorted : (alloc.vec.Vec i64 alloc.alloc.Global) ←
    (collect_evens
      l
      (0 : usize)
      (← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk)));
  (rebuild_at
    l
    (← (core_models.ops.deref.Deref.deref
      (alloc.vec.Vec i64 alloc.alloc.Global) sorted))
    (0 : usize)
    (0 : usize)
    (← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk)))

end clever_036_sort_even

