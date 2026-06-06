
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


namespace clever_033_unique

--  Return sorted unique elements of `l`. (Return type widened to
--  `Vec<i64>` to match the docstring; CLEVER auto-defaulted to `i64`.)
@[spec]
def insert_sorted_at
    (v : (RustSlice i64))
    (x : i64)
    (i : usize)
    (inserted : Bool)
    (acc : (alloc.vec.Vec i64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 v)))) then do
    if (← (!? inserted)) then do
      let chunk : (RustArray i64 1) := (RustArray.ofVec #v[x]);
      let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
          acc
          (← (rust_primitives.unsize chunk)));
      (pure acc)
    else do
      (pure acc)
  else do
    let vi : i64 ← v[i]_?;
    if (← ((← (!? inserted)) &&? (← (vi >=? x)))) then do
      let chunk : (RustArray i64 2) := (RustArray.ofVec #v[x, vi]);
      let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
          acc
          (← (rust_primitives.unsize chunk)));
      (insert_sorted_at v x (← (i +? (1 : usize))) true acc)
    else do
      let chunk : (RustArray i64 1) := (RustArray.ofVec #v[vi]);
      let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
          acc
          (← (rust_primitives.unsize chunk)));
      (insert_sorted_at v x (← (i +? (1 : usize))) inserted acc)
partial_fixpoint

@[spec]
def dedupe_at
    (sorted : (RustSlice i64))
    (i : usize)
    (acc : (alloc.vec.Vec i64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 sorted)))) then do
    (pure acc)
  else do
    let keep : Bool ←
      if (← (i ==? (0 : usize))) then do
        (pure true)
      else do
        ((← sorted[i]_?) !=? (← sorted[(← (i -? (1 : usize)))]_?));
    if keep then do
      let chunk : (RustArray i64 1) := (RustArray.ofVec #v[(← sorted[i]_?)]);
      let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
          acc
          (← (rust_primitives.unsize chunk)));
      (dedupe_at sorted (← (i +? (1 : usize))) acc)
    else do
      (dedupe_at sorted (← (i +? (1 : usize))) acc)
partial_fixpoint

@[spec]
def insert_sorted (v : (alloc.vec.Vec i64 alloc.alloc.Global)) (x : i64) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  (insert_sorted_at
    (← (core_models.ops.deref.Deref.deref
      (alloc.vec.Vec i64 alloc.alloc.Global) v))
    x
    (0 : usize)
    false
    (← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk)))

@[spec]
def sort_at
    (l : (RustSlice i64))
    (i : usize)
    (acc : (alloc.vec.Vec i64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 l)))) then do
    (pure acc)
  else do
    (sort_at l (← (i +? (1 : usize))) (← (insert_sorted acc (← l[i]_?))))
partial_fixpoint

@[spec]
def unique (l : (RustSlice i64)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  let sorted : (alloc.vec.Vec i64 alloc.alloc.Global) ←
    (sort_at
      l
      (0 : usize)
      (← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk)));
  (dedupe_at
    (← (core_models.ops.deref.Deref.deref
      (alloc.vec.Vec i64 alloc.alloc.Global) sorted))
    (0 : usize)
    (← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk)))

end clever_033_unique

