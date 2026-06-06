
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


namespace clever_069_strange_sort_list

--  HumanEval/70 — `strange_sort_list(l)`.  Return a permutation of `l`
--  whose elements alternate between the current minimum and the
--  current maximum of the remaining items.
-- 
--  Examples:
--    [1, 2, 3, 4]      -> [1, 4, 2, 3]
--    [5, 5, 5, 5]      -> [5, 5, 5, 5]
--    []                -> []
-- 
--  Implemented as: sort the input, then take from alternating ends.
@[spec]
def insert_sorted_at
    (v : (RustSlice i64))
    (x : i64)
    (i : usize)
    (inserted : Bool)
    (acc : (alloc.vec.Vec i64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  let n : usize ← (core_models.slice.Impl.len i64 v);
  if (← (i >=? n)) then do
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
      (insert_sorted_at v x (← (i +? (1 : usize))) true acc)
    else do
      let acc : (alloc.vec.Vec i64 alloc.alloc.Global) := acc;
      let chunk : (RustArray i64 1) := (RustArray.ofVec #v[(← v[i]_?)]);
      let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
          acc
          (← (rust_primitives.unsize chunk)));
      (insert_sorted_at v x (← (i +? (1 : usize))) inserted acc)
partial_fixpoint

@[spec]
def build_strange_at
    (sorted : (RustSlice i64))
    (taken : usize)
    (acc : (alloc.vec.Vec i64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  let n : usize ← (core_models.slice.Impl.len i64 sorted);
  if (← (taken >=? n)) then do
    (pure acc)
  else do
    let half : usize ← (taken /? (2 : usize));
    let idx : usize ←
      if (← ((← (taken %? (2 : usize))) ==? (0 : usize))) then do
        (pure half)
      else do
        ((← (n -? (1 : usize))) -? half);
    let acc : (alloc.vec.Vec i64 alloc.alloc.Global) := acc;
    let chunk : (RustArray i64 1) := (RustArray.ofVec #v[(← sorted[idx]_?)]);
    let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
        acc
        (← (rust_primitives.unsize chunk)));
    (build_strange_at sorted (← (taken +? (1 : usize))) acc)
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
    (sorted : (alloc.vec.Vec i64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 l)))) then do
    (pure sorted)
  else do
    (sort_at l (← (i +? (1 : usize))) (← (insert_sorted sorted (← l[i]_?))))
partial_fixpoint

@[spec]
def strange_sort_list (l : (RustSlice i64)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  let sorted : (alloc.vec.Vec i64 alloc.alloc.Global) ←
    (sort_at
      l
      (0 : usize)
      (← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk)));
  (build_strange_at
    (← (core_models.ops.deref.Deref.deref
      (alloc.vec.Vec i64 alloc.alloc.Global) sorted))
    (0 : usize)
    (← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk)))

end clever_069_strange_sort_list

