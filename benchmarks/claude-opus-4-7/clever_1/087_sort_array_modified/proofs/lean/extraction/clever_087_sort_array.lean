
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


namespace clever_087_sort_array

--  HumanEval/88 / CLEVER 087 — `sort_array(lst)`.  Sort `lst` ascending
--  if `(lst[0] + lst[last]) % 2 != 0` (sum is odd); descending otherwise.
--  Spec restricts to non-negative integers → `u64`.
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
def reverse_at
    (s : (RustSlice u64))
    (i : usize)
    (acc : (alloc.vec.Vec u64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  if (← (i >=? (← (core_models.slice.Impl.len u64 s)))) then do
    (pure acc)
  else do
    let acc : (alloc.vec.Vec u64 alloc.alloc.Global) := acc;
    let chunk : (RustArray u64 1) :=
      (RustArray.ofVec #v[(← s[
                              (← ((← ((← (core_models.slice.Impl.len u64 s))
                                  -? (1 : usize)))
                                -? i))
                              ]_?)]);
    let acc : (alloc.vec.Vec u64 alloc.alloc.Global) ←
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global
        acc
        (← (rust_primitives.unsize chunk)));
    (reverse_at s (← (i +? (1 : usize))) acc)
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
def sort_array (lst : (RustSlice u64)) :
    RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  if (← (core_models.slice.Impl.is_empty u64 lst)) then do
    (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk)
  else do
    let sorted : (alloc.vec.Vec u64 alloc.alloc.Global) ←
      (sort_at
        lst
        (0 : usize)
        (← (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk)));
    let parity : u64 ←
      ((← ((← ((← lst[(0 : usize)]_?) %? (2 : u64)))
          +? (← ((← lst[
              (← ((← (core_models.slice.Impl.len u64 lst)) -? (1 : usize)))
              ]_?)
            %? (2 : u64)))))
        %? (2 : u64));
    if (← (parity !=? (0 : u64))) then do
      (pure sorted)
    else do
      (reverse_at
        (← (core_models.ops.deref.Deref.deref
          (alloc.vec.Vec u64 alloc.alloc.Global) sorted))
        (0 : usize)
        (← (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk)))

end clever_087_sort_array

