
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


namespace clever_032_sort_third

--  Return a list identical to `l` at indices NOT divisible by 3, with the
--  values at indices divisible by 3 replaced by those same values in
--  ascending order. (Return type widened to `Vec<i64>` to match the
--  docstring; CLEVER auto-defaulted to `i64`.)
@[spec]
def insert_sorted (v : (alloc.vec.Vec i64 alloc.alloc.Global)) (x : i64) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  let result : (alloc.vec.Vec i64 alloc.alloc.Global) ←
    (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk);
  let n : usize ← (alloc.vec.Impl_1.len i64 alloc.alloc.Global v);
  let i : usize := (0 : usize);
  let inserted : Bool := false;
  let ⟨i, inserted, result⟩ ←
    (rust_primitives.hax.while_loop
      (fun ⟨i, inserted, result⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, inserted, result⟩ => (do (i <? n) : RustM Bool))
      (fun ⟨i, inserted, result⟩ =>
        (do
        (rust_primitives.hax.int.from_machine (0 : u32)) :
        RustM hax_lib.int.Int))
      (rust_primitives.hax.Tuple3.mk i inserted result)
      (fun ⟨i, inserted, result⟩ =>
        (do
        let ⟨inserted, result⟩ ←
          if (← ((← (!? inserted)) &&? (← ((← v[i]_?) >=? x)))) then do
            let chunk : (RustArray i64 1) := (RustArray.ofVec #v[x]);
            let result : (alloc.vec.Vec i64 alloc.alloc.Global) ←
              (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
                result
                (← (rust_primitives.unsize chunk)));
            let inserted : Bool := true;
            (pure (rust_primitives.hax.Tuple2.mk inserted result))
          else do
            (pure (rust_primitives.hax.Tuple2.mk inserted result));
        let chunk : (RustArray i64 1) := (RustArray.ofVec #v[(← v[i]_?)]);
        let result : (alloc.vec.Vec i64 alloc.alloc.Global) ←
          (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
            result
            (← (rust_primitives.unsize chunk)));
        let i : usize ← (i +? (1 : usize));
        (pure (rust_primitives.hax.Tuple3.mk i inserted result)) :
        RustM
        (rust_primitives.hax.Tuple3
          usize
          Bool
          (alloc.vec.Vec i64 alloc.alloc.Global)))));
  let result : (alloc.vec.Vec i64 alloc.alloc.Global) ←
    if (← (!? inserted)) then do
      let chunk : (RustArray i64 1) := (RustArray.ofVec #v[x]);
      let result : (alloc.vec.Vec i64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
          result
          (← (rust_primitives.unsize chunk)));
      (pure result)
    else do
      (pure result);
  (pure result)

@[spec]
def collect_thirds
    (l : (RustSlice i64))
    (i : usize)
    (acc : (alloc.vec.Vec i64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 l)))) then do
    (pure acc)
  else do
    if (← ((← (i %? (3 : usize))) ==? (0 : usize))) then do
      (collect_thirds
        l
        (← (i +? (1 : usize)))
        (← (insert_sorted acc (← l[i]_?))))
    else do
      (collect_thirds l (← (i +? (1 : usize))) acc)
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
    if (← ((← (i %? (3 : usize))) ==? (0 : usize))) then do
      let chunk : (RustArray i64 1) := (RustArray.ofVec #v[(← sorted[j]_?)]);
      let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
          acc
          (← (rust_primitives.unsize chunk)));
      (rebuild_at l sorted (← (i +? (1 : usize))) (← (j +? (1 : usize))) acc)
    else do
      let chunk : (RustArray i64 1) := (RustArray.ofVec #v[(← l[i]_?)]);
      let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
          acc
          (← (rust_primitives.unsize chunk)));
      (rebuild_at l sorted (← (i +? (1 : usize))) j acc)
partial_fixpoint

@[spec]
def sort_third (l : (RustSlice i64)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  let sorted : (alloc.vec.Vec i64 alloc.alloc.Global) ←
    (collect_thirds
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

end clever_032_sort_third

