
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


namespace clever_122_get_odd_collatz

--  HumanEval/123 / CLEVER 122 — `get_odd_collatz(n)`.  Return the
--  sorted list of odd numbers in the Collatz sequence starting at `n`.
--  The sequence: `x → x/2` if x even, `x → 3x + 1` if x odd; ends at 1.
@[spec]
def vec_contains (v : (RustSlice u64)) (x : u64) (i : usize) : RustM Bool := do
  if (← (i >=? (← (core_models.slice.Impl.len u64 v)))) then do
    (pure false)
  else do
    if (← ((← v[i]_?) ==? x)) then do
      (pure true)
    else do
      (vec_contains v x (← (i +? (1 : usize))))
partial_fixpoint

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
    let ⟨acc, new_done⟩ ←
      if (← ((← (!? done)) &&? (← ((← v[i]_?) >=? x)))) then do
        let chunk : (RustArray u64 1) := (RustArray.ofVec #v[x]);
        let acc : (alloc.vec.Vec u64 alloc.alloc.Global) ←
          (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global
            acc
            (← (rust_primitives.unsize chunk)));
        (pure (rust_primitives.hax.Tuple2.mk acc true))
      else do
        (pure (rust_primitives.hax.Tuple2.mk acc done));
    let acc : (alloc.vec.Vec u64 alloc.alloc.Global) ←
      if (← ((← (!? new_done)) ||? (← ((← v[i]_?) !=? x)))) then do
        let chunk : (RustArray u64 1) := (RustArray.ofVec #v[(← v[i]_?)]);
        let acc : (alloc.vec.Vec u64 alloc.alloc.Global) ←
          (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global
            acc
            (← (rust_primitives.unsize chunk)));
        (pure acc)
      else do
        (pure acc);
    (insert_asc_at v x (← (i +? (1 : usize))) new_done acc)
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
def step_at (x : u64) (acc : (alloc.vec.Vec u64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  if (← (x ==? (1 : u64))) then do
    if
    (← (!? (← (vec_contains
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u64 alloc.alloc.Global) acc))
      (1 : u64)
      (0 : usize))))) then do
      (insert_asc acc (1 : u64))
    else do
      (pure acc)
  else do
    if (← ((← (x %? (2 : u64))) ==? (1 : u64))) then do
      let next : (alloc.vec.Vec u64 alloc.alloc.Global) ←
        if
        (← (vec_contains
          (← (core_models.ops.deref.Deref.deref
            (alloc.vec.Vec u64 alloc.alloc.Global) acc))
          x
          (0 : usize))) then do
          (pure acc)
        else do
          (insert_asc acc x);
      (step_at (← ((← ((3 : u64) *? x)) +? (1 : u64))) next)
    else do
      (step_at (← (x /? (2 : u64))) acc)
partial_fixpoint

@[spec]
def get_odd_collatz (n : u64) :
    RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  if (← (n ==? (0 : u64))) then do
    (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk)
  else do
    (step_at n (← (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk)))

end clever_122_get_odd_collatz

