
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


namespace clever_115_max_fill_count

--  CLEVER 115 (HumanEval/116) — note that the canonical signature here
--  is named `max_fill_count` but the docstring describes a *different*
--  problem: sort an array of non-negative integers by the number of
--  `1` bits in their binary representation (ascending), ties broken by
--  decimal value.  The function name in this crate honours the CLEVER
--  docstring's algorithm.  Override to `u64` per the docstring's
--  "non-negative integers".
@[spec]
def popcount_at (n : u64) (acc : u64) : RustM u64 := do
  if (← (n ==? (0 : u64))) then do
    (pure acc)
  else do
    (popcount_at (← (n /? (2 : u64))) (← (acc +? (← (n %? (2 : u64))))))
partial_fixpoint

@[spec]
def lex_less (a : u64) (b : u64) : RustM Bool := do
  let pa : u64 ← (popcount_at a (0 : u64));
  let pb : u64 ← (popcount_at b (0 : u64));
  if (← (pa <? pb)) then do
    (pure true)
  else do
    if (← (pa >? pb)) then do (pure false) else do (a <? b)

@[spec]
def insert_sorted_at
    (v : (RustSlice u64))
    (x : u64)
    (i : usize)
    (done : Bool)
    (r : (alloc.vec.Vec u64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  if (← (i >=? (← (core_models.slice.Impl.len u64 v)))) then do
    let r : (alloc.vec.Vec u64 alloc.alloc.Global) := r;
    let r : (alloc.vec.Vec u64 alloc.alloc.Global) ←
      if (← (!? done)) then do
        let chunk : (RustArray u64 1) := (RustArray.ofVec #v[x]);
        let r : (alloc.vec.Vec u64 alloc.alloc.Global) ←
          (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global
            r
            (← (rust_primitives.unsize chunk)));
        (pure r)
      else do
        (pure r);
    (pure r)
  else do
    let r : (alloc.vec.Vec u64 alloc.alloc.Global) := r;
    let done : Bool := done;
    let ⟨done, r⟩ ←
      if (← ((← (!? done)) &&? (← (!? (← (lex_less (← v[i]_?) x)))))) then do
        let chunk : (RustArray u64 1) := (RustArray.ofVec #v[x]);
        let r : (alloc.vec.Vec u64 alloc.alloc.Global) ←
          (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global
            r
            (← (rust_primitives.unsize chunk)));
        let done : Bool := true;
        (pure (rust_primitives.hax.Tuple2.mk done r))
      else do
        (pure (rust_primitives.hax.Tuple2.mk done r));
    let chunk : (RustArray u64 1) := (RustArray.ofVec #v[(← v[i]_?)]);
    let r : (alloc.vec.Vec u64 alloc.alloc.Global) ←
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global
        r
        (← (rust_primitives.unsize chunk)));
    (insert_sorted_at v x (← (i +? (1 : usize))) done r)
partial_fixpoint

@[spec]
def insert_sorted (v : (alloc.vec.Vec u64 alloc.alloc.Global)) (x : u64) :
    RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  (insert_sorted_at
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
    (sort_at l (← (i +? (1 : usize))) (← (insert_sorted s (← l[i]_?))))
partial_fixpoint

@[spec]
def sort_by_popcount (l : (RustSlice u64)) :
    RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  (sort_at
    l
    (0 : usize)
    (← (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk)))

end clever_115_max_fill_count

