
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


namespace clever_067_pluck

--  HumanEval/68 — `pluck(l)`.  Find the smallest even value's
--  `[value, index]` pair in `l`.  Ties on value broken by smallest
--  index.  Returns an empty list if no even value (or empty input).
-- 
--  Note: CLEVER's spec restricts inputs to non-negative integers.  The
--  implementation accepts any `i64`; on a non-negative domain it is
--  faithful to the spec.  On a list containing negatives the
--  "smallest even" interpretation is the arithmetically smallest, which
--  is a reasonable extension.
@[spec]
def smallest_even_at
    (l : (RustSlice i64))
    (i : usize)
    (best : i64)
    (found : Bool) :
    RustM (rust_primitives.hax.Tuple2 i64 Bool) := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 l)))) then do
    (pure (rust_primitives.hax.Tuple2.mk best found))
  else do
    if
    (← ((← ((← ((← l[i]_?) %? (2 : i64))) ==? (0 : i64)))
      &&? (← ((← (!? found)) ||? (← ((← l[i]_?) <? best)))))) then do
      (smallest_even_at l (← (i +? (1 : usize))) (← l[i]_?) true)
    else do
      (smallest_even_at l (← (i +? (1 : usize))) best found)
partial_fixpoint

@[spec]
def first_index_of (l : (RustSlice i64)) (target : i64) (i : usize) :
    RustM u64 := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 l)))) then do
    (pure (0 : u64))
  else do
    if (← ((← l[i]_?) ==? target)) then do
      (rust_primitives.hax.cast_op i : RustM u64)
    else do
      (first_index_of l target (← (i +? (1 : usize))))
partial_fixpoint

@[spec]
def pluck (l : (RustSlice i64)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  let ⟨val, found⟩ ← (smallest_even_at l (0 : usize) (0 : i64) false);
  if (← (!? found)) then do
    (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk)
  else do
    let idx : i64 ←
      (rust_primitives.hax.cast_op
        (← (first_index_of l val (0 : usize))) :
        RustM i64);
    let result : (alloc.vec.Vec i64 alloc.alloc.Global) ←
      (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk);
    let chunk : (RustArray i64 2) := (RustArray.ofVec #v[val, idx]);
    let result : (alloc.vec.Vec i64 alloc.alloc.Global) ←
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
        result
        (← (rust_primitives.unsize chunk)));
    (pure result)

end clever_067_pluck

