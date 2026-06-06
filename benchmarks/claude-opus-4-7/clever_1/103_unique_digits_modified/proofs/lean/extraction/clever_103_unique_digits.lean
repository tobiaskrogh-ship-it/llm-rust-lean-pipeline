
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


namespace clever_103_unique_digits

--  HumanEval/104 / CLEVER 103 — `unique_digits(x)`.  Return a sorted
--  list of positive integers from `x` whose decimal digits are all odd.
--  (The name "unique" is misleading; "all-odd-digit" is the actual contract.)
@[spec]
def has_even_digit_at (n : u64) : RustM Bool := do
  if (← (n ==? (0 : u64))) then do
    (pure false)
  else do
    if (← ((← ((← (n %? (10 : u64))) %? (2 : u64))) ==? (0 : u64))) then do
      (pure true)
    else do
      (has_even_digit_at (← (n /? (10 : u64))))
partial_fixpoint

@[spec]
def insert_asc_at
    (v : (RustSlice u64))
    (i : usize)
    (e : u64)
    (done : Bool)
    (acc : (alloc.vec.Vec u64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  if (← (i >=? (← (core_models.slice.Impl.len u64 v)))) then do
    if (← (!? done)) then do
      let acc : (alloc.vec.Vec u64 alloc.alloc.Global) := acc;
      let chunk : (RustArray u64 1) := (RustArray.ofVec #v[e]);
      let acc : (alloc.vec.Vec u64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global
          acc
          (← (rust_primitives.unsize chunk)));
      (pure acc)
    else do
      (pure acc)
  else do
    if (← ((← (!? done)) &&? (← ((← v[i]_?) >=? e)))) then do
      let acc : (alloc.vec.Vec u64 alloc.alloc.Global) := acc;
      let chunk_e : (RustArray u64 1) := (RustArray.ofVec #v[e]);
      let acc : (alloc.vec.Vec u64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global
          acc
          (← (rust_primitives.unsize chunk_e)));
      let chunk_v : (RustArray u64 1) := (RustArray.ofVec #v[(← v[i]_?)]);
      let acc : (alloc.vec.Vec u64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global
          acc
          (← (rust_primitives.unsize chunk_v)));
      (insert_asc_at v (← (i +? (1 : usize))) e true acc)
    else do
      let acc : (alloc.vec.Vec u64 alloc.alloc.Global) := acc;
      let chunk_v : (RustArray u64 1) := (RustArray.ofVec #v[(← v[i]_?)]);
      let acc : (alloc.vec.Vec u64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global
          acc
          (← (rust_primitives.unsize chunk_v)));
      (insert_asc_at v (← (i +? (1 : usize))) e done acc)
partial_fixpoint

@[spec]
def has_even_digit (n : u64) : RustM Bool := do
  if (← (n ==? (0 : u64))) then do (pure true) else do (has_even_digit_at n)

@[spec]
def insert_asc (v : (alloc.vec.Vec u64 alloc.alloc.Global)) (e : u64) :
    RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  (insert_asc_at
    (← (core_models.ops.deref.Deref.deref
      (alloc.vec.Vec u64 alloc.alloc.Global) v))
    (0 : usize)
    e
    false
    (← (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk)))

@[spec]
def filter_at
    (l : (RustSlice u64))
    (i : usize)
    (acc : (alloc.vec.Vec u64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  if (← (i >=? (← (core_models.slice.Impl.len u64 l)))) then do
    (pure acc)
  else do
    if (← (has_even_digit (← l[i]_?))) then do
      (filter_at l (← (i +? (1 : usize))) acc)
    else do
      (filter_at l (← (i +? (1 : usize))) (← (insert_asc acc (← l[i]_?))))
partial_fixpoint

@[spec]
def unique_digits (x : (RustSlice u64)) :
    RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  (filter_at
    x
    (0 : usize)
    (← (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk)))

end clever_103_unique_digits

