
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


namespace clever_029_get_positive

--  Return only the strictly positive (> 0) numbers from `l`, in input order.
--  (Return type widened from CLEVER's auto-defaulted `i64` to `Vec<i64>` to
--  match the docstring's "Return only positive numbers in the list".)
@[spec]
def collect_at
    (l : (RustSlice i64))
    (i : usize)
    (acc : (alloc.vec.Vec i64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 l)))) then do
    (pure acc)
  else do
    if (← ((← l[i]_?) >? (0 : i64))) then do
      let acc : (alloc.vec.Vec i64 alloc.alloc.Global) := acc;
      let chunk : (RustArray i64 1) := (RustArray.ofVec #v[(← l[i]_?)]);
      let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
          acc
          (← (rust_primitives.unsize chunk)));
      (collect_at l (← (i +? (1 : usize))) acc)
    else do
      (collect_at l (← (i +? (1 : usize))) acc)
partial_fixpoint

@[spec]
def get_positive (l : (RustSlice i64)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  (collect_at
    l
    (0 : usize)
    (← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk)))

end clever_029_get_positive

