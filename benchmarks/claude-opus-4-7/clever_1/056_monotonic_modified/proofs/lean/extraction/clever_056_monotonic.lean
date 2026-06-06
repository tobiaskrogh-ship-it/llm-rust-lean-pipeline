
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


namespace clever_056_monotonic

--  HumanEval/57 — `monotonic(l)`.  Returns true iff the elements of `l`
--  are monotonically increasing OR monotonically decreasing.  Lists of
--  length 0 or 1 are vacuously both, so the answer is `true`.
-- 
--  Implemented as two tail-recursive scans over the slice.  Note the
--  `||` short-circuit guards no partial operation here (both helpers
--  are total), so it survives Hax extraction faithfully.
@[spec]
def is_nondecreasing_from (l : (RustSlice i64)) (i : u64) : RustM Bool := do
  let n : u64 ←
    (rust_primitives.hax.cast_op
      (← (core_models.slice.Impl.len i64 l)) :
      RustM u64);
  if (← ((← (i +? (1 : u64))) >=? n)) then do
    (pure true)
  else do
    if
    (← ((← l[(← (rust_primitives.hax.cast_op i : RustM usize))]_?)
      >? (← l[
        (← (rust_primitives.hax.cast_op (← (i +? (1 : u64))) : RustM usize))
        ]_?))) then do
      (pure false)
    else do
      (is_nondecreasing_from l (← (i +? (1 : u64))))
partial_fixpoint

@[spec]
def is_nonincreasing_from (l : (RustSlice i64)) (i : u64) : RustM Bool := do
  let n : u64 ←
    (rust_primitives.hax.cast_op
      (← (core_models.slice.Impl.len i64 l)) :
      RustM u64);
  if (← ((← (i +? (1 : u64))) >=? n)) then do
    (pure true)
  else do
    if
    (← ((← l[(← (rust_primitives.hax.cast_op i : RustM usize))]_?)
      <? (← l[
        (← (rust_primitives.hax.cast_op (← (i +? (1 : u64))) : RustM usize))
        ]_?))) then do
      (pure false)
    else do
      (is_nonincreasing_from l (← (i +? (1 : u64))))
partial_fixpoint

@[spec]
def monotonic (l : (RustSlice i64)) : RustM Bool := do
  if (← (is_nondecreasing_from l (0 : u64))) then do
    (pure true)
  else do
    (is_nonincreasing_from l (0 : u64))

end clever_056_monotonic

