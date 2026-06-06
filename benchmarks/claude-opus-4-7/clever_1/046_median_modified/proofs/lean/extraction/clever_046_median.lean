
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


namespace clever_046_median

--  HumanEval/47 — `median(l)`.  Returns a median of the integer list.
-- 
--  Note: CLEVER's reference returns a `float` (the average of the two
--  central elements for even-length lists).  Mapped to `i64` here by
--  returning the **lower** median of the two central elements when the
--  length is even — the same convention used by quickselect-based
--  integer medians.  Semantics are preserved on odd-length lists, where
--  the median is the unique central element.  For an empty input the
--  function returns `0` as a degenerate sentinel.
@[spec]
def count_strictly_less (l : (RustSlice i64)) (m : i64) (i : usize) :
    RustM u64 := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 l)))) then do
    (pure (0 : u64))
  else do
    if (← ((← l[i]_?) <? m)) then do
      ((1 : u64) +? (← (count_strictly_less l m (← (i +? (1 : usize))))))
    else do
      (count_strictly_less l m (← (i +? (1 : usize))))
partial_fixpoint

@[spec]
def count_strictly_greater (l : (RustSlice i64)) (m : i64) (i : usize) :
    RustM u64 := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 l)))) then do
    (pure (0 : u64))
  else do
    if (← ((← l[i]_?) >? m)) then do
      ((1 : u64) +? (← (count_strictly_greater l m (← (i +? (1 : usize))))))
    else do
      (count_strictly_greater l m (← (i +? (1 : usize))))
partial_fixpoint

--  Pick any l[i] satisfying the lower-median property.  The first one
--  scanned will satisfy it because the property is satisfied by exactly
--  one value (or the smaller of two adjacent ones on even lengths).
@[spec]
def find_median_at (l : (RustSlice i64)) (i : usize) : RustM i64 := do
  let n : u64 ←
    (rust_primitives.hax.cast_op
      (← (core_models.slice.Impl.len i64 l)) :
      RustM u64);
  if (← (n ==? (0 : u64))) then do
    (pure (0 : i64))
  else do
    if (← (i >=? (← (core_models.slice.Impl.len i64 l)))) then do
      (pure (0 : i64))
    else do
      let half : u64 ← ((← (n -? (1 : u64))) /? (2 : u64));
      let lt : u64 ← (count_strictly_less l (← l[i]_?) (0 : usize));
      let gt : u64 ← (count_strictly_greater l (← l[i]_?) (0 : usize));
      if
      (← ((← (lt <=? half))
        &&? (← ((← ((← (gt +? (1 : u64))) +? half)) <=? n)))) then do
        l[i]_?
      else do
        (find_median_at l (← (i +? (1 : usize))))
partial_fixpoint

@[spec]
def median (l : (RustSlice i64)) : RustM i64 := do
  (find_median_at l (0 : usize))

end clever_046_median

