
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


namespace clever_004_mean_absolute_deviation

--  For a given list of input numbers, calculate the mean absolute deviation
--  around the mean:  MAD = average | x - x_mean |.
-- 
--  Note: CLEVER's reference signature is `(numbers: List[float]) -> float`.
--  Translated to `i64` because the Hax Lean prelude has gaps in `f64`
--  support (missing `Impl.abs`, `PartialOrd`, `Neg`, broken `Sub.sub` for
--  non-integer types). Integer arithmetic loses fractional precision on the
--  mean and the deviation sum compared to the `f64` reference, but the
--  shape of the contract (average absolute distance from the mean) is the
--  same.
@[spec]
def sum_from (numbers : (RustSlice i64)) (i : usize) : RustM i64 := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 numbers)))) then do
    (pure (0 : i64))
  else do
    ((← numbers[i]_?) +? (← (sum_from numbers (← (i +? (1 : usize))))))
partial_fixpoint

@[spec]
def abs_dev_sum_from (numbers : (RustSlice i64)) (mean : i64) (i : usize) :
    RustM i64 := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 numbers)))) then do
    (pure (0 : i64))
  else do
    let d : i64 ← ((← numbers[i]_?) -? mean);
    let abs_d : i64 ← if (← (d >=? (0 : i64))) then do (pure d) else do (-? d);
    (abs_d +? (← (abs_dev_sum_from numbers mean (← (i +? (1 : usize))))))
partial_fixpoint

@[spec]
def mean_absolute_deviation (numbers : (RustSlice i64)) : RustM i64 := do
  let n : i64 ←
    (rust_primitives.hax.cast_op
      (← (core_models.slice.Impl.len i64 numbers)) :
      RustM i64);
  if (← (n ==? (0 : i64))) then do
    (pure (0 : i64))
  else do
    let mean : i64 ← ((← (sum_from numbers (0 : usize))) /? n);
    ((← (abs_dev_sum_from numbers mean (0 : usize))) /? n)

end clever_004_mean_absolute_deviation

