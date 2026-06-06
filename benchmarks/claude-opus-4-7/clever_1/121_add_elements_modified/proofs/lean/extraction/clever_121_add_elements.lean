
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


namespace clever_121_add_elements

--  HumanEval/122 / CLEVER 121 — `add_elements(arr, k)`.  Sum of the
--  elements among the first `k` of `arr` whose absolute value has at
--  most 2 decimal digits (i.e. `-99 ≤ v ≤ 99`).
@[spec]
def sum_at (arr : (RustSlice i64)) (k : i64) (i : i64) (acc : i64) :
    RustM i64 := do
  if
  (← ((← (i >=? k))
    ||? (← ((← (rust_primitives.hax.cast_op i : RustM usize))
      >=? (← (core_models.slice.Impl.len i64 arr)))))) then do
    (pure acc)
  else do
    let v : i64 ← arr[(← (rust_primitives.hax.cast_op i : RustM usize))]_?;
    let abs_v : i64 ← if (← (v <? (0 : i64))) then do (-? v) else do (pure v);
    if (← (abs_v <=? (99 : i64))) then do
      (sum_at arr k (← (i +? (1 : i64))) (← (acc +? v)))
    else do
      (sum_at arr k (← (i +? (1 : i64))) acc)
partial_fixpoint

@[spec]
def add_elements (arr : (RustSlice i64)) (k : i64) : RustM i64 := do
  if (← (k <=? (0 : i64))) then do
    (pure (0 : i64))
  else do
    (sum_at arr k (0 : i64) (0 : i64))

end clever_121_add_elements

