
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


namespace clever_127_prod_signs

--  HumanEval/128 / CLEVER 127 — `prod_signs(arr)`.  Return `sum(|v|) *
--  product(sgn(v))` where `sgn(0) = 0`, `sgn(>0) = 1`, `sgn(<0) = -1`.
--  Return `None` for empty input.
@[spec]
def run_at (arr : (RustSlice i64)) (i : usize) (sum_abs : i64) (sign : i64) :
    RustM i64 := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 arr)))) then do
    (sum_abs *? sign)
  else do
    let v : i64 ← arr[i]_?;
    let av : i64 ← if (← (v <? (0 : i64))) then do (-? v) else do (pure v);
    let s : i64 ←
      if (← (v ==? (0 : i64))) then do
        (pure (0 : i64))
      else do
        if (← (v >? (0 : i64))) then do
          (pure (1 : i64))
        else do
          (pure (-1 : i64));
    (run_at arr (← (i +? (1 : usize))) (← (sum_abs +? av)) (← (sign *? s)))
partial_fixpoint

@[spec]
def prod_signs (arr : (RustSlice i64)) :
    RustM (core_models.option.Option i64) := do
  if (← (core_models.slice.Impl.is_empty i64 arr)) then do
    (pure core_models.option.Option.None)
  else do
    (pure (core_models.option.Option.Some
      (← (run_at arr (0 : usize) (0 : i64) (1 : i64)))))

end clever_127_prod_signs

