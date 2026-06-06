
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


namespace clever_107_count_nums

--  HumanEval/108 / CLEVER 107 — `count_nums(arr)`.  Count elements
--  whose *signed* digit sum is > 0.  For negative `n`, the leading
--  digit takes the sign (e.g. `-123 → -1 + 2 + 3 = 4`).
@[spec]
def first_digit_at (n : i64) : RustM i64 := do
  if (← (n <? (10 : i64))) then do
    (pure n)
  else do
    (first_digit_at (← (n /? (10 : i64))))
partial_fixpoint

@[spec]
def digit_sum_at (n : i64) (acc : i64) : RustM i64 := do
  if (← (n ==? (0 : i64))) then do
    (pure acc)
  else do
    (digit_sum_at (← (n /? (10 : i64))) (← (acc +? (← (n %? (10 : i64))))))
partial_fixpoint

@[spec]
def signed_digit_sum (n : i64) : RustM i64 := do
  if (← (n ==? (0 : i64))) then do
    (pure (0 : i64))
  else do
    if (← (n >? (0 : i64))) then do
      (digit_sum_at n (0 : i64))
    else do
      let m : i64 ← (-? n);
      ((← (digit_sum_at m (0 : i64)))
        -? (← ((2 : i64) *? (← (first_digit_at m)))))

@[spec]
def count_at (arr : (RustSlice i64)) (i : usize) (acc : i64) : RustM i64 := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 arr)))) then do
    (pure acc)
  else do
    if (← ((← (signed_digit_sum (← arr[i]_?))) >? (0 : i64))) then do
      (count_at arr (← (i +? (1 : usize))) (← (acc +? (1 : i64))))
    else do
      (count_at arr (← (i +? (1 : usize))) acc)
partial_fixpoint

@[spec]
def count_nums (arr : (RustSlice i64)) : RustM i64 := do
  (count_at arr (0 : usize) (0 : i64))

end clever_107_count_nums

