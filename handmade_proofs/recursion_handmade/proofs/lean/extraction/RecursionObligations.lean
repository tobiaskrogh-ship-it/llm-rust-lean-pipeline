
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import recursion_handmade

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace RecursionObligations

private theorem hax_beq_def_u64 (x y : u64) :
    x ==? y = pure (x == y) := rfl
private theorem hax_sub_def_u64 (x y : u64) :
    x -? y = if BitVec.usubOverflow x.toBitVec y.toBitVec
             then RustM.fail Error.integerOverflow
             else pure (x - y) := rfl
private theorem hax_add_def_u64 (x y : u64) :
    x +? y = if BitVec.uaddOverflow x.toBitVec y.toBitVec
             then RustM.fail Error.integerOverflow
             else pure (x + y) := rfl
theorem count_to_postcondition_simple (n : u64) :
    recursion_handmade.count_to n = RustM.ok n := by
  induction h : n.toNat generalizing n with
  | zero =>
    rw [recursion_handmade.count_to, hax_beq_def_u64, pure_bind, if_pos]
    replace h : n = 0 := UInt64.toNat_inj.mp h
    subst h
    rfl
    replace h : n = 0 := UInt64.toNat_inj.mp h
    subst h
    rfl
  | succ k ih =>
    have hn : n ≠ 0 := by
        intro hc
        subst hc
        contradiction
    rw [recursion_handmade.count_to, hax_beq_def_u64, pure_bind,
    if_neg, hax_sub_def_u64, if_neg, pure_bind, ih]
    show (n - 1) +? 1 = RustM.ok n
    rw [hax_add_def_u64, if_neg, show n - 1 + 1 = n by bv_decide]
    rfl -- goal discharged
    bv_decide -- constradiction used here
    rw [UInt64.toNat_sub_of_le' (by simp; omega)]
    simp [h] -- goal discharged
    bv_decide -- constradiction used here
    simp
    trivial -- constradiction used here



































/-- Boundary: `count_to 0` returns `0` without entering the recursive branch. -/
theorem count_to_zero :
    recursion_handmade.count_to 0 = RustM.ok 0 := by
    rw [recursion_handmade.count_to]
    rw [hax_beq_def_u64]
    rw [pure_bind]
    rw [if_pos]
    trivial
    rfl




end RecursionObligations
