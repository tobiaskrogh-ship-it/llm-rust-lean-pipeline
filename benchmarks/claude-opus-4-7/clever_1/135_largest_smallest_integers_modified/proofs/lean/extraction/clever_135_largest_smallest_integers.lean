
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


namespace clever_135_largest_smallest_integers

--  HumanEval/136 / CLEVER 135 — `largest_smallest_integers(lst)`.
--  Returns `(a, b)` where `a` is the largest negative integer in `lst`
--  (or `None`), and `b` is the smallest positive integer in `lst` (or
--  `None`).  Zero counts as neither.
@[spec]
def lneg_at (l : (RustSlice i64)) (i : usize) (best : i64) (found : Bool) :
    RustM (rust_primitives.hax.Tuple2 i64 Bool) := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 l)))) then do
    (pure (rust_primitives.hax.Tuple2.mk best found))
  else do
    if
    (← ((← ((← l[i]_?) <? (0 : i64)))
      &&? (← ((← (!? found)) ||? (← ((← l[i]_?) >? best)))))) then do
      (lneg_at l (← (i +? (1 : usize))) (← l[i]_?) true)
    else do
      (lneg_at l (← (i +? (1 : usize))) best found)
partial_fixpoint

@[spec]
def spos_at (l : (RustSlice i64)) (i : usize) (best : i64) (found : Bool) :
    RustM (rust_primitives.hax.Tuple2 i64 Bool) := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 l)))) then do
    (pure (rust_primitives.hax.Tuple2.mk best found))
  else do
    if
    (← ((← ((← l[i]_?) >? (0 : i64)))
      &&? (← ((← (!? found)) ||? (← ((← l[i]_?) <? best)))))) then do
      (spos_at l (← (i +? (1 : usize))) (← l[i]_?) true)
    else do
      (spos_at l (← (i +? (1 : usize))) best found)
partial_fixpoint

@[spec]
def largest_smallest_integers (lst : (RustSlice i64)) :
    RustM
    (rust_primitives.hax.Tuple2
      (core_models.option.Option i64)
      (core_models.option.Option i64))
    := do
  let ⟨a, af⟩ ← (lneg_at lst (0 : usize) (0 : i64) false);
  let ⟨b, bf⟩ ← (spos_at lst (0 : usize) (0 : i64) false);
  let aa : (core_models.option.Option i64) ←
    if af then do
      (pure (core_models.option.Option.Some a))
    else do
      (pure core_models.option.Option.None);
  let bb : (core_models.option.Option i64) ←
    if bf then do
      (pure (core_models.option.Option.Some b))
    else do
      (pure core_models.option.Option.None);
  (pure (rust_primitives.hax.Tuple2.mk aa bb))

end clever_135_largest_smallest_integers

