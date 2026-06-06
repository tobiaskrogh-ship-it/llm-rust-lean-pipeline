
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


namespace clever_000_has_close_elements

--  Check if in given list of numbers, are any two numbers closer to each
--  other than the given threshold.
-- 
--  Note: CLEVER's reference signature is `(numbers: List[float], threshold:
--  float) -> bool`. Translated to `i64` here because the Hax Lean prelude has
--  gaps in `f64` support (no `Impl.abs`, no `PartialOrd f64 f64`, no `Neg
--  f64`, and `Sub.sub` is emitted without type arguments for non-integer
--  types). Semantics are preserved up to integer arithmetic.
@[spec]
def has_close_elements_at
    (numbers : (RustSlice i64))
    (threshold : i64)
    (k : u64) :
    RustM Bool := do
  let n : u64 ←
    (rust_primitives.hax.cast_op
      (← (core_models.slice.Impl.len i64 numbers)) :
      RustM u64);
  if (← (k >=? (← (n *? n)))) then do
    (pure false)
  else do
    let i : usize ← (rust_primitives.hax.cast_op (← (k /? n)) : RustM usize);
    let j : usize ← (rust_primitives.hax.cast_op (← (k %? n)) : RustM usize);
    let diff : i64 ←
      if (← ((← numbers[i]_?) >? (← numbers[j]_?))) then do
        ((← numbers[i]_?) -? (← numbers[j]_?))
      else do
        ((← numbers[j]_?) -? (← numbers[i]_?));
    if (← ((← (i !=? j)) &&? (← (diff <? threshold)))) then do
      (pure true)
    else do
      (has_close_elements_at numbers threshold (← (k +? (1 : u64))))
partial_fixpoint

@[spec]
def has_close_elements (numbers : (RustSlice i64)) (threshold : i64) :
    RustM Bool := do
  (has_close_elements_at numbers threshold (0 : u64))

end clever_000_has_close_elements

