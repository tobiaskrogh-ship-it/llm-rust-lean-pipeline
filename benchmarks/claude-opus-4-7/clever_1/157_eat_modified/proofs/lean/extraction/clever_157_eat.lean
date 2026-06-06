
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


namespace clever_157_eat

--  HumanEval/159 / CLEVER 157 — `eat(number, need, remaining)`.
--  You've already eaten `number` carrots, you need to eat `need` more.
--  Return `[total_eaten, remaining_after]`.  If `remaining < need`,
--  you eat all remaining carrots.
@[spec]
def eat (number : u64) (need : u64) (remaining : u64) :
    RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  let result : (alloc.vec.Vec u64 alloc.alloc.Global) ←
    (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk);
  let result : (alloc.vec.Vec u64 alloc.alloc.Global) ←
    if (← (remaining >=? need)) then do
      let chunk : (RustArray u64 2) :=
        (RustArray.ofVec #v[(← (number +? need)), (← (remaining -? need))]);
      let result : (alloc.vec.Vec u64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global
          result
          (← (rust_primitives.unsize chunk)));
      (pure result)
    else do
      let chunk : (RustArray u64 2) :=
        (RustArray.ofVec #v[(← (number +? remaining)), (0 : u64)]);
      let result : (alloc.vec.Vec u64 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global
          result
          (← (rust_primitives.unsize chunk)));
      (pure result);
  (pure result)

end clever_157_eat

