
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


namespace clever_160_generate_integers

--  HumanEval/163 / CLEVER 160 — `generate_integers(a, b)`.  Return the
--  even single-digit integers (0, 2, 4, 6, 8) in `[min(a, b), max(a, b)]`,
--  in ascending order.
@[spec]
def build_at
    (lo : u64)
    (hi : u64)
    (k : u64)
    (acc : (alloc.vec.Vec u64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  if (← ((← (k >? hi)) ||? (← (k >? (8 : u64))))) then do
    (pure acc)
  else do
    let acc : (alloc.vec.Vec u64 alloc.alloc.Global) ←
      if
      (← ((← (k >=? lo)) &&? (← ((← (k %? (2 : u64))) ==? (0 : u64))))) then do
        let chunk : (RustArray u64 1) := (RustArray.ofVec #v[k]);
        let acc : (alloc.vec.Vec u64 alloc.alloc.Global) ←
          (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global
            acc
            (← (rust_primitives.unsize chunk)));
        (pure acc)
      else do
        (pure acc);
    (build_at lo hi (← (k +? (1 : u64))) acc)
partial_fixpoint

@[spec]
def generate_integers (a : u64) (b : u64) :
    RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  let lo : u64 ← if (← (a <? b)) then do (pure a) else do (pure b);
  let hi : u64 ← if (← (a <? b)) then do (pure b) else do (pure a);
  (build_at
    lo
    hi
    (0 : u64)
    (← (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk)))

end clever_160_generate_integers

