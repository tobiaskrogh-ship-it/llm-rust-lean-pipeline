
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


namespace clever_150_compare

--  HumanEval/152 / CLEVER 150 — `compare(scores, guesses)`.  For each
--  position `i`, return `|scores[i] - guesses[i]|`.  Output length is
--  `min(len(scores), len(guesses))`.
@[spec]
def build_at
    (s : (RustSlice i64))
    (g : (RustSlice i64))
    (i : usize)
    (acc : (alloc.vec.Vec i64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  if
  (← ((← (i >=? (← (core_models.slice.Impl.len i64 s))))
    ||? (← (i >=? (← (core_models.slice.Impl.len i64 g)))))) then do
    (pure acc)
  else do
    let d : i64 ←
      if (← ((← s[i]_?) >=? (← g[i]_?))) then do
        ((← s[i]_?) -? (← g[i]_?))
      else do
        ((← g[i]_?) -? (← s[i]_?));
    let chunk : (RustArray i64 1) := (RustArray.ofVec #v[d]);
    let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
        acc
        (← (rust_primitives.unsize chunk)));
    (build_at s g (← (i +? (1 : usize))) acc)
partial_fixpoint

@[spec]
def compare (scores : (RustSlice i64)) (guesses : (RustSlice i64)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  (build_at
    scores
    guesses
    (0 : usize)
    (← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk)))

end clever_150_compare

