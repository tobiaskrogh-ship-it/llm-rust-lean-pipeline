
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


namespace clever_061_derivative

--  HumanEval/62 — `derivative(xs)`.  Given coefficients
--  `xs = [a0, a1, a2, ..., a_{n-1}]` representing the polynomial
--  `a0 + a1*x + a2*x^2 + ... + a_{n-1}*x^{n-1}`, return the
--  coefficients of its derivative: `[a1, 2*a2, 3*a3, ..., (n-1)*a_{n-1}]`.
-- 
--  The empty input and a single-element (constant polynomial) input
--  both yield an empty derivative.
@[spec]
def build_at
    (c : (RustSlice i64))
    (i : usize)
    (acc : (alloc.vec.Vec i64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  if (← (i >=? (← (core_models.slice.Impl.len i64 c)))) then do
    (pure acc)
  else do
    let chunk : (RustArray i64 1) :=
      (RustArray.ofVec #v[(← ((← (rust_primitives.hax.cast_op i : RustM i64))
                              *? (← c[i]_?)))]);
    let acc : (alloc.vec.Vec i64 alloc.alloc.Global) ←
      (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
        acc
        (← (rust_primitives.unsize chunk)));
    (build_at c (← (i +? (1 : usize))) acc)
partial_fixpoint

@[spec]
def derivative (c : (RustSlice i64)) :
    RustM (alloc.vec.Vec i64 alloc.alloc.Global) := do
  if (← (core_models.slice.Impl.is_empty i64 c)) then do
    (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk)
  else do
    (build_at
      c
      (1 : usize)
      (← (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk)))

end clever_061_derivative

