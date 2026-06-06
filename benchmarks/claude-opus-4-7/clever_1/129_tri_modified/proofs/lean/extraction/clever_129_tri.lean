
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


namespace clever_129_tri

--  HumanEval/130 / CLEVER 129 — `tri(n)`.  Return the first `n + 1`
--  terms of the recurrence:
--    tri(1) = 3,  tri(n)     = 1 + n/2  if n is even,
--                 tri(n)     = tri(n-1) + tri(n-2) + tri(n+1)  if n is odd.
--  Non-negative `n`, so use `u64`.
-- 
--  The trick: for odd n, expanding the recurrence and tri(n+1) (even)
--  gives a closed form so this is computable without forward references.
--  tri(0) is unspecified; we return 3 (matches Python solutions in the wild).
@[spec]
def tri_at (n : u64) (i : u64) (acc : (alloc.vec.Vec u64 alloc.alloc.Global)) :
    RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  if (← (i >? n)) then do
    (pure acc)
  else do
    let v : u64 ←
      if (← (i ==? (0 : u64))) then do
        (pure (3 : u64))
      else do
        if (← (i ==? (1 : u64))) then do
          (pure (3 : u64))
        else do
          if (← ((← (i %? (2 : u64))) ==? (0 : u64))) then do
            ((1 : u64) +? (← (i /? (2 : u64))))
          else do
            let prev_odd : u64 ←
              acc[
                (← (rust_primitives.hax.cast_op
                  (← (i -? (2 : u64))) :
                  RustM usize))
                ]_?;
            let a : u64 ←
              ((1 : u64) +? (← ((← (i -? (1 : u64))) /? (2 : u64))));
            let b : u64 ←
              ((1 : u64) +? (← ((← (i +? (1 : u64))) /? (2 : u64))));
            ((← (a +? prev_odd)) +? b);
    let acc : (alloc.vec.Vec u64 alloc.alloc.Global) := acc;
    let chunk : (RustArray u64 1) := (RustArray.ofVec #v[v]);
    let acc : (alloc.vec.Vec u64 alloc.alloc.Global) ←
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global
        acc
        (← (rust_primitives.unsize chunk)));
    (tri_at n (← (i +? (1 : u64))) acc)
partial_fixpoint

@[spec]
def tri (n : u64) : RustM (alloc.vec.Vec u64 alloc.alloc.Global) := do
  (tri_at
    n
    (0 : u64)
    (← (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk)))

end clever_129_tri

