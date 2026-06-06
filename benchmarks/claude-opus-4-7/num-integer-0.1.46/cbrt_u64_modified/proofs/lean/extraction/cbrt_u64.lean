
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


namespace cbrt_u64

--  Tail-recursive body of `cbrt_u32`. Lifted from the original `while
--  s_iter > 0 { s_iter -= 1; ... }` loop per the project's
--  recursion-preference rule: the loop has a single tuple state
--  `(s_iter, x, y2, y)`, no break/continue, and a bounded decreasing
--  measure (`s_iter`, at most 11 iterations for `u32`), all conditions
--  for the rewrite. Each recursive call corresponds to one loop body
--  execution. Inside the body, `y2 *= 4` and `y *= 2` are applied
--  unconditionally (becoming `y2_d`, `y_d` here), then the `if (x >> s)
--  >= b` branch additionally subtracts from `x` and bumps `y2`/`y`.
@[spec]
def cbrt_u32_loop (s_iter : u32) (x : u32) (y2 : u32) (y : u32) :
    RustM u32 := do
  if (← (s_iter ==? (0 : u32))) then do
    (pure y)
  else do
    let s_iter_new : u32 ← (s_iter -? (1 : u32));
    let s : u32 ← (s_iter_new *? (3 : u32));
    let y2_d : u32 ← (y2 *? (4 : u32));
    let y_d : u32 ← (y *? (2 : u32));
    let b : u32 ← ((← ((3 : u32) *? (← (y2_d +? y_d)))) +? (1 : u32));
    if (← ((← (x >>>? s)) >=? b)) then do
      let x_new : u32 ← (x -? (← (b <<<? s)));
      let y2_new : u32 ← ((← (y2_d +? (← ((2 : u32) *? y_d)))) +? (1 : u32));
      let y_new : u32 ← (y_d +? (1 : u32));
      (cbrt_u32_loop s_iter_new x_new y2_new y_new)
    else do
      (cbrt_u32_loop s_iter_new x y2_d y_d)
partial_fixpoint

--  Tail-recursive `floor(log2(y))` accumulator. Lifted from the original
--  `while y > 1 { y >>= 1; hi += 1; }` loop per the project's
--  recursion-preference rule: single-loop, single-tuple state `(y, hi)`,
--  clearly decreasing measure (`y`, halved each step), bounded depth
--  (at most 63 iterations for `u64`). Same shape as `log2_rec` in
--  `proof_patterns/sqrt_u64_modified/src/lib.rs`.
@[spec]
def log2_floor_rec (y : u64) (count : u32) : RustM u32 := do
  if (← (y <=? (1 : u64))) then do
    (pure count)
  else do
    (log2_floor_rec (← (y >>>? (1 : i32))) (← (count +? (1 : u32))))
partial_fixpoint

--  Tail-recursive `g << k` accumulator. Lifted from the original
--  `while i < k { g <<= 1; i += 1; }` loop per the project's
--  recursion-preference rule: single-loop, single-tuple state `(i, g)`,
--  clearly decreasing measure (`k - i`, bounded by `k <= 22` here).
@[spec]
def pow2_loop (k : u32) (i : u32) (g : u64) : RustM u64 := do
  if (← (i >=? k)) then do
    (pure g)
  else do
    (pow2_loop k (← (i +? (1 : u32))) (← (g <<<? (1 : i32))))
partial_fixpoint

--  Tail-recursive replacement for the upward `while x < xn` loop of the
--  cube-root Newton fixpoint. The loop has a single tuple state
--  `(x, xn)` with no break/continue. Newton's method for cube root
--  from an overestimate converges monotonically downward, so this upward
--  phase exits almost immediately in practice; bounded depth in all
--  cases. Same shape as `sqrt_loop_up` in
--  `proof_patterns/sqrt_u64_modified/src/lib.rs`.
@[spec]
def fixpoint_cbrt_up (a : u64) (x : u64) (xn : u64) :
    RustM (rust_primitives.hax.Tuple2 u64 u64) := do
  if (← (x <? xn)) then do
    let new_x : u64 := xn;
    let new_xn : u64 ←
      ((← ((← (a /? (← (new_x *? new_x)))) +? (← (new_x *? (2 : u64)))))
        /? (3 : u64));
    (fixpoint_cbrt_up a new_x new_xn)
  else do
    (pure (rust_primitives.hax.Tuple2.mk x xn))
partial_fixpoint

--  Tail-recursive replacement for the downward `while x > xn` loop of
--  the cube-root Newton fixpoint. Newton's method converges quickly
--  once it overshoots the true cube root --- `O(log log a)` steps, a
--  handful at most for `u64`. The decreasing measure is `x` itself.
--  Same shape as `sqrt_loop_down` in
--  `proof_patterns/sqrt_u64_modified/src/lib.rs`.
@[spec]
def fixpoint_cbrt_down (a : u64) (x : u64) (xn : u64) : RustM u64 := do
  if (← (x >? xn)) then do
    let new_x : u64 := xn;
    let new_xn : u64 ←
      ((← ((← (a /? (← (new_x *? new_x)))) +? (← (new_x *? (2 : u64)))))
        /? (3 : u64));
    (fixpoint_cbrt_down a new_x new_xn)
  else do
    (pure x)
partial_fixpoint

--  Hacker's-Delight `icbrt2`, monomorphized to `u32`.
-- 
--  Mirrors the body of the `Roots::cbrt` impl for `u32` produced by
--  `unsigned_roots!(u32)` in `src/roots.rs:333..351`. The original
--  `while` loop is lifted into the tail-recursive helper
--  `cbrt_u32_loop` (see above) so that downstream proofs in Lean can
--  use `Nat.strongRecOn` on the recursion measure instead of the more
--  intricate `Spec.MonoLoopCombinator.while_loop` body-step Hoare-triple
--  machinery.
@[spec]
def cbrt_u32 (a : u32) : RustM u32 := do
  let smax : u32 ← ((32 : u32) /? (3 : u32));
  (cbrt_u32_loop (← (smax +? (1 : u32))) a (0 : u32) (0 : u32))

--  Integer-only stand-in for `(a as f64).cbrt() as u64`, used as the
--  starting point for the Newton fixpoint in the `a > u32::MAX` branch
--  of `cbrt`. Returns a power-of-two `g` with `cbrt(a) <= g < 2^32`,
--  so the recurrence `(a / (x*x) + 2*x) / 3` stays inside `u64` from
--  the first step. The Newton recurrence converges to the same value
--  from any starting overestimate, so the converged result is identical
--  to the upstream `f64`-guess version --- only the iteration count
--  changes. This replaces the `f64`-based guess because `f64` is not
--  modeled by the Hax Lean prelude (no `Cast u64 f64`, no `f64::cbrt`);
--  see `rewrite_patterns/f64_no_hax_model.rs`.
-- 
--  Both internal `while` loops have been lifted into the tail-recursive
--  helpers `log2_floor_rec` and `pow2_loop` (above), per the project's
--  recursion-preference rule.
-- 
--  Precondition (called only from `cbrt` when `a > u32::MAX`, i.e. `a >= 2^32`):
--    * `a >= 2`, so `floor(log2(a)) >= 1` and `k = (hi+3)/3 >= 1`,
--      so `g >= 2 > 0`.
--    * For `a < 2^64`, `floor(log2(a)) <= 63`, so `k <= 22` and
--      `g <= 2^22 < 2^32`. The `pow2_loop` doubling therefore never
--      overflows `u64`.
@[spec]
def cbrt_guess_u64 (a : u64) : RustM u64 := do
  let hi : u32 ← (log2_floor_rec a (0 : u32));
  let k : u32 ← ((← (hi +? (3 : u32))) /? (3 : u32));
  (pow2_loop k (0 : u32) (1 : u64))

--  Defunctionalized `fixpoint(guess, |x| (a/(x*x) + x*2) / 3)` from
--  `src/roots.rs:373..374` (the `next` closure for cube roots). The two
--  original `while` loops (upward then downward) are lifted into the
--  tail-recursive helpers `fixpoint_cbrt_up` / `fixpoint_cbrt_down`
--  above, per the project's recursion-preference rule. This is the same
--  rewrite shape used by `proof_patterns/sqrt_u64_modified` for the
--  analogous square-root Babylonian iteration.
@[spec]
def fixpoint_cbrt (a : u64) (x : u64) : RustM u64 := do
  let xn : u64 ←
    ((← ((← (a /? (← (x *? x)))) +? (← (x *? (2 : u64))))) /? (3 : u64));
  let ⟨x1, xn1⟩ ← (fixpoint_cbrt_up a x xn);
  (fixpoint_cbrt_down a x1 xn1)

--  Concrete `u64` cube root --- truncated principal `∛x`.
-- 
--  `cbrt(x)` returns the largest `r: u64` with `r*r*r <= x`.
@[spec]
def cbrt (x : u64) : RustM u64 := do
  let a : u64 := x;
  if (← (a <? (8 : u64))) then do
    if (← (a >? (0 : u64))) then do (pure (1 : u64)) else do (pure (0 : u64))
  else do
    if (← (a <=? (4294967295 : u64))) then do
      (rust_primitives.hax.cast_op
        (← (cbrt_u32 (← (rust_primitives.hax.cast_op a : RustM u32)))) :
        RustM u64)
    else do
      let guess : u64 ← (cbrt_guess_u64 a);
      (fixpoint_cbrt a guess)

end cbrt_u64

