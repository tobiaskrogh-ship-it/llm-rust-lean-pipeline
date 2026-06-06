
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


namespace sqrt_u64

--  Returns ⌊log₂(x)⌋ for a positive `u64`.
-- 
--  `u64::leading_zeros` is not modeled in the Hax Lean prelude
--  (per `rewrite_patterns/u64_trailing_zeros_method.rs`); we replace
--  the bit-count primitive with a tail-recursive shift loop. Per the
--  project's recursion-preference rule this is the preferred shape
--  over a `while` loop. The recursion depth is at most 63 (one step per
--  bit), so the lack of guaranteed TCO in Rust is not a concern.
@[spec]
def log2_rec (y : u64) (count : u32) : RustM u32 := do
  if (← (y <=? (1 : u64))) then do
    (pure count)
  else do
    (log2_rec (← (y >>>? (1 : i32))) (← (count +? (1 : u32))))
partial_fixpoint

--  Tail-recursive replacement for the upward `while x < xn` loop in `sqrt`.
-- 
--  The loop has a single tuple state `(x, xn)` with no break/continue and
--  bounded iteration depth (at most ~`log2(a)/2 + 1 ≤ 32` steps before the
--  initial guess exceeds the true square root). Per the project's
--  recursion-preference rule, this is rewritten as tail recursion to
--  avoid the body-step Hoare triple that `while_loop` would require.
@[spec]
def sqrt_loop_up (a : u64) (x : u64) (xn : u64) :
    RustM (rust_primitives.hax.Tuple2 u64 u64) := do
  if (← (x <? xn)) then do
    let new_x : u64 := xn;
    let new_xn : u64 ← ((← ((← (a /? new_x)) +? new_x)) >>>? (1 : i32));
    (sqrt_loop_up a new_x new_xn)
  else do
    (pure (rust_primitives.hax.Tuple2.mk x xn))
partial_fixpoint

--  Tail-recursive replacement for the downward `while x > xn` loop in `sqrt`.
-- 
--  Babylonian iteration converges quadratically once it overshoots the true
--  square root, so the recursion depth here is `O(log log a)` — for `u64`,
--  at most a handful of steps. The decreasing measure is `x` itself.
@[spec]
def sqrt_loop_down (a : u64) (x : u64) (xn : u64) : RustM u64 := do
  if (← (x >? xn)) then do
    let new_x : u64 := xn;
    let new_xn : u64 ← ((← ((← (a /? new_x)) +? new_x)) >>>? (1 : i32));
    (sqrt_loop_down a new_x new_xn)
  else do
    (pure x)
partial_fixpoint

@[spec]
def log2 (x : u64) : RustM u32 := do (log2_rec x (0 : u32))

--  Returns the truncated principal square root of `x` -- `⌊√x⌋`.
-- 
--  This is solving for `r` in `r² = x`, rounding toward zero.
--  The result satisfies `r² ≤ x < (r+1)²`.
-- 
--  # Examples
-- 
--  ```
--  use sqrt_u64::sqrt;
--  let x: u64 = 12345;
--  assert_eq!(sqrt(x * x), x);
--  assert_eq!(sqrt(x * x + 1), x);
--  assert_eq!(sqrt(x * x - 1), x - 1);
--  ```
@[spec]
def sqrt (x : u64) : RustM u64 := do
  let a : u64 := x;
  if (← (a <? (4 : u64))) then do
    if (← (a >? (0 : u64))) then do (pure (1 : u64)) else do (pure (0 : u64))
  else do
    let x0 : u64 ←
      ((1 : u64) <<<? (← ((← ((← (log2 a)) +? (1 : u32))) /? (2 : u32))));
    let xn0 : u64 ← ((← ((← (a /? x0)) +? x0)) >>>? (1 : i32));
    let ⟨x1, xn1⟩ ← (sqrt_loop_up a x0 xn0);
    (sqrt_loop_down a x1 xn1)

end sqrt_u64

