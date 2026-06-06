
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


namespace lcm_u64

--  Count of trailing zero bits in `x`. Replaces `u64::trailing_zeros`,
--  whose extraction target `core_models.num.Impl_9.trailing_zeros` is not
--  defined in the Hax Lean prelude.
@[spec]
def trailing_zeros_u64 (x : u64) : RustM u32 := do
  if (← (x ==? (0 : u64))) then do
    (pure (64 : u32))
  else do
    let y : u64 := x;
    let count : u32 := (0 : u32);
    let ⟨count, y⟩ ←
      (rust_primitives.hax.while_loop
        (fun ⟨count, y⟩ => (do (pure true) : RustM Bool))
        (fun ⟨count, y⟩ =>
          (do ((← (y &&&? (1 : u64))) ==? (0 : u64)) : RustM Bool))
        (fun ⟨count, y⟩ =>
          (do
          (rust_primitives.hax.int.from_machine (0 : u32)) :
          RustM hax_lib.int.Int))
        (rust_primitives.hax.Tuple2.mk count y)
        (fun ⟨count, y⟩ =>
          (do
          let y : u64 ← (y >>>? (1 : i32));
          let count : u32 ← (count +? (1 : u32));
          (pure (rust_primitives.hax.Tuple2.mk count y)) :
          RustM (rust_primitives.hax.Tuple2 u32 u64))));
    (pure count)

--  Tail-recursive core of Stein's algorithm: both arguments are odd and
--  nonzero on entry. Each step either terminates (`m == n`) or strictly
--  reduces the larger argument, so the recursion depth is bounded by the
--  bit-width of the inputs (~64 iterations for `u64`).
@[spec]
def gcd_stein_loop (m : u64) (n : u64) : RustM u64 := do
  if (← (m ==? n)) then do
    (pure m)
  else do
    if (← (m >? n)) then do
      let d : u64 ← (m -? n);
      (gcd_stein_loop (← (d >>>? (← (trailing_zeros_u64 d)))) n)
    else do
      let d : u64 ← (n -? m);
      (gcd_stein_loop m (← (d >>>? (← (trailing_zeros_u64 d)))))
partial_fixpoint

--  Greatest Common Divisor of two `u64`s using Stein's (binary) algorithm.
--  Inlined from the `Integer` impl for `u64` in `num-integer` 0.1.46.
@[spec]
def gcd_u64 (a : u64) (b : u64) : RustM u64 := do
  if (← ((← (a ==? (0 : u64))) ||? (← (b ==? (0 : u64))))) then do
    (a |||? b)
  else do
    let shift : u32 ← (trailing_zeros_u64 (← (a |||? b)));
    let m : u64 ← (a >>>? (← (trailing_zeros_u64 a)));
    let n : u64 ← (b >>>? (← (trailing_zeros_u64 b)));
    ((← (gcd_stein_loop m n)) <<<? shift)

--  Calculates the Lowest Common Multiple (LCM) of `x` and `y`.
@[spec]
def lcm (x : u64) (y : u64) : RustM u64 := do
  if (← ((← (x ==? (0 : u64))) &&? (← (y ==? (0 : u64))))) then do
    (pure (0 : u64))
  else do
    let gcd : u64 ← (gcd_u64 x y);
    (x *? (← (y /? gcd)))

end lcm_u64

