
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


namespace binomial_u64

--  Number of trailing zero bits of `x`; `trailing_zeros_u64(0) == 64`.
-- 
--  Inlined replacement for `u64::trailing_zeros()`, which has no model
--  in the Hax Lean prelude.
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

--  Tail-recursive core of Stein's binary GCD: assumes both inputs odd
--  and non-zero, and returns the GCD of the odd parts. The original
--  `while m != n { ... }` loop on the outer subtract-and-strip step is
--  replaced by structural recursion on the (m, n) state.
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

--  Greatest common divisor on `u64`, Stein's binary algorithm.
-- 
--  Inlined from the unsigned arm of the `Integer for $T` impl macro in
--  `num-integer-0.1.46/src/lib.rs` lines 870–895.
@[spec]
def gcd_u64 (x : u64) (y : u64) : RustM u64 := do
  if (← ((← (x ==? (0 : u64))) ||? (← (y ==? (0 : u64))))) then do
    (x |||? y)
  else do
    let shift : u32 ← (trailing_zeros_u64 (← (x |||? y)));
    let m : u64 ← (x >>>? (← (trailing_zeros_u64 x)));
    let n : u64 ← (y >>>? (← (trailing_zeros_u64 y)));
    ((← (gcd_stein_loop m n)) <<<? shift)

--  Calculate `r * a / b`, avoiding overflows and fractions.
-- 
--  Assumes that `b` divides `r * a` evenly. Inlined from
--  `num-integer-0.1.46/src/lib.rs` lines 1124–1128.
@[spec]
def multiply_and_divide (r : u64) (a : u64) (b : u64) : RustM u64 := do
  let g : u64 ← (gcd_u64 r b);
  ((← (r /? g)) *? (← (a /? (← (b /? g)))))

--  Tail-recursive form of the inner accumulator loop of `binomial`.
-- 
--  Carries the loop state `(n, d, r)`: at each step, we multiply the
--  running product `r` by `n / d` (mediated by `multiply_and_divide` to
--  avoid intermediate overflow), then decrement `n` and increment `d`.
--  Terminates when `d > k`, returning the accumulated `r`.
-- 
--  Decreasing measure: `k - d + 1` (or, equivalently, the bound
--  `d <= k + 1`). Depth ≤ `k + 1`, which is ≤ 68 across the
--  overflow-free `u64` domain.
@[spec]
def binomial_loop (n : u64) (k : u64) (d : u64) (r : u64) : RustM u64 := do
  if (← (d >? k)) then do
    (pure r)
  else do
    (binomial_loop
      (← (n -? (1 : u64)))
      k
      (← (d +? (1 : u64)))
      (← (multiply_and_divide r n d)))
partial_fixpoint

--  Calculate the binomial coefficient C(n, k) for `u64`.
-- 
--  For `u64` the largest `n` for which there is no overflow for any `k`
--  is `67` (matching the table in the original `binomial` doc-comment).
-- 
--  Monomorphic `u64` version of `num_integer::binomial::<u64>`. The body
--  is unchanged from the source other than the type substitution and
--  the loop → tail-recursion rewrite above.
@[spec]
def binomial (n : u64) (k : u64) : RustM u64 := do
  if (← (k >? n)) then do
    (pure (0 : u64))
  else do
    if (← (k >? (← (n -? k)))) then do
      (binomial n (← (n -? k)))
    else do
      (binomial_loop n k (1 : u64) (1 : u64))
partial_fixpoint

end binomial_u64

