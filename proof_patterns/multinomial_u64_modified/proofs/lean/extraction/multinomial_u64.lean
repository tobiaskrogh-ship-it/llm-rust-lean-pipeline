
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


namespace multinomial_u64

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

--  Calculates the Greatest Common Divisor (GCD) of two `u64` values, using
--  Stein's binary algorithm. Inlined from
--  `<u64 as Integer>::gcd` (via the `impl_integer_for_usize!` macro).
@[spec]
def gcd (x : u64) (y : u64) : RustM u64 := do
  if (← ((← (x ==? (0 : u64))) ||? (← (y ==? (0 : u64))))) then do
    (x |||? y)
  else do
    let shift : u32 ← (trailing_zeros_u64 (← (x |||? y)));
    let m : u64 ← (x >>>? (← (trailing_zeros_u64 x)));
    let n : u64 ← (y >>>? (← (trailing_zeros_u64 y)));
    ((← (gcd_stein_loop m n)) <<<? shift)

--  Calculate `r * a / b`, avoiding overflows and fractions.
-- 
--  Assumes that `b` divides `r * a` evenly.
@[spec]
def multiply_and_divide (r : u64) (a : u64) (b : u64) : RustM u64 := do
  let g : u64 ← (gcd r b);
  ((← (r /? g)) *? (← (a /? (← (b /? g)))))

--  Tail-recursive form of the inner accumulator loop of `binomial`.
-- 
--  Carries the loop state `(n, d, r)`: at each step, we multiply the
--  running product `r` by `n / d` (mediated by `multiply_and_divide` to
--  avoid intermediate overflow), then decrement `n` and increment `d`.
--  Terminates when `d > k`, returning the accumulated `r`.
-- 
--  Decreasing measure: `k - d + 1` (equivalently, the bound `d <= k + 1`).
--  Depth ≤ `k + 1`, which is ≤ 68 across the overflow-free `u64` domain.
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

--  Calculate the binomial coefficient.
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

--  Tail-recursive form of the `multinomial` slice iteration. Carries the
--  running sum `p` and the accumulated product `r`; walks `k` by index
--  `i` with decreasing measure `k.len() - i`.
@[spec]
def multinomial_loop (k : (RustSlice u64)) (i : usize) (p : u64) (r : u64) :
    RustM u64 := do
  if (← (i >=? (← (core_models.slice.Impl.len u64 k)))) then do
    (pure r)
  else do
    let p_new : u64 ← (p +? (← k[i]_?));
    (multinomial_loop
      k
      (← (i +? (1 : usize)))
      p_new
      (← (r *? (← (binomial p_new (← k[i]_?))))))
partial_fixpoint

--  Calculate the multinomial coefficient.
@[spec]
def multinomial (k : (RustSlice u64)) : RustM u64 := do
  (multinomial_loop k (0 : usize) (0 : u64) (1 : u64))

end multinomial_u64

