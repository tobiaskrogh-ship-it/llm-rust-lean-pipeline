
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


namespace nth_root_u64

--  Returns `⌊log₂(x)⌋` for `x >= 1`. Replaces `u64::leading_zeros`,
--  which has no Hax Lean prelude model
--  (`rewrite_patterns/u64_trailing_zeros_method.rs`). Tail-recursive
--  shift loop; recursion depth is at most 63 (one step per bit) — well
--  inside the 10^5 safe envelope for the recursion-preference rule.
@[spec]
def log2_rec (y : u64) (count : u32) : RustM u32 := do
  if (← (y <=? (1 : u64))) then do
    (pure count)
  else do
    (log2_rec (← (y >>>? (1 : i32))) (← (count +? (1 : u32))))
partial_fixpoint

--  Tail-recursive `g << k` accumulator. Replaces a `while i < k {
--  g <<= 1; i += 1; }` shape per the recursion-preference rule.
--  Recursion depth bounded by `k`, which is at most 64.
@[spec]
def pow2_loop (k : u32) (i : u32) (g : u64) : RustM u64 := do
  if (← (i >=? k)) then do
    (pure g)
  else do
    (pow2_loop k (← (i +? (1 : u32))) (← (g <<<? (1 : i32))))
partial_fixpoint

--  Compute `x^n` as `u64`, returning `None` if it overflows `u64`.
--  Replaces `u64::checked_pow`, which has no Hax model
--  (`rewrite_patterns/checked_wrapping_to_bare_arith.rs`). The caller
--  **does** branch on `None` (the original `next` closure in `nth_root`
--  returns 0 when the power overflows), so we cannot use bare `*`; we
--  reproduce `checked_pow`'s overflow semantics explicitly.
-- 
--  Termination: `n` is the decreasing measure. Recursion depth bounded
--  by the exponent (`<= 128` for the test sweep in proptest).
-- 
--  Overflow check: for `x > 0`, `rest * x > u64::MAX` iff
--  `rest > u64::MAX / x` (the floor division is the right threshold
--  because `(u64::MAX / x) * x <= u64::MAX < (u64::MAX / x + 1) * x`).
--  The `x == 0` case is special-cased first so the `u64::MAX / x`
--  division stays under its guard through Hax's eager `do`-block
--  extraction (see `rewrite_patterns/short_circuit_and_with_partial_op.rs`).
--  `u64::MAX` itself is inlined as the literal `18_446_744_073_709_551_615`
--  per `rewrite_patterns/primitive_int_assoc_const.rs`.
@[spec]
def pow_u64_opt (x : u64) (n : u32) :
    RustM (core_models.option.Option u64) := do
  if (← (n ==? (0 : u32))) then do
    (pure (core_models.option.Option.Some (1 : u64)))
  else do
    match (← (pow_u64_opt x (← (n -? (1 : u32))))) with
      | (core_models.option.Option.Some  rest) => do
        if (← (x ==? (0 : u64))) then do
          (pure (core_models.option.Option.Some (0 : u64)))
        else do
          if (← (rest >? (← ((18446744073709551615 : u64) /? x)))) then do
            (pure core_models.option.Option.None)
          else do
            (pure (core_models.option.Option.Some (← (rest *? x))))
      | (core_models.option.Option.None ) => do
        (pure core_models.option.Option.None)
partial_fixpoint

--  Tail-recursive body of `cbrt_u32`. Replaces `for s in (0..smax+1).rev()`
--  from the original, which uses an unmodeled `Range` iterator + `.rev()`
--  chain (`rewrite_patterns/iter_chain_to_recursion.rs`).
-- 
--  The iteration counter `s_iter` decreases from `smax + 1 = 11` down to
--  `0`; each step corresponds to one source loop iteration with the
--  shadowed `s = s_iter_new * 3` substituted directly. Same shape as
--  `proof_patterns/cbrt_u64_modified::cbrt_u32_loop`.
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

--  Upward phase of the Babylonian fixpoint: while `x < xn`, advance.
--  Same shape as `proof_patterns/sqrt_u64_modified::sqrt_loop_up`.
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

--  Downward phase of the Babylonian fixpoint: while `x > xn`, advance;
--  otherwise return `x`. Newton's method converges quadratically from
--  an overestimate, so depth is `O(log log a)` — well bounded for `u64`.
--  Decreasing measure: `x` itself.
--  Same shape as `proof_patterns/sqrt_u64_modified::sqrt_loop_down`.
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
def cbrt_loop_up (a : u64) (x : u64) (xn : u64) :
    RustM (rust_primitives.hax.Tuple2 u64 u64) := do
  if (← (x <? xn)) then do
    let new_x : u64 := xn;
    let new_xn : u64 ←
      ((← ((← (a /? (← (new_x *? new_x)))) +? (← (new_x *? (2 : u64)))))
        /? (3 : u64));
    (cbrt_loop_up a new_x new_xn)
  else do
    (pure (rust_primitives.hax.Tuple2.mk x xn))
partial_fixpoint

@[spec]
def cbrt_loop_down (a : u64) (x : u64) (xn : u64) : RustM u64 := do
  if (← (x >? xn)) then do
    let new_x : u64 := xn;
    let new_xn : u64 ←
      ((← ((← (a /? (← (new_x *? new_x)))) +? (← (new_x *? (2 : u64)))))
        /? (3 : u64));
    (cbrt_loop_down a new_x new_xn)
  else do
    (pure x)
partial_fixpoint

@[spec]
def log2_u64 (x : u64) : RustM u32 := do (log2_rec x (0 : u32))

@[spec]
def cbrt_u32 (a : u32) : RustM u32 := do
  (cbrt_u32_loop (11 : u32) a (0 : u32) (0 : u32))

--  Integer-only power-of-two initial guess for `sqrt(a)`. Returns
--  `g = 2^ceil((log2(a)+1)/2)`, which is `>= sqrt(a)`. Replaces
--  `(a as f64).sqrt() as u64` (`f64` is not modeled by Hax —
--  `rewrite_patterns/f64_no_hax_model.rs`). The Babylonian iteration
--  converges to the same value from any starting overestimate; only
--  the iteration count differs.
@[spec]
def sqrt_guess_u64 (a : u64) : RustM u64 := do
  let hi : u32 ← (log2_u64 a);
  let k : u32 ← ((← (hi +? (2 : u32))) /? (2 : u32));
  (pow2_loop k (0 : u32) (1 : u64))

--  Truncated principal square root of `a: u64`.
@[spec]
def sqrt_u64 (a : u64) : RustM u64 := do
  if (← (a <? (4 : u64))) then do
    if (← (a >? (0 : u64))) then do (pure (1 : u64)) else do (pure (0 : u64))
  else do
    let x0 : u64 ← (sqrt_guess_u64 a);
    let xn0 : u64 ← ((← ((← (a /? x0)) +? x0)) >>>? (1 : i32));
    let ⟨x1, xn1⟩ ← (sqrt_loop_up a x0 xn0);
    (sqrt_loop_down a x1 xn1)

--  Integer-only initial guess for the `cbrt` Newton fixpoint.
--  `k = ceil((log2(a)+1)/3)`, so `g = 2^k >= cbrt(a)`. At the call site
--  (`a > 4_294_967_295`), `log2(a) >= 32`, so `k <= 22`, hence `g <= 2^22`
--  and `g*g <= 2^44 < 2^64`. Same shape as
--  `proof_patterns/cbrt_u64_modified::cbrt_guess_u64`.
@[spec]
def cbrt_guess_u64 (a : u64) : RustM u64 := do
  let hi : u32 ← (log2_u64 a);
  let k : u32 ← ((← (hi +? (3 : u32))) /? (3 : u32));
  (pow2_loop k (0 : u32) (1 : u64))

--  Truncated principal cube root of `a: u64`.
@[spec]
def cbrt_u64 (a : u64) : RustM u64 := do
  if (← (a <? (8 : u64))) then do
    if (← (a >? (0 : u64))) then do (pure (1 : u64)) else do (pure (0 : u64))
  else do
    if (← (a <=? (4294967295 : u64))) then do
      (rust_primitives.hax.cast_op
        (← (cbrt_u32 (← (rust_primitives.hax.cast_op a : RustM u32)))) :
        RustM u64)
    else do
      let x0 : u64 ← (cbrt_guess_u64 a);
      let xn0 : u64 ←
        ((← ((← (a /? (← (x0 *? x0)))) +? (← (x0 *? (2 : u64))))) /? (3 : u64));
      let ⟨x1, xn1⟩ ← (cbrt_loop_up a x0 xn0);
      (cbrt_loop_down a x1 xn1)

--  Integer-only initial guess for the `nth_root` Newton fixpoint.
--  `1u64 << ((log2(a) + n - 1) / n)` — works for any `a >= 1` and
--  `n >= 1`. Replaces the original `if x <= u32::MAX as u64 { ... }
--  else { (x.ln() / n).exp() as u64 }` conditional, whose `else` branch
--  used `f64::ln` / `f64::exp` — unmodeled by Hax
--  (`rewrite_patterns/f64_no_hax_model.rs`).
@[spec]
def nth_root_guess (a : u64) (n : u32) : RustM u64 := do
  let shift : u32 ← ((← ((← ((← (log2_u64 a)) +? n)) -? (1 : u32))) /? n);
  (pow2_loop shift (0 : u32) (1 : u64))

--  One step of the Newton recurrence `(y + x*(n-1)) / n` where
--  `y = a / x^(n-1)` (or `0` if `x^(n-1)` overflows `u64`, matching
--  the original `match x.checked_pow(n1) { ... }` shape).
-- 
--  The `ax == 0` branch protects against `a / 0`: it can only arise if
--  `x == 0` (since `pow_u64_opt(0, k>0) = Some(0)`), which the Newton
--  iteration does not reach in practice (the initial guess is `>= 1`
--  and the recurrence preserves `x >= 1` whenever `n >= 2`). The guard
--  is kept defensively and matches the original code's effective
--  "treat divide-by-anomaly as y = 0" pattern.
@[spec]
def nth_root_step (a : u64) (n1 : u32) (n : u32) (x : u64) : RustM u64 := do
  let y : u64 ←
    match (← (pow_u64_opt x n1)) with
      | (core_models.option.Option.Some  ax) => do
        if (← (ax ==? (0 : u64))) then do (pure (0 : u64)) else do (a /? ax)
      | (core_models.option.Option.None ) => do (pure (0 : u64));
  ((← (y +? (← (x *? (← (rust_primitives.hax.cast_op n1 : RustM u64))))))
    /? (← (rust_primitives.hax.cast_op n : RustM u64)))

@[spec]
def nth_root_loop_up (a : u64) (n1 : u32) (n : u32) (x : u64) (xn : u64) :
    RustM (rust_primitives.hax.Tuple2 u64 u64) := do
  if (← (x <? xn)) then do
    let new_x : u64 := xn;
    let new_xn : u64 ← (nth_root_step a n1 n new_x);
    (nth_root_loop_up a n1 n new_x new_xn)
  else do
    (pure (rust_primitives.hax.Tuple2.mk x xn))
partial_fixpoint

@[spec]
def nth_root_loop_down (a : u64) (n1 : u32) (n : u32) (x : u64) (xn : u64) :
    RustM u64 := do
  if (← (x >? xn)) then do
    let new_x : u64 := xn;
    let new_xn : u64 ← (nth_root_step a n1 n new_x);
    (nth_root_loop_down a n1 n new_x new_xn)
  else do
    (pure x)
partial_fixpoint

--  Returns the truncated principal `n`th root of `self_val: u64`.
-- 
--  Equivalent to `<u64 as num_integer::Roots>::nth_root(&self_val, n)` in
--  `num-integer-0.1.46`.
-- 
--  # Panics
-- 
--  Panics if `n == 0` (induced via `n - 1` u32 underflow — see
--  crate-level docs for why `panic!("...")` with a format string is
--  avoided).
@[spec]
def nth_root (self_val : u64) (n : u32) : RustM u64 := do
  let a : u64 := self_val;
  if (← (n ==? (1 : u32))) then do
    (pure a)
  else do
    if (← (n ==? (2 : u32))) then do
      (sqrt_u64 a)
    else do
      if (← (n ==? (3 : u32))) then do
        (cbrt_u64 a)
      else do
        let n1 : u32 ← (n -? (1 : u32));
        if (← (n >=? (64 : u32))) then do
          if (← (a >? (0 : u64))) then do
            (pure (1 : u64))
          else do
            (pure (0 : u64))
        else do
          if (← (a <? (← ((1 : u64) <<<? n)))) then do
            if (← (a >? (0 : u64))) then do
              (pure (1 : u64))
            else do
              (pure (0 : u64))
          else do
            let x0 : u64 ← (nth_root_guess a n);
            let xn0 : u64 ← (nth_root_step a n1 n x0);
            let ⟨x1, xn1⟩ ← (nth_root_loop_up a n1 n x0 xn0);
            (nth_root_loop_down a n1 n x1 xn1)

end nth_root_u64

