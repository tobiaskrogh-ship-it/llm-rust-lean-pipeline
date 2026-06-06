-- Companion obligations file for the `gcd_lcm_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import gcd_lcm_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Gcd_lcm_u64Obligations

/-! ## Zero-input edge-case postconditions

Captures the Rust property test `zero_input_edge_cases`:
```
assert_eq!(gcd_lcm(0, 0), (0, 0));
for x in 1..256u64 {
    assert_eq!(gcd_lcm(x, 0), (x, 0));
    assert_eq!(gcd_lcm(0, x), (x, 0));
}
```
Three independent equational postconditions, one theorem each. The
specialised `(0, 0)` case is logically subsumed by either of the other
two with `x := 0` / `y := 0`, but keeping a dedicated theorem mirrors
the Rust test's structure (the `(0, 0)` branch is the explicit special
case in the Rust source). -/

/-- Postcondition (zero–zero): `gcd_lcm(0, 0)` returns `(0, 0)`,
matching the explicit special case in the Rust source. -/
theorem gcd_lcm_zero_zero :
    gcd_lcm_u64.gcd_lcm (0 : u64) 0 =
      RustM.ok (rust_primitives.hax.Tuple2.mk (0 : u64) (0 : u64)) := by
  decide

/-- Postcondition (right-identity zero): for every `x`,
`gcd_lcm(x, 0)` returns `(x, 0)`. The generic branch reduces to
`gcd(x, 0) = x` (Stein's first guard returns `m | n = x`) and
`x * (0 / x) = 0`. -/
theorem gcd_lcm_x_zero (x : u64) :
    gcd_lcm_u64.gcd_lcm x (0 : u64) =
      RustM.ok (rust_primitives.hax.Tuple2.mk x (0 : u64)) := by
  by_cases hx : x = 0
  · subst hx; decide
  · -- Non-zero `x`: the `&&?` guard becomes false, so we go through
    -- the gcd/lcm branch. `gcd x 0` short-circuits via `n == 0` to
    -- return `x ||| 0 = x`; then `0 /? x = 0`, `x *? 0 = 0`.
    simp only [gcd_lcm_u64.gcd_lcm, gcd_lcm_u64.gcd,
               rust_primitives.cmp.eq, rust_primitives.hax.logical_op.and,
               rust_primitives.hax.logical_op.or, pure_bind]
    have hx_beq : (x == (0 : u64)) = false := by
      simp; exact hx
    simp only [hx_beq, beq_self_eq_true, Bool.false_and, Bool.false_or, Bool.or_true,
               if_false, if_true]
    -- After the gcd-side simplification, we have `m ||| n` for `m=x, n=0`.
    show ((x ||| (0 : u64) |||? (0 : u64)) >>= fun g =>
          (x *? ((0 : u64) /? g) >>= fun l =>
            pure (rust_primitives.hax.Tuple2.mk g l))) =
         RustM.ok (rust_primitives.hax.Tuple2.mk x (0 : u64))
    sorry

/-- Postcondition (left-identity zero): for every `y`,
`gcd_lcm(0, y)` returns `(y, 0)`. Symmetric to the previous theorem. -/
theorem gcd_lcm_zero_y (y : u64) :
    gcd_lcm_u64.gcd_lcm (0 : u64) y =
      RustM.ok (rust_primitives.hax.Tuple2.mk y (0 : u64)) := by
  sorry

/-! ## `gcd` half of the postcondition

Captures the Rust property test `gcd_is_a_common_divisor`, which has
three independent sub-clauses for non-`(0, 0)` inputs (`g ≥ 1`,
`x % g = 0`, `y % g = 0`) plus the `(0, 0)` case `g = 0` already
pinned by `gcd_lcm_zero_zero`. -/

/-- Postcondition: the `gcd` component divides `x` (at the `Nat` level).
For `(0, 0)` the result is `(0, 0)`, so the statement reads
`0 % 0 = 0`, which is definitionally true in `Nat`. -/
theorem gcd_divides_x (x y g l : u64)
    (hres : gcd_lcm_u64.gcd_lcm x y =
              RustM.ok (rust_primitives.hax.Tuple2.mk g l)) :
    x.toNat % g.toNat = 0 := by
  sorry

/-- Postcondition: the `gcd` component divides `y` (at the `Nat` level).
Symmetric to `gcd_divides_x`. -/
theorem gcd_divides_y (x y g l : u64)
    (hres : gcd_lcm_u64.gcd_lcm x y =
              RustM.ok (rust_primitives.hax.Tuple2.mk g l)) :
    y.toNat % g.toNat = 0 := by
  sorry

/-- Postcondition: when `(x, y) ≠ (0, 0)` the `gcd` component is at
least `1`. Independent from the divisibility clauses — a buggy impl
returning `0` for `(1, 1)` would still satisfy `1 % 0 = 1` ≠ 0 (it
would actually break `gcd_divides_x` here, but the two checks are
asserted independently in the Rust test). -/
theorem gcd_positive_when_inputs_nonzero (x y g l : u64)
    (hxy : ¬ (x = 0 ∧ y = 0))
    (hres : gcd_lcm_u64.gcd_lcm x y =
              RustM.ok (rust_primitives.hax.Tuple2.mk g l)) :
    1 ≤ g.toNat := by
  sorry

/-- Postcondition: the `gcd` component is the *greatest* common divisor
— every common divisor of `x` and `y` also divides `g`. Independent
from the "is a common divisor" claim above: a buggy impl returning
`1` whenever `gcd(x, y) > 1` would still divide both inputs but fail
this test. Mirrors the inner loop of the Rust property test
`gcd_is_the_greatest_common_divisor`. -/
theorem gcd_is_greatest_common_divisor (x y g l : u64) (d : Nat)
    (hres : gcd_lcm_u64.gcd_lcm x y =
              RustM.ok (rust_primitives.hax.Tuple2.mk g l))
    (hd_pos : 1 ≤ d)
    (hdx : x.toNat % d = 0)
    (hdy : y.toNat % d = 0) :
    g.toNat % d = 0 := by
  sorry

/-! ## `lcm` half of the postcondition (algebraic identity) -/

/-- Postcondition: `g * l = x * y` at the `Nat` level. Together with
the gcd characterisation above this uniquely determines the `lcm`
component for every input (the `(0, 0)` case satisfies the identity
trivially as `0 * 0 = 0 * 0`). Captures the Rust property test
`gcd_times_lcm_equals_x_times_y`. The Nat-level statement avoids any
overflow consideration on the product — both factors come from `u64`,
so the product is bounded by `2^128` and stays inside `Nat`. -/
theorem gcd_times_lcm_eq_x_times_y (x y g l : u64)
    (hres : gcd_lcm_u64.gcd_lcm x y =
              RustM.ok (rust_primitives.hax.Tuple2.mk g l)) :
    g.toNat * l.toNat = x.toNat * y.toNat := by
  sorry

/-! ## Failure condition

Captures the contract clause documented at the head of the test
module: "panics on overflow when `lcm(x, y) > u64::MAX` (debug mode)".
The Rust property tests stay inside `u64` and so never trigger this
branch, but the contract surface includes it (sourced from the
function's doc-comment). -/

/-- Failure condition (integer overflow on `lcm`): when the unbounded
`lcm` `x * y / gcd(x, y)` exceeds the `u64` range, the multiplication
`x * (y / g)` overflows and the function panics with
`Error.integerOverflow`. The `(0, 0)` case satisfies `Nat.gcd = 0`
and `0 / 0 = 0` in `Nat`, so the hypothesis `2^64 ≤ 0` fails and the
theorem is vacuous there — the special-case branch in the source is
exactly what avoids the spurious failure on `(0, 0)`. -/
theorem gcd_lcm_overflow (x y : u64)
    (h : 2 ^ 64 ≤ x.toNat * y.toNat / Nat.gcd x.toNat y.toNat) :
    gcd_lcm_u64.gcd_lcm x y = RustM.fail .integerOverflow := by
  sorry

end Gcd_lcm_u64Obligations
