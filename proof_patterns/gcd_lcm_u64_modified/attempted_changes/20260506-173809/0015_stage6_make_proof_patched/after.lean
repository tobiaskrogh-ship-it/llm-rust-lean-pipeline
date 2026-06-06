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
    -- the gcd/lcm branch.  The key facts are
    --   `(x == 0) = false`, `(0 == 0) = true`,
    --   `gcd x 0 = x` (Stein's first guard), `0 / x = 0`, `x * 0 = 0`.
    have hx_beq : (x == (0 : u64)) = false := beq_eq_false_iff_ne.mpr hx
    have hor : x ||| (0 : u64) = x := by bv_decide
    have hno_mul : BitVec.umulOverflow x.toBitVec (0#64) = false := by
      bv_decide
    have hmul0 : x * (0 : u64) = 0 := by bv_decide
    simp [gcd_lcm_u64.gcd_lcm, gcd_lcm_u64.gcd,
          rust_primitives.cmp.eq, rust_primitives.hax.logical_op.and,
          rust_primitives.hax.logical_op.or,
          rust_primitives.ops.arith.Div.div,
          rust_primitives.ops.arith.Mul.mul,
          hx_beq, hx, hor, hno_mul, hmul0]
    rfl

/-- Postcondition (left-identity zero): for every `y`,
`gcd_lcm(0, y)` returns `(y, 0)`. Symmetric to the previous theorem. -/
theorem gcd_lcm_zero_y (y : u64) :
    gcd_lcm_u64.gcd_lcm (0 : u64) y =
      RustM.ok (rust_primitives.hax.Tuple2.mk y (0 : u64)) := by
  by_cases hy : y = 0
  · subst hy; decide
  · -- Non-zero `y`: similar to `gcd_lcm_x_zero`.  Here `gcd 0 y = y`
    --   (Stein's first guard via `m == 0`), `y /? y = 1`, `0 *? 1 = 0`.
    have hy_beq : (y == (0 : u64)) = false := beq_eq_false_iff_ne.mpr hy
    have hor : (0 : u64) ||| y = y := by bv_decide
    have hdiv_self : y / y = (1 : u64) := by
      have hne : y ≠ 0 := hy
      bv_decide
    simp [gcd_lcm_u64.gcd_lcm, gcd_lcm_u64.gcd,
          rust_primitives.cmp.eq, rust_primitives.hax.logical_op.and,
          rust_primitives.hax.logical_op.or,
          rust_primitives.ops.arith.Div.div,
          rust_primitives.ops.arith.Mul.mul,
          hy_beq, hy, hor, hdiv_self]
    rfl

/-! ## `gcd` half of the postcondition

Captures the Rust property test `gcd_is_a_common_divisor`, which has
three independent sub-clauses for non-`(0, 0)` inputs (`g ≥ 1`,
`x % g = 0`, `y % g = 0`) plus the `(0, 0)` case `g = 0` already
pinned by `gcd_lcm_zero_zero`. -/

/-- Postcondition: the `gcd` component divides `x` (at the `Nat` level).
For `(0, 0)` the result is `(0, 0)`, so the statement reads
`0 % 0 = 0`, which is definitionally true in `Nat`.

UNPROVEN. Technical reason: the Hax prelude is missing
`core_models.num.Impl_9.trailing_zeros`. We have stubbed it as
`opaque` so the extraction compiles, but `opaque` produces no
defining equation, so for non-zero inputs the body of `gcd_lcm_u64.gcd`
- which calls `trailing_zeros` three times and runs a Stein-style
  while-loop driven by those calls - is unknown. Given only
  `hres : gcd_lcm x y = ok (g, l)` for `x, y ≠ 0`, no information
  about `g.toNat` can be derived, so the divisibility relation
  `x.toNat % g.toNat = 0` is not provable. Closing this requires
  (a) replacing the opaque with a `pure (UInt32.ofNat (BitVec.countTrailingZeros …))`
  spec, and (b) proving Stein's binary GCD correct against
  `Nat.gcd`, which is a substantial separate effort. -/
theorem gcd_divides_x (x y g l : u64)
    (hres : gcd_lcm_u64.gcd_lcm x y =
              RustM.ok (rust_primitives.hax.Tuple2.mk g l)) :
    x.toNat % g.toNat = 0 := by
  sorry

/-- Postcondition: the `gcd` component divides `y` (at the `Nat` level).
Symmetric to `gcd_divides_x`.

UNPROVEN. Same technical reason as `gcd_divides_x`: the opaque
`trailing_zeros` blocks all reasoning about `gcd`'s output for
non-zero `x, y`. -/
theorem gcd_divides_y (x y g l : u64)
    (hres : gcd_lcm_u64.gcd_lcm x y =
              RustM.ok (rust_primitives.hax.Tuple2.mk g l)) :
    y.toNat % g.toNat = 0 := by
  sorry

/-- Postcondition: when `(x, y) ≠ (0, 0)` the `gcd` component is at
least `1`. Independent from the divisibility clauses — a buggy impl
returning `0` for `(1, 1)` would still satisfy `1 % 0 = 1` ≠ 0 (it
would actually break `gcd_divides_x` here, but the two checks are
asserted independently in the Rust test).

UNPROVEN. Same technical reason as `gcd_divides_x`: the result `g`
of `gcd x y` for both non-zero inputs goes through opaque
`trailing_zeros` calls and a while loop, so its value is unknown.
The cases where exactly one of `x, y` is zero ARE provable in
isolation (they reduce via `gcd_lcm_x_zero` / `gcd_lcm_zero_y`),
but the both-non-zero case is the one we need a Stein-correctness
proof for. -/
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
`gcd_is_the_greatest_common_divisor`.

UNPROVEN. Same technical reason as `gcd_divides_x`. The greatest
common divisor characterisation is the strongest of the gcd
postconditions and requires the full Stein-correctness theorem
plus the maximality argument. -/
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
so the product is bounded by `2^128` and stays inside `Nat`.

UNPROVEN. Same technical reason as `gcd_divides_x`: for both-non-zero
inputs `x, y`, the value of `g = gcd x y` depends on the opaque
`trailing_zeros`. The lcm `l` is then `x * (y / g)` which inherits
this dependency. The algebraic identity `g * l = x * y` requires
knowing that `g` actually divides `y` (so that `y / g` is exact),
which itself requires the Stein-correctness proof. -/
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
exactly what avoids the spurious failure on `(0, 0)`.

UNPROVEN. Same technical reason as `gcd_divides_x`: the only path
that can reach the multiplication `x *? (y /? g)` for both-non-zero
inputs goes through the opaque-`trailing_zeros`-driven gcd loop.
Without knowing `g`, we cannot determine when `x * (y / g)` overflows
the u64 range, and so cannot prove the failure side of the contract. -/
theorem gcd_lcm_overflow (x y : u64)
    (h : 2 ^ 64 ≤ x.toNat * y.toNat / Nat.gcd x.toNat y.toNat) :
    gcd_lcm_u64.gcd_lcm x y = RustM.fail .integerOverflow := by
  sorry

end Gcd_lcm_u64Obligations
