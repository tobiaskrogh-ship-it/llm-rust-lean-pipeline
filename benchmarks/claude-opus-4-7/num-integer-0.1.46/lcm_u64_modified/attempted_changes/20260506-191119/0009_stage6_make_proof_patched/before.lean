-- Companion obligations file for the `lcm_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import lcm_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Lcm_u64Obligations

/-- Postcondition (zero is absorbing, left): for every `y : u64`, `lcm 0 y`
    successfully returns `0`. Captures one half of the Rust property test
    `prop_zero_is_absorbing` (the `lcm(0, v)` direction). When `y = 0` the
    function takes the explicit `x == 0 && y == 0` early-return branch; when
    `y ≠ 0` it goes through the gcd path with `gcd_u64 0 y = y`, then
    `0 *? (y / y) = 0 *? 1 = ok 0`. Either way the result is `ok 0`. -/
theorem lcm_zero_left (y : u64) :
    lcm_u64.lcm 0 y = RustM.ok 0 := by
  sorry

/-- Postcondition (zero is absorbing, right): for every `x : u64`, `lcm x 0`
    successfully returns `0`. Captures the `lcm(v, 0)` direction of the Rust
    property test `prop_zero_is_absorbing`. When `x = 0` the early-return
    branch fires; when `x ≠ 0` we have `gcd_u64 x 0 = x`, then
    `x *? (0 / x) = x *? 0 = ok 0`. -/
theorem lcm_zero_right (x : u64) :
    lcm_u64.lcm x 0 = RustM.ok 0 := by
  sorry

/-- Postcondition (common multiple, left factor): whenever `lcm x y` returns
    successfully with value `r`, `r` is a multiple of `x` (in `Nat`). Captures
    the Rust property test `prop_result_is_multiple_of_x`. The hypothesis is
    framed as "the function returned `ok r`" so the claim is vacuous on
    inputs where the implementation overflows; this is the same shape as the
    contract clauses in `factorial_modified` / `sum_to_n_modified`.

    Note: `x ≠ 0` and `y ≠ 0` are not required because `0 ∣ 0` is true in
    `Nat`, so the divisibility holds trivially when either argument is zero
    (the result is `0`). -/
theorem lcm_multiple_of_x (x y r : u64)
    (h : lcm_u64.lcm x y = RustM.ok r) :
    x.toNat ∣ r.toNat := by
  sorry

/-- Postcondition (common multiple, right factor): whenever `lcm x y` returns
    successfully with value `r`, `r` is a multiple of `y` (in `Nat`). Captures
    the Rust property test `prop_result_is_multiple_of_y`. Stated separately
    from `lcm_multiple_of_x` because the implementation is asymmetric
    (`x * (y / gcd)`), so the two divisibilities are not the same proof. -/
theorem lcm_multiple_of_y (x y r : u64)
    (h : lcm_u64.lcm x y = RustM.ok r) :
    y.toNat ∣ r.toNat := by
  sorry

/-- Postcondition (least common multiple): whenever `lcm x y` returns
    successfully with value `r`, no positive `Nat` strictly less than `r` is
    divisible by both `x` and `y`. Captures the Rust property test
    `prop_result_is_least_common_multiple`, which is independent of the
    "common multiple" tests: a buggy implementation could return `x * y`
    (always a common multiple) and still satisfy `lcm_multiple_of_x` and
    `lcm_multiple_of_y` — this clause rules that out.

    Stated against `Nat` divisibility (`x.toNat ∣ z`) because the witness
    range `0 < z < r.toNat` is over `Nat`. The preconditions `x ≠ 0` and
    `y ≠ 0` mirror the property test's `1u64..25` ranges and avoid
    degenerate cases (when `r = 0` the claim is vacuously true anyway). -/
theorem lcm_is_least (x y r : u64)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (h : lcm_u64.lcm x y = RustM.ok r) :
    ∀ z : Nat, 0 < z → z < r.toNat → ¬ (x.toNat ∣ z ∧ y.toNat ∣ z) := by
  sorry

/-- Postcondition (commutativity / symmetry): `lcm` is symmetric in its
    arguments. Captures the Rust property test `prop_commutative`. The
    implementation is asymmetric (`x * (y / gcd(x, y))`), so this is a
    non-trivial claim — including on overflow-adjacent inputs (e.g.
    `(1, u64::MAX)`, `(2, 0x8000_…)`) where the `y / gcd` rearrangement
    is what keeps both orderings within `u64`'s range. Stated as an
    equation in `RustM u64`, so it covers both the `ok` and `fail` cases
    uniformly. -/
theorem lcm_commutative (x y : u64) :
    lcm_u64.lcm x y = lcm_u64.lcm y x := by
  sorry

end Lcm_u64Obligations
