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

/-- Helper: `gcd_u64 0 y = pure y` — when the first argument is zero, the
    early-return branch fires and returns `0 ||| y = y`. -/
private theorem gcd_u64_zero_left (y : u64) :
    lcm_u64.gcd_u64 0 y = RustM.ok y := by
  unfold lcm_u64.gcd_u64
  show (do
    let b ← (do let a ← rust_primitives.cmp.eq (0 : u64) 0
                let b ← rust_primitives.cmp.eq y 0
                rust_primitives.hax.logical_op.or a b)
    if b then ((0 : u64) |||? y) else _) = RustM.ok y
  simp [rust_primitives.cmp.eq, rust_primitives.hax.logical_op.or]
  show RustM.ok ((0 : u64) ||| y) = RustM.ok y
  congr 1
  exact UInt64.zero_or y

/-- Helper: `gcd_u64 x 0 = pure x` — symmetric early-return. -/
private theorem gcd_u64_zero_right (x : u64) :
    lcm_u64.gcd_u64 x 0 = RustM.ok x := by
  unfold lcm_u64.gcd_u64
  show (do
    let b ← (do let a ← rust_primitives.cmp.eq x 0
                let b ← rust_primitives.cmp.eq (0 : u64) 0
                rust_primitives.hax.logical_op.or a b)
    if b then (x |||? (0 : u64)) else _) = RustM.ok x
  simp [rust_primitives.cmp.eq, rust_primitives.hax.logical_op.or]
  show RustM.ok (x ||| (0 : u64)) = RustM.ok x
  congr 1
  exact UInt64.or_zero x

/-- Postcondition (zero is absorbing, left): for every `y : u64`, `lcm 0 y`
    successfully returns `0`. Captures one half of the Rust property test
    `prop_zero_is_absorbing` (the `lcm(0, v)` direction). When `y = 0` the
    function takes the explicit `x == 0 && y == 0` early-return branch; when
    `y ≠ 0` it goes through the gcd path with `gcd_u64 0 y = y`, then
    `0 *? (y / y) = 0 *? 1 = ok 0`. Either way the result is `ok 0`. -/
theorem lcm_zero_left (y : u64) :
    lcm_u64.lcm 0 y = RustM.ok 0 := by
  unfold lcm_u64.lcm
  by_cases hy : y = 0
  · subst hy
    show (do
      let b ← (do let a ← rust_primitives.cmp.eq (0 : u64) 0
                  let b ← rust_primitives.cmp.eq (0 : u64) 0
                  rust_primitives.hax.logical_op.and a b)
      if b then pure (0 : u64) else _) = RustM.ok 0
    simp [rust_primitives.cmp.eq, rust_primitives.hax.logical_op.and]
  · -- y ≠ 0: take else branch via gcd.
    have h_eq_y : (y == (0 : u64)) = false := by
      simp [BEq.beq]
      intro hh
      apply hy
      exact UInt64.toNat_inj.mp (by simp; omega)
    show (do
      let b ← (do let a ← rust_primitives.cmp.eq (0 : u64) 0
                  let b ← rust_primitives.cmp.eq y 0
                  rust_primitives.hax.logical_op.and a b)
      if b then pure (0 : u64)
      else (do let gcd ← lcm_u64.gcd_u64 0 y
               (0 : u64) *? (← y /? gcd))) = RustM.ok 0
    simp [rust_primitives.cmp.eq, rust_primitives.hax.logical_op.and, h_eq_y]
    -- Now goal: gcd_u64 0 y >>= fun gcd => 0 *? (← y /? gcd) = RustM.ok 0
    rw [gcd_u64_zero_left]
    -- pure y >>= ...
    show ((0 : u64) *? (← (y /? y))) = RustM.ok 0
    -- y /? y = pure 1 (since y ≠ 0)
    show (do let q ← (rust_primitives.ops.arith.Div.div y y : RustM u64)
             rust_primitives.ops.arith.Mul.mul (0 : u64) q) = RustM.ok 0
    simp only [rust_primitives.ops.arith.Div.div, if_neg hy, pure_bind]
    -- Now: 0 *? (y / y) where y / y = 1
    have hyy : y / y = 1 := UInt64.div_self hy
    rw [hyy]
    -- Goal: 0 *? 1 = RustM.ok 0
    show (rust_primitives.ops.arith.Mul.mul (0 : u64) 1 : RustM u64) = RustM.ok 0
    simp only [rust_primitives.ops.arith.Mul.mul]
    have h_no_ovf : BitVec.umulOverflow ((0 : u64).toBitVec) ((1 : u64).toBitVec) = false := by
      decide
    rw [if_neg (by rw [h_no_ovf]; decide)]
    rfl

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
