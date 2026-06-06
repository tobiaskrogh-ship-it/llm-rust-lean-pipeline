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
    early-return branch fires and returns `0 ||| y = y`. Stated with `pure`
    rather than `RustM.ok` so the `rw` chains downstream feed straight into
    `pure_bind`. -/
private theorem gcd_u64_zero_left (y : u64) :
    lcm_u64.gcd_u64 0 y = pure y := by
  unfold lcm_u64.gcd_u64
  -- The first conjunct of the early-return guard is `(0 == 0) = true`, so the
  -- short-circuit `||?` returns true and we land in the then-branch.
  simp only [rust_primitives.cmp.eq, rust_primitives.hax.logical_op.or,
             pure_bind, beq_self_eq_true, Bool.true_or, ↓reduceIte]
  -- Goal now: `(0 |||? y) = pure y` where `|||?` is `pure (0 ||| y)`.
  show (pure ((0 : u64) ||| y) : RustM u64) = pure y
  congr 1
  apply UInt64.toNat_inj.mp
  simp

/-- Helper: `gcd_u64 x 0 = pure x` — symmetric early-return when the second
    argument is zero. -/
private theorem gcd_u64_zero_right (x : u64) :
    lcm_u64.gcd_u64 x 0 = pure x := by
  unfold lcm_u64.gcd_u64
  simp only [rust_primitives.cmp.eq, rust_primitives.hax.logical_op.or,
             pure_bind, beq_self_eq_true, Bool.or_true, ↓reduceIte]
  show (pure (x ||| (0 : u64)) : RustM u64) = pure x
  congr 1
  apply UInt64.toNat_inj.mp
  simp

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
    -- Both arguments are concrete `0`; the function reduces by computation.
    simp only [rust_primitives.cmp.eq, rust_primitives.hax.logical_op.and,
               pure_bind, beq_self_eq_true, Bool.and_self, ↓reduceIte]
    rfl
  · -- `y ≠ 0`: take the else branch via gcd.
    have h_eq_y : (y == (0 : u64)) = false := by
      simp [BEq.beq, hy]
    simp only [rust_primitives.cmp.eq, rust_primitives.hax.logical_op.and,
               pure_bind, beq_self_eq_true, Bool.true_and, h_eq_y,
               ↓reduceIte]
    -- Goal: `gcd_u64 0 y >>= fun gcd => 0 *? (← y /? gcd) = RustM.ok 0`
    rw [gcd_u64_zero_left]
    -- `pure y >>= ...`; reduce.
    simp only [pure_bind]
    -- Goal now: `(do let q ← y /? y; 0 *? q) = RustM.ok 0`
    show (do let q ← (rust_primitives.ops.arith.Div.div y y : RustM u64)
             rust_primitives.ops.arith.Mul.mul (0 : u64) q) = RustM.ok 0
    simp only [rust_primitives.ops.arith.Div.div, if_neg hy, pure_bind]
    -- `y / y = 1` for nonzero `y`.
    have h_pos : 0 < y.toNat := by
      rw [Nat.pos_iff_ne_zero]
      intro hh
      apply hy
      apply UInt64.toNat_inj.mp
      simp [hh]
    have hyy : y / y = 1 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_div]
      rw [Nat.div_self h_pos]
      rfl
    rw [hyy]
    show (rust_primitives.ops.arith.Mul.mul (0 : u64) 1 : RustM u64) = RustM.ok 0
    simp only [rust_primitives.ops.arith.Mul.mul]
    have h_no_ovf :
        BitVec.umulOverflow ((0 : u64).toBitVec) ((1 : u64).toBitVec) = false := by
      decide
    rw [h_no_ovf, if_neg (by decide)]
    rfl

/-- Postcondition (zero is absorbing, right): for every `x : u64`, `lcm x 0`
    successfully returns `0`. Captures the `lcm(v, 0)` direction of the Rust
    property test `prop_zero_is_absorbing`. When `x = 0` the early-return
    branch fires; when `x ≠ 0` we have `gcd_u64 x 0 = x`, then
    `x *? (0 / x) = x *? 0 = ok 0`. -/
theorem lcm_zero_right (x : u64) :
    lcm_u64.lcm x 0 = RustM.ok 0 := by
  unfold lcm_u64.lcm
  by_cases hx : x = 0
  · subst hx
    simp only [rust_primitives.cmp.eq, rust_primitives.hax.logical_op.and,
               pure_bind, beq_self_eq_true, Bool.and_self, ↓reduceIte]
    rfl
  · have h_eq_x : (x == (0 : u64)) = false := by
      simp [BEq.beq, hx]
    simp only [rust_primitives.cmp.eq, rust_primitives.hax.logical_op.and,
               pure_bind, beq_self_eq_true, h_eq_x, Bool.false_and,
               ↓reduceIte]
    rw [gcd_u64_zero_right]
    simp only [pure_bind]
    show (do let q ← (rust_primitives.ops.arith.Div.div (0 : u64) x : RustM u64)
             rust_primitives.ops.arith.Mul.mul x q) = RustM.ok 0
    simp only [rust_primitives.ops.arith.Div.div, if_neg hx, pure_bind]
    -- `0 / x = 0`.
    have h0x : (0 : u64) / x = 0 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_div]
      simp
    rw [h0x]
    show (rust_primitives.ops.arith.Mul.mul x 0 : RustM u64) = RustM.ok 0
    simp only [rust_primitives.ops.arith.Mul.mul]
    have h_no_ovf :
        BitVec.umulOverflow x.toBitVec ((0 : u64).toBitVec) = false := by
      have : ¬ UInt64.mulOverflow x 0 := by
        rw [UInt64.mulOverflow_iff]; simp
      simpa [UInt64.mulOverflow] using this
    rw [h_no_ovf, if_neg (by decide)]
    show RustM.ok (x * 0) = RustM.ok 0
    -- `congr 1` reduces this to `x * 0 = 0`, which Lean closes automatically
    -- via the `BitVec.mul_zero` simp set baked into `congr`.
    congr 1

/-- Postcondition (common multiple, left factor): whenever `lcm x y` returns
    successfully with value `r`, `r` is a multiple of `x` (in `Nat`). Captures
    the Rust property test `prop_result_is_multiple_of_x`.

    Left as `sorry`: this requires reasoning about the value of `gcd_u64 x y`
    through the Stein's-algorithm `while_loop`, which would need a full loop
    invariant relating `m`, `n`, and the gcd of the original inputs. The
    available reference examples do not cover `while_loop`-with-postcondition
    proofs at all (`average_*` are straight-line, `factorial`/`sum_to_n` use
    `partial_fixpoint` recursion), so the loop-invariant pattern would have to
    be invented from prelude internals. -/
theorem lcm_multiple_of_x (x y r : u64)
    (h : lcm_u64.lcm x y = RustM.ok r) :
    x.toNat ∣ r.toNat := by
  sorry

/-- Postcondition (common multiple, right factor): whenever `lcm x y` returns
    successfully with value `r`, `r` is a multiple of `y` (in `Nat`).

    Left as `sorry` for the same reason as `lcm_multiple_of_x` — it requires
    a loop invariant for `gcd_u64`'s Stein's-algorithm `while_loop`. -/
theorem lcm_multiple_of_y (x y r : u64)
    (h : lcm_u64.lcm x y = RustM.ok r) :
    y.toNat ∣ r.toNat := by
  sorry

/-- Postcondition (least common multiple): whenever `lcm x y` returns
    successfully with value `r`, no positive `Nat` strictly less than `r` is
    divisible by both `x` and `y`.

    Left as `sorry`: in addition to the `gcd_u64` loop-invariant analysis
    needed for the divisibility lemmas above, this clause requires the
    minimality side of the gcd characterization (every common divisor of `x`
    and `y` divides `gcd_u64 x y`). No reference example exercises that. -/
theorem lcm_is_least (x y r : u64)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (h : lcm_u64.lcm x y = RustM.ok r) :
    ∀ z : Nat, 0 < z → z < r.toNat → ¬ (x.toNat ∣ z ∧ y.toNat ∣ z) := by
  sorry

/-- Postcondition (commutativity / symmetry): `lcm` is symmetric in its
    arguments.

    Left as `sorry`: the implementation is genuinely asymmetric
    (`x * (y / gcd)`), so commutativity reduces to two facts that both depend
    on the value of `gcd_u64`: (i) `gcd_u64 x y = gcd_u64 y x` (a loop-symmetry
    claim about Stein's algorithm), and (ii) `x * (y / gcd) = y * (x / gcd)`
    when `gcd | x` and `gcd | y` (a Nat-level rearrangement that needs the
    divisibility facts in turn). Both depend on a loop invariant for
    `gcd_u64`'s `while_loop`, which the available reference examples do not
    cover. -/
theorem lcm_commutative (x y : u64) :
    lcm_u64.lcm x y = lcm_u64.lcm y x := by
  sorry

end Lcm_u64Obligations
