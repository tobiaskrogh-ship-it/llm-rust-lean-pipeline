-- Companion obligations file for the `div_floor_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import div_floor_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Div_floor_u64Obligations

/-- Postcondition (success / closed form):
    when `y ≠ 0`, `div_floor` succeeds and returns exactly `x / y`.
    This subsumes the concrete unit tests in `test_div_floor`
    (e.g. `div_floor 10 3 = 3`) and the `agrees_with_source` cross-check
    (since the original `num-integer` body reduces to `*self / *other`,
    which on `u64` is the same `/` used here). -/
theorem div_floor_postcondition (x y : u64) (hy : y ≠ 0) :
    div_floor_u64.div_floor x y = RustM.ok (x / y) := by
  -- Unfold the function and the `Div.div` instance for unsigned UInt64:
  --   `div x y := if y = 0 then .fail .divisionByZero else pure (x / y)`.
  simp only [div_floor_u64.div_floor, rust_primitives.ops.arith.Div.div]
  rw [if_neg hy]
  rfl

/-- Failure condition (precondition violation):
    when `y = 0`, `div_floor` panics with `Error.divisionByZero`.
    This captures the `#[should_panic]` test `panics_on_zero_divisor`:
    a buggy implementation that silently returned, say, 0 or u64::MAX
    on a zero divisor would be ruled out by this theorem. -/
theorem div_floor_div_by_zero_failure (x : u64) :
    div_floor_u64.div_floor x 0 = RustM.fail .divisionByZero := by
  -- After unfolding, simp normalises the condition `0 = 0` to `True`;
  -- the `if_true` simp lemma then closes the goal.
  simp [div_floor_u64.div_floor, rust_primitives.ops.arith.Div.div]

/-- Postcondition (Euclidean lower bound):
    for every valid call (`y ≠ 0`) producing `RustM.ok q`,
    `q * y ≤ x` (at the `Nat` level, to side-step `u64` overflow concerns).
    This is one half of the `postcondition_floor_division` test
    (`q * d ≤ n`). -/
theorem div_floor_quotient_times_divisor_le (x y q : u64) (hy : y ≠ 0)
    (hres : div_floor_u64.div_floor x y = RustM.ok q) :
    q.toNat * y.toNat ≤ x.toNat := by
  -- Reduce `hres` to `q = x / y` via the closed-form postcondition.
  rw [div_floor_postcondition x y hy] at hres
  -- After `rw`, `hres : RustM.ok (x / y) = RustM.ok q`,
  -- definitionally `some (.ok (x / y)) = some (.ok q)`.
  have h1 : Option.some (Except.ok (x / y) : Except Error u64) =
            Option.some (Except.ok q) := hres
  simp only [Option.some.injEq, Except.ok.injEq] at h1
  -- `h1 : x / y = q`.
  subst h1
  -- Goal: `(x / y).toNat * y.toNat ≤ x.toNat`.
  rw [UInt64.toNat_div]
  exact Nat.div_mul_le_self _ _

/-- Postcondition (Euclidean remainder bound):
    for every valid call (`y ≠ 0`) producing `RustM.ok q`,
    `x − q*y < y` (at the `Nat` level).
    This is the other half of `postcondition_floor_division`
    (`n − q*d < d`). -/
theorem div_floor_remainder_lt_divisor (x y q : u64) (hy : y ≠ 0)
    (hres : div_floor_u64.div_floor x y = RustM.ok q) :
    x.toNat - q.toNat * y.toNat < y.toNat := by
  rw [div_floor_postcondition x y hy] at hres
  have h1 : Option.some (Except.ok (x / y) : Except Error u64) =
            Option.some (Except.ok q) := hres
  simp only [Option.some.injEq, Except.ok.injEq] at h1
  subst h1
  rw [UInt64.toNat_div]
  -- Goal: `x.toNat - x.toNat / y.toNat * y.toNat < y.toNat`.
  -- Need `0 < y.toNat` to apply `Nat.mod_lt` and the standard
  -- `m / k * k + m % k = m` decomposition.
  have hy_n : y.toNat ≠ 0 := by
    intro h0
    apply hy
    -- `y = 0` follows from `y.toNat = (0 : u64).toNat = 0` by injectivity of `UInt64.toNat`.
    exact UInt64.toNat_inj.mp (by simpa using h0)
  have hpos : 0 < y.toNat := Nat.pos_of_ne_zero hy_n
  have hmod_lt : x.toNat % y.toNat < y.toNat := Nat.mod_lt _ hpos
  -- `Nat.mod_add_div' m k : m % k + m / k * k = m` (primed: order matches the goal).
  have hdecomp : x.toNat % y.toNat + x.toNat / y.toNat * y.toNat = x.toNat :=
    Nat.mod_add_div' x.toNat y.toNat
  omega

end Div_floor_u64Obligations
