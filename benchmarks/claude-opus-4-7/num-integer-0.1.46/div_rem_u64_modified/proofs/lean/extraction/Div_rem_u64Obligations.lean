-- Companion obligations file for the `div_rem_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import div_rem_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Div_rem_u64Obligations

/-- Postcondition (success / closed form):
    when `y ≠ 0`, `div_rem` succeeds and returns the pair
    `(x / y, x % y)`. This subsumes the concrete unit tests
    `doc_test_examples` and `test_div_rem`, the equational checks
    in `agrees_with_source` (the original `num-integer` body
    reduces to `(*self / *other, *self % *other)` on unsigned
    types), and the random sweep `postcondition_division_rule_random`. -/
theorem div_rem_postcondition (x y : u64) (hy : y ≠ 0) :
    div_rem_u64.div_rem x y =
      RustM.ok (rust_primitives.hax.Tuple2.mk (x / y) (x % y)) := by
  -- Unfold the function and the two fallible ops; both `if y = 0` branches
  -- collapse to the `pure` arm under `hy`, leaving `pure (Tuple2.mk (x/y) (x%y))`.
  simp only [div_rem_u64.div_rem,
             rust_primitives.ops.arith.Div.div,
             rust_primitives.ops.arith.Rem.rem,
             if_neg hy]
  rfl

/-- Failure condition (precondition violation):
    when `y = 0`, `div_rem` panics with `Error.divisionByZero`
    — the first fallible operation `x /? y` short-circuits the `do`-block
    on a zero divisor. Captures the `#[should_panic]` tests
    `panics_on_zero_divisor_nonzero_dividend` and
    `panics_on_zero_divisor_zero_dividend` (the failure is universal in `x`). -/
theorem div_rem_div_by_zero_failure (x : u64) :
    div_rem_u64.div_rem x 0 = RustM.fail .divisionByZero := by
  -- Unfolding the function and `Div.div` already reduces the `if 0 = 0`
  -- branch to `.fail .divisionByZero`; `simp only` collapses the `do`-bind
  -- on a failure to the failure itself, and the goal closes by `rfl`.
  simp only [div_rem_u64.div_rem,
             rust_primitives.ops.arith.Div.div]
  rfl

/-- Postcondition (Euclidean / division-rule identity):
    for every valid call (`y ≠ 0`) producing `RustM.ok (q, r)`,
    the identity `q * y + r = x` holds at the `Nat` level. Captures
    the `d * q + r == n` assertion in `test_division_rule` /
    `test_div_rem`, the same identity in `postcondition_division_rule`,
    and its random sweep `postcondition_division_rule_random`. -/
theorem div_rem_quotient_times_divisor_plus_remainder_eq
    (x y q r : u64) (hy : y ≠ 0)
    (hres : div_rem_u64.div_rem x y =
              RustM.ok (rust_primitives.hax.Tuple2.mk q r)) :
    q.toNat * y.toNat + r.toNat = x.toNat := by
  -- Replace the LHS of `hres` by its closed form, so we can read off `q` and `r`.
  rw [div_rem_postcondition x y hy] at hres
  -- `hres : RustM.ok (Tuple2.mk (x/y) (x%y)) = RustM.ok (Tuple2.mk q r)` —
  -- peel `Option.some`, `Except.ok`, then the `Tuple2.mk` constructor.
  injection hres with hres
  injection hres with hres
  injection hres with hq hr
  subst hq
  subst hr
  -- Goal: (x / y).toNat * y.toNat + (x % y).toNat = x.toNat.
  -- `Nat.div_add_mod` is stated as `y * (x/y) + x%y = x`; rotate the
  -- multiplication into the form the goal expects, then close.
  rw [UInt64.toNat_div, UInt64.toNat_mod,
      Nat.mul_comm (x.toNat / y.toNat) y.toNat]
  exact Nat.div_add_mod x.toNat y.toNat

/-- Postcondition (remainder bound):
    for every valid call (`y ≠ 0`) producing `RustM.ok (q, r)`,
    `r < y` (at the `Nat` level). Captures the `assert!(r < d)`
    half of `postcondition_division_rule` and its random sweep
    `postcondition_division_rule_random`. -/
theorem div_rem_remainder_lt_divisor
    (x y q r : u64) (hy : y ≠ 0)
    (hres : div_rem_u64.div_rem x y =
              RustM.ok (rust_primitives.hax.Tuple2.mk q r)) :
    r.toNat < y.toNat := by
  rw [div_rem_postcondition x y hy] at hres
  injection hres with hres
  injection hres with hres
  injection hres with hq hr
  subst hr
  -- Goal: (x % y).toNat < y.toNat.
  rw [UInt64.toNat_mod]
  -- `y.toNat > 0` follows from `y ≠ 0` via the toNat injection on UInt64.
  have hy_pos : 0 < y.toNat := by
    rcases Nat.eq_zero_or_pos y.toNat with h | h
    · exfalso
      apply hy
      apply UInt64.toNat.inj
      simpa using h
    · exact h
  exact Nat.mod_lt _ hy_pos

end Div_rem_u64Obligations
