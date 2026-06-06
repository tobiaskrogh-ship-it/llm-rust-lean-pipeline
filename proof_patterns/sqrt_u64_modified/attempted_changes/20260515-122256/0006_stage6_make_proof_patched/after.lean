-- Companion obligations file for the `sqrt_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import sqrt_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Sqrt_u64Obligations

/-! ## Postcondition: lower bound (`r² ≤ x`)

Captures the property test `prop_sqrt_lower_bound`: for the returned root `r`,
`r.toNat * r.toNat ≤ x.toNat`. A buggy implementation that returns too large a
value (e.g. `x` itself, or `r + 1` for non-perfect squares) is caught here.

Stated at the `Nat` level: a correct result satisfies `r ≤ 2^32 - 1`, so
`r * r` fits in `u64`; phrasing the inequality over `Nat` avoids embedding
the `checked_mul` overflow guard from the Rust test. -/
theorem sqrt_lower_bound (x : u64) :
    ∃ r : u64, sqrt_u64.sqrt x = RustM.ok r ∧ r.toNat * r.toNat ≤ x.toNat := by
  sorry

/-! ## Postcondition: upper bound (`x < (r+1)²`)

Captures the property test `prop_sqrt_upper_bound`: for the returned root `r`,
`x.toNat < (r.toNat + 1) * (r.toNat + 1)`. Independent from the lower bound —
an implementation always returning `0` would pass the lower bound but fail
this one.

Stated at the `Nat` level: `(r.toNat + 1) * (r.toNat + 1)` is `Nat` arithmetic,
so the Rust test's "vacuous when `(r+1)²` overflows `u64`" caveat folds in
automatically — when `(r+1)²` exceeds `2^64`, `x.toNat < (r+1)²` still holds
since `x.toNat < 2^64`. -/
theorem sqrt_upper_bound (x : u64) :
    ∃ r : u64, sqrt_u64.sqrt x = RustM.ok r
      ∧ x.toNat < (r.toNat + 1) * (r.toNat + 1) := by
  sorry

/-! ## Totality / no panic

Explicit "no failure mode" clause from the Rust contract comment ("Failures:
none — the function never panics"). For every `u64` input, `sqrt` returns a
value successfully. -/
theorem sqrt_total (x : u64) :
    ∃ v : u64, sqrt_u64.sqrt x = RustM.ok v := by
  sorry

/-! ## Specific values: small inputs

Each line of `sqrt_small` becomes one theorem. These pin down the function on
the `a < 4` branch of the implementation, which is the boundary the Rust
source explicitly handles. -/

theorem sqrt_zero : sqrt_u64.sqrt 0 = RustM.ok 0 := by
  unfold sqrt_u64.sqrt
  rfl

theorem sqrt_one : sqrt_u64.sqrt 1 = RustM.ok 1 := by
  unfold sqrt_u64.sqrt
  rfl

theorem sqrt_two : sqrt_u64.sqrt 2 = RustM.ok 1 := by
  unfold sqrt_u64.sqrt
  rfl

theorem sqrt_three : sqrt_u64.sqrt 3 = RustM.ok 1 := by
  unfold sqrt_u64.sqrt
  rfl

theorem sqrt_four : sqrt_u64.sqrt 4 = RustM.ok 2 := by
  sorry

/-! ## Specific values: doctest

The doc-test `sqrt_doctest` asserts three identities at `x = 12345`. Each
becomes one theorem. -/

theorem sqrt_doctest_exact :
    sqrt_u64.sqrt (12345 * 12345 : u64) = RustM.ok (12345 : u64) := by
  sorry

theorem sqrt_doctest_plus_one :
    sqrt_u64.sqrt (12345 * 12345 + 1 : u64) = RustM.ok (12345 : u64) := by
  sorry

theorem sqrt_doctest_minus_one :
    sqrt_u64.sqrt (12345 * 12345 - 1 : u64) = RustM.ok (12344 : u64) := by
  sorry

end Sqrt_u64Obligations
