-- Companion obligations file for the `cbrt_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import cbrt_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Cbrt_u64Obligations

/-! ## Master postcondition

The Rust source `cbrt : u64 → u64` returns the truncated integer cube
root: the largest `r : u64` with `r³ ≤ x`. Its contract is captured by
two universal bounds on the result:

  * **Lower bound** — `r³ ≤ x`        (P1: "r is a cube-root candidate"),
  * **Upper bound** — `x < (r+1)³`    (P2: "r is the *greatest* such").

Both bounds are stated at `Nat`-level so that the "modulo u64 overflow"
caveat from the Rust property test disappears — when
`r = cbrt(2^64 − 1) = 2_642_245`, the cube `(r+1)³ ≈ 1.85 × 10^19`
exceeds `2^64`, so the genuine `Nat` inequality
`x.toNat < (r+1)³` still holds (since `x.toNat < 2^64`).

The function is total: no precondition is needed. For every `u64` input
the result fits in `u64` (`cbrt(2^64 − 1) = 2_642_245 < 2^32`), and the
intermediate partial operators (`*?`/`+?`/`/?`/`<<<?`/`>>>?`) inside
the helpers are discharged by branch-specific invariants:

  * `a < 8`        — early return `0` or `1`, no arithmetic.
  * `a ≤ u32::MAX` — Hacker's-Delight `icbrt2` running entirely in `u32`,
                     with the bit-width bound `s ≤ 10` keeping every shift
                     and add in range.
  * `a > u32::MAX` — `cbrt_guess_u64` produces `g ≤ 2^22 < 2^32`, so the
                     Newton recurrence `(a/(x*x) + 2*x)/3` keeps `x ≤ 2^32`
                     invariantly; therefore `x*x < 2^64`, `a/(x*x) > 0`
                     (so the divisor in the *next* step is positive),
                     `2*x < 2^33`, and `a/(x*x) + 2*x < 2^64`.

This master theorem bundles both bounds with the function's totality
(`= RustM.ok r`); the individual contract clauses below project out of
this lemma. -/
theorem cbrt_postcondition (x : u64) :
    ∃ r : u64, cbrt_u64.cbrt x = RustM.ok r ∧
      r.toNat * r.toNat * r.toNat ≤ x.toNat ∧
      x.toNat < (r.toNat + 1) * (r.toNat + 1) * (r.toNat + 1) := by
  sorry

/-! ## Contract clauses derived from the master postcondition. -/

/-- Totality / no-panic. The Rust source has no `panic!`; failure modes
    (`/?` divisor of zero on the first Newton step, `*?`/`+?` overflow
    on `x*x`/`a/(x*x) + 2*x`, `<<<?`/`>>>?` shift-overflow on the
    `icbrt2` and `pow2_loop` helpers) are all ruled out by the
    branch-specific invariants summarised in `cbrt_postcondition`. -/
theorem cbrt_total (x : u64) :
    ∃ r : u64, cbrt_u64.cbrt x = RustM.ok r := by
  obtain ⟨r, hr, _, _⟩ := cbrt_postcondition x
  exact ⟨r, hr⟩

/-- Lower bound (independent clause): `cbrt(x)³ ≤ x`. Captures the Rust
    property test `prop_cube_le_x` directly. A buggy implementation that
    returns too large a value (e.g. `x` itself for `x ≥ 2`, or
    `cbrt x + 1` on non-perfect cubes) is caught here. Stated at
    `Nat`-level so that the `checked_pow(3)` guard from the Rust test
    (which only triggers for incorrect oversize results) drops out. -/
theorem cbrt_lower_bound (x : u64) :
    ∃ r : u64, cbrt_u64.cbrt x = RustM.ok r ∧
      r.toNat * r.toNat * r.toNat ≤ x.toNat := by
  obtain ⟨r, hr, hlb, _⟩ := cbrt_postcondition x
  exact ⟨r, hr, hlb⟩

/-- Upper bound (independent clause): `x < (cbrt(x) + 1)³`. Captures the
    Rust property test `prop_x_lt_next_cube`. Independent from the lower
    bound: an implementation that always returns `0` would pass the
    lower bound but fail this one. Stated at `Nat`-level: the Rust
    test's "modulo overflow" vacuous case (when `(r+1)³` doesn't fit in
    `u64`) becomes the genuine inequality `x.toNat < (r+1)³` in `Nat`,
    which still holds since `x.toNat < 2^64 ≤ (r+1)³` in that regime. -/
theorem cbrt_upper_bound (x : u64) :
    ∃ r : u64, cbrt_u64.cbrt x = RustM.ok r ∧
      x.toNat < (r.toNat + 1) * (r.toNat + 1) * (r.toNat + 1) := by
  obtain ⟨r, hr, _, hub⟩ := cbrt_postcondition x
  exact ⟨r, hr, hub⟩

/-! ## Boundary cases (small-input early-return arm)

The Rust source dispatches `a < 8` via an explicit early-return that
sidesteps the `icbrt2` / Newton iteration: `cbrt 0 = 0`, `cbrt {1..7} = 1`.
These are corollaries of the master postcondition but pin the explicit
code path that the loop helpers never see. From the `cbrt_small_values`
test. -/

/-- Boundary case `cbrt 0 = 0`. Pins the `a = 0` arm of the early-return
    branch (`if a > 0 ... else 0`). Captures `cbrt(0) = 0` from
    `cbrt_small_values`. -/
theorem cbrt_zero : cbrt_u64.cbrt 0 = RustM.ok 0 := by
  unfold cbrt_u64.cbrt
  rfl

/-- Boundary case `cbrt 1 = 1`. Pins the `0 < a < 8` arm of the
    early-return branch. Captures `cbrt(1) = 1` from
    `cbrt_small_values`. -/
theorem cbrt_one : cbrt_u64.cbrt 1 = RustM.ok 1 := by
  unfold cbrt_u64.cbrt
  rfl

end Cbrt_u64Obligations
