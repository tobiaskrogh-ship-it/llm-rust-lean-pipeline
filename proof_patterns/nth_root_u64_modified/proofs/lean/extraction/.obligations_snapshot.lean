-- Companion obligations file for the `nth_root_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import nth_root_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Nth_root_u64Obligations

/-! ## `sqrt_u64` contract clauses

`sqrt_u64 : u64 → RustM u64` is documented as returning the truncated
principal square root. The contract has two universal bounds:

  * **Lower bound** — `r² ≤ a` (always, no precondition).
  * **Upper bound** — `a < (r+1)²`, stated at the `Nat` level so the
    "modulo u64 overflow" caveat from the Rust property test
    disappears (when `r = 2³² − 1` the product `(r+1)*(r+1)` equals
    `2⁶⁴`, still strictly exceeding `a.toNat ≤ 2⁶⁴ − 1`).

The function is total: no precondition is needed. -/

/-- Master existential for `sqrt_u64`: returns some `r` simultaneously
    satisfying the lower and upper square-root bounds. The individual
    contract clauses below project out of this lemma. -/
theorem sqrt_u64_postcondition (a : u64) :
    ∃ r : u64, nth_root_u64.sqrt_u64 a = RustM.ok r ∧
      r.toNat * r.toNat ≤ a.toNat ∧
      a.toNat < (r.toNat + 1) * (r.toNat + 1) := by
  sorry

/-- Totality / no-panic for `sqrt_u64`. The Rust source has no `panic!`;
    failure modes (`/?` divisor of zero on the initial guess, `+?`
    overflow on `a/x + x`, `>>>?` shift-overflow on the halving,
    `<<<?` shift-overflow on the power-of-two guess) are all ruled
    out by the loop invariants summarised in `sqrt_u64_postcondition`. -/
theorem sqrt_u64_total (a : u64) :
    ∃ r : u64, nth_root_u64.sqrt_u64 a = RustM.ok r := by
  obtain ⟨r, hr, _, _⟩ := sqrt_u64_postcondition a
  exact ⟨r, hr⟩

/-- Lower bound (independent clause) for `sqrt_u64`: `sqrt(a)² ≤ a`.
    Captures the property test `prop_sqrt_lower_bound`. A buggy
    implementation that returns too large a value would fail here. -/
theorem sqrt_u64_lower_bound (a : u64) :
    ∃ r : u64, nth_root_u64.sqrt_u64 a = RustM.ok r ∧
      r.toNat * r.toNat ≤ a.toNat := by
  obtain ⟨r, hr, hlb, _⟩ := sqrt_u64_postcondition a
  exact ⟨r, hr, hlb⟩

/-- Upper bound (independent clause) for `sqrt_u64`: `a < (sqrt(a) + 1)²`,
    stated at `Nat`-level so the Rust test's "modulo overflow" vacuous
    case becomes a genuine inequality that still holds (since
    `a.toNat < 2⁶⁴ ≤ (r+1)²` when `r = 2³² − 1`). Captures
    `prop_sqrt_upper_bound`. Independent from the lower bound: an
    implementation always returning `0` would pass the lower bound
    but fail this one. -/
theorem sqrt_u64_upper_bound (a : u64) :
    ∃ r : u64, nth_root_u64.sqrt_u64 a = RustM.ok r ∧
      a.toNat < (r.toNat + 1) * (r.toNat + 1) := by
  obtain ⟨r, hr, _, hub⟩ := sqrt_u64_postcondition a
  exact ⟨r, hr, hub⟩

/-! ## `cbrt_u64` contract clauses

`cbrt_u64 : u64 → RustM u64` is documented as returning the truncated
principal cube root. Same two-clause shape as `sqrt_u64`, exponent 3. -/

/-- Master existential for `cbrt_u64`: returns some `r` simultaneously
    satisfying the lower and upper cube-root bounds. -/
theorem cbrt_u64_postcondition (a : u64) :
    ∃ r : u64, nth_root_u64.cbrt_u64 a = RustM.ok r ∧
      r.toNat * r.toNat * r.toNat ≤ a.toNat ∧
      a.toNat < (r.toNat + 1) * (r.toNat + 1) * (r.toNat + 1) := by
  sorry

/-- Totality / no-panic for `cbrt_u64`. -/
theorem cbrt_u64_total (a : u64) :
    ∃ r : u64, nth_root_u64.cbrt_u64 a = RustM.ok r := by
  obtain ⟨r, hr, _, _⟩ := cbrt_u64_postcondition a
  exact ⟨r, hr⟩

/-- Lower bound (independent clause) for `cbrt_u64`: `cbrt(a)³ ≤ a`.
    Captures the property test `prop_cbrt_lower_bound`. -/
theorem cbrt_u64_lower_bound (a : u64) :
    ∃ r : u64, nth_root_u64.cbrt_u64 a = RustM.ok r ∧
      r.toNat * r.toNat * r.toNat ≤ a.toNat := by
  obtain ⟨r, hr, hlb, _⟩ := cbrt_u64_postcondition a
  exact ⟨r, hr, hlb⟩

/-- Upper bound (independent clause) for `cbrt_u64`: `a < (cbrt(a) + 1)³`,
    stated at `Nat`-level. Captures `prop_cbrt_upper_bound`. -/
theorem cbrt_u64_upper_bound (a : u64) :
    ∃ r : u64, nth_root_u64.cbrt_u64 a = RustM.ok r ∧
      a.toNat < (r.toNat + 1) * (r.toNat + 1) * (r.toNat + 1) := by
  obtain ⟨r, hr, _, hub⟩ := cbrt_u64_postcondition a
  exact ⟨r, hr, hub⟩

/-! ## `nth_root` contract clauses

`nth_root : u64 → u32 → RustM u64` is documented as returning the
truncated principal `n`-th root of its first argument for `n ≥ 1`.
The contract has three clauses:

  * **Failure (panic)** — `n == 0` triggers a u32 underflow inside
    the `n - 1` subtraction. Hax models this as
    `RustM.fail Error.integerOverflow`, which is the same observable
    effect as the original `panic!("…")` (see the crate-level comment
    on why `panic!` with a format string is rewritten this way).
    Captured by the `#[should_panic] zeroth_root` test.
  * **Lower bound** — `r^n ≤ a` for any `n ≥ 1` and any `a`. Captures
    `prop_nth_root_lower_bound`.
  * **Upper bound** — `a < (r+1)^n`, stated at the `Nat` level so the
    "modulo overflow" caveat from the Rust property test drops out
    (when `n ≥ 64` the bound `(1+1)^n ≥ 2⁶⁴ > a.toNat` is automatic).
    Captures `prop_nth_root_upper_bound`.

Feasibility note: the proptest samples `n in 1u32..=128`, but the
universal statement (any `n ≥ 1`) is in fact correct in the Lean
model — the `n ≥ 64` branch returns `1` (or `0` at `a = 0`) from a
fast-path arm that never touches the Newton iteration, with bounds
that hold trivially. So we use the full universal precondition
`1 ≤ n.toNat` rather than mimicking the proptest's sampling range. -/

/-- Master existential for `nth_root` (precondition `n ≥ 1`):
    returns some `r` simultaneously satisfying the lower and
    upper `n`-th-root bounds. -/
theorem nth_root_postcondition (self_val : u64) (n : u32) (hn : 1 ≤ n.toNat) :
    ∃ r : u64, nth_root_u64.nth_root self_val n = RustM.ok r ∧
      r.toNat ^ n.toNat ≤ self_val.toNat ∧
      self_val.toNat < (r.toNat + 1) ^ n.toNat := by
  sorry

/-- Totality / no-panic for `nth_root` in the valid range `n ≥ 1`.
    Outside this range the function panics; see `nth_root_zero_panics`. -/
theorem nth_root_total (self_val : u64) (n : u32) (hn : 1 ≤ n.toNat) :
    ∃ r : u64, nth_root_u64.nth_root self_val n = RustM.ok r := by
  obtain ⟨r, hr, _, _⟩ := nth_root_postcondition self_val n hn
  exact ⟨r, hr⟩

/-- Lower bound (independent clause) for `nth_root`: `r^n ≤ a` for any
    `n ≥ 1`. Captures `prop_nth_root_lower_bound`. -/
theorem nth_root_lower_bound (self_val : u64) (n : u32) (hn : 1 ≤ n.toNat) :
    ∃ r : u64, nth_root_u64.nth_root self_val n = RustM.ok r ∧
      r.toNat ^ n.toNat ≤ self_val.toNat := by
  obtain ⟨r, hr, hlb, _⟩ := nth_root_postcondition self_val n hn
  exact ⟨r, hr, hlb⟩

/-- Upper bound (independent clause) for `nth_root`: `a < (r+1)^n`,
    stated at `Nat`-level so the Rust test's vacuous overflow case
    becomes a genuine inequality. Captures `prop_nth_root_upper_bound`.
    Independent from the lower bound (an always-`0` implementation
    would pass the lower bound and fail this one). -/
theorem nth_root_upper_bound (self_val : u64) (n : u32) (hn : 1 ≤ n.toNat) :
    ∃ r : u64, nth_root_u64.nth_root self_val n = RustM.ok r ∧
      self_val.toNat < (r.toNat + 1) ^ n.toNat := by
  obtain ⟨r, hr, _, hub⟩ := nth_root_postcondition self_val n hn
  exact ⟨r, hr, hub⟩

/-! ## Failure condition: panic on `n = 0` -/

/-- `nth_root(a, 0)` panics for any `a` via u32 underflow in the
    `n - 1` subtraction. Hax models this as
    `RustM.fail .integerOverflow`, matching the observable effect of
    the original `panic!("…")` in `num-integer-0.1.46`. Captures the
    `#[should_panic] zeroth_root` test, which exercises this on the
    specific input `nth_root(123u64, 0)`. Stated universally because
    the panic depends only on `n = 0`, not on the value of `a`. -/
theorem nth_root_zero_panics (self_val : u64) :
    nth_root_u64.nth_root self_val 0 = RustM.fail .integerOverflow := by
  sorry

/-! ## Boundary cases (specific values pinned by the `bit_size` test)

The `bit_size` integration test pins two specific outputs at the
extreme corner of the input domain. They are derivable from the
master postcondition plus arithmetic, but the test exists as a
spot-check and they correspond to distinct code paths (`n ≥ 64`
fast-return arm vs. Newton arm at the maximal practical `n`). -/

/-- `nth_root(u64::MAX, 63) = 2`. Captures the first assertion of the
    `bit_size` test. Exercises the Newton arm at the largest exponent
    that still triggers iteration (`n = 63 < 64`, `a ≥ (1 << 63)`). -/
theorem nth_root_max_63 :
    nth_root_u64.nth_root 18446744073709551615 63 = RustM.ok 2 := by
  sorry

/-- `nth_root(u64::MAX, 64) = 1`. Captures the second assertion of the
    `bit_size` test. Exercises the `n ≥ 64` fast-path arm, which
    returns `1` immediately when `a > 0` without invoking the
    Newton iteration. -/
theorem nth_root_max_64 :
    nth_root_u64.nth_root 18446744073709551615 64 = RustM.ok 1 := by
  sorry

end Nth_root_u64Obligations
