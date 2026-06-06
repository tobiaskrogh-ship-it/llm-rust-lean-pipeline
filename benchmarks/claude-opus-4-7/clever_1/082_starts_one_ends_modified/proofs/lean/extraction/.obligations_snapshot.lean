-- Companion obligations file for the `clever_082_starts_one_ends` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_082_starts_one_ends

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_082_starts_one_endsObligations

/-! ## Contract clauses

The Rust source contains the following contract-style tests:

  * `small_cases` — five unit pins: `starts_one_ends(0)=0`,
    `starts_one_ends(1)=1`, `starts_one_ends(2)=18`,
    `starts_one_ends(3)=180`, `starts_one_ends(4)=1800`.
  * `matches_brute_force (n in 0u64..=6)` — main postcondition: the
    closed form `18 · 10^(n-2)` agrees with an independent
    enumeration of "n-digit positives starting or ending with 1".
    For `n = 0` the convention is `0` and for `n = 1` only `1`
    qualifies, both of which are degenerate base cases.

Each becomes one independent `theorem`.

### Feasibility analysis

The body of `pow10_at` walks `acc ↦ acc *? 10` with `acc` starting
at `1`, so the intermediate values are `1, 10, 100, …, 10^(n-2)`.
The outer wrapper then multiplies by `18`.  The closed form
`18 · 10^(n-2)` fits in `u64` iff `n ≤ 20`:

  * `18 · 10^18 = 1.8·10^19 < 2^64 ≈ 1.84·10^19`  → succeeds at `n = 20`.
  * `18 · 10^19 = 1.8·10^20 > 2^64`               → overflows at `n = 21`.

For `n = 21` the inner `pow10_at(19, 1) = 10^19` still fits, but the
outer `18 *? 10^19` overflows; for `n ≥ 22` the inner walk itself
overflows when computing `10^20 = 10 · 10^19`.  Either way, the
function returns `.fail .integerOverflow` for every `n ≥ 21`.

We therefore state the closed-form postcondition with the explicit
range `2 ≤ n ≤ 20`, and a matching failure clause for `n ≥ 21`.
The proptest's range `0..=6` is a tiny slice of the true success
domain; the theorem we state is much stronger than the proptest. -/

/-! ## Unit pins from `small_cases`.

These literal values are independently asserted by the Rust test
suite.  Closing each with `native_decide` reduces the extracted
definition by kernel evaluation. -/

/-- Unit pin: `starts_one_ends(0) = 0`.  Base-case convention
    that `n = 0` yields no count. -/
theorem starts_one_ends_at_0 :
    clever_082_starts_one_ends.starts_one_ends 0 = RustM.ok 0 := by
  native_decide

/-- Unit pin: `starts_one_ends(1) = 1`.  Only `1` itself is a
    1-digit number that starts or ends with `1`. -/
theorem starts_one_ends_at_1 :
    clever_082_starts_one_ends.starts_one_ends 1 = RustM.ok 1 := by
  native_decide

/-- Unit pin: `starts_one_ends(2) = 18`.  Inclusion–exclusion at
    `n = 2` gives `18 · 10^0 = 18`. -/
theorem starts_one_ends_at_2 :
    clever_082_starts_one_ends.starts_one_ends 2 = RustM.ok 18 := by
  native_decide

/-- Unit pin: `starts_one_ends(3) = 180`.  Closed form at `n = 3`:
    `18 · 10^1 = 180`. -/
theorem starts_one_ends_at_3 :
    clever_082_starts_one_ends.starts_one_ends 3 = RustM.ok 180 := by
  native_decide

/-- Unit pin: `starts_one_ends(4) = 1800`.  Closed form at `n = 4`:
    `18 · 10^2 = 1800`. -/
theorem starts_one_ends_at_4 :
    clever_082_starts_one_ends.starts_one_ends 4 = RustM.ok 1800 := by
  native_decide

/-! ## Main postcondition (closed form).

Captures the `matches_brute_force` proptest at the `Nat` level: the
function returns `18 · 10^(n.toNat - 2)`.  The proptest only
samples `0 ≤ n ≤ 6` for cheap brute-force enumeration, but the
closed form holds across the entire success domain `2 ≤ n ≤ 20`
(beyond which the result no longer fits in `u64`). -/

/-- Postcondition (closed form): for `2 ≤ n.toNat ≤ 20`, the
    function succeeds and returns `18 · 10^(n.toNat - 2)`.  Combined
    with the two base-case unit pins (`_at_0`, `_at_1`), this pins
    down the exact mathematical value on the entire success domain. -/
theorem starts_one_ends_closed_form (n : u64)
    (hlo : 2 ≤ n.toNat) (hhi : n.toNat ≤ 20) :
    clever_082_starts_one_ends.starts_one_ends n
      = RustM.ok (UInt64.ofNat (18 * 10 ^ (n.toNat - 2))) := by
  sorry

/-! ## Failure condition (integer overflow).

For `n ≥ 21` the closed-form value `18 · 10^(n-2)` exceeds
`u64::MAX`, so the function panics with `Error.integerOverflow`.
This pins down the precondition `n ≤ 20`.  The proptest does not
explicitly assert the failure mode (it's outside its sampled
range), but the contract clearly delineates it — the function
*must* return some `RustM` value, and outside the success domain
that value can only be `.fail .integerOverflow` (the only failure
mode any `*?` site can produce). -/

/-- Failure: for every `n ≥ 21`, `starts_one_ends n` panics with
    integer overflow.  The boundary value `n = 21` overflows in the
    outer `18 *? 10^19`; larger `n` overflow earlier in the
    `pow10_at` walk. -/
theorem starts_one_ends_overflow (n : u64) (h : 21 ≤ n.toNat) :
    clever_082_starts_one_ends.starts_one_ends n
      = RustM.fail .integerOverflow := by
  sorry

end Clever_082_starts_one_endsObligations
