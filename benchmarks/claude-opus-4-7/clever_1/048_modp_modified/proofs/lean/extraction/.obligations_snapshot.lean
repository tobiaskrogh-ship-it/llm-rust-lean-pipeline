-- Companion obligations file for the `clever_048_modp` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_048_modp

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_048_modpObligations

/-! ## Contract clauses

The Rust source contains the following contract-style tests in `mod tests`:
  * `small_cases` — four unit pins: `modp(0,5)=1`, `modp(0,1)=0`,
    `modp(3,5)=3`, `modp(10,7)=2`.
  * `matches_oracle` — main postcondition: for `p > 0`, `modp(n, p)` equals
    `2^n mod p` (computed via the `u128` naive oracle, which agrees with
    `Nat`-level `2^n mod p` for any `p` fitting in `u64`).
  * `p_zero_yields_zero` — degenerate convention: `p = 0 → 0`.

Each becomes one independent `theorem`.  Equational form (`f x = RustM.ok …`)
is used everywhere because the function is total in the safe domain.

### Feasibility note on `matches_oracle`

The proptest bounds `p ≤ 2^30`, but the universal Nat statement holds across
the wider range `0 < p ≤ 2^63`.  The accumulator invariant `acc < p` plus
`p ≤ 2^63` gives `acc * 2 < 2^64`, ruling out the only overflow site
(`(acc *? 2) %? p`).  For `p > 2^63` the universal statement is *false*:
e.g. for `p = 2^63 + 1`, after enough steps `acc = 2^63 < p`, and then
`acc * 2 = 2^64` overflows.  So we take the strongest honest precondition
`p.toNat ≤ 2^63`, well beyond the proptest's range.

The `k +? 1` step never overflows: recursion only continues when `k < n ≤
u64::MAX`, so `k + 1 ≤ n ≤ u64::MAX`.  No `n`-side precondition needed. -/

/-- Degenerate boundary: `p = 0 → 0`, regardless of `n`.
    Captures the proptest `p_zero_yields_zero`. -/
theorem modp_p_zero (n : u64) :
    clever_048_modp.modp n 0 = RustM.ok 0 := by
  sorry

/-- Main postcondition (closed form): for `p > 0` in the feasibility
    range `p.toNat ≤ 2^63`, `modp n p = 2^n mod p`.  Captures the
    proptest `matches_oracle` (whose `u128` naive oracle is precisely
    `2^n mod p` at the `Nat` level).  Implies `result < p`. -/
theorem modp_matches_oracle (n p : u64)
    (h_pos : 0 < p.toNat)
    (h_fit : p.toNat ≤ 2 ^ 63) :
    clever_048_modp.modp n p
      = RustM.ok (UInt64.ofNat (2 ^ n.toNat % p.toNat)) := by
  sorry

/-! ## Unit pins from `small_cases` -/

/-- Unit pin: `modp 0 5 = 1`.  Reflects the convention `2^0 = 1`,
    and `1 % 5 = 1`. -/
theorem modp_at_0_5 :
    clever_048_modp.modp 0 5 = RustM.ok 1 := by
  sorry

/-- Unit pin: `modp 0 1 = 0`.  Differentiates the boundary `p = 1`
    (where `1 % 1 = 0`) from the `p > 1` case. -/
theorem modp_at_0_1 :
    clever_048_modp.modp 0 1 = RustM.ok 0 := by
  sorry

/-- Unit pin: `modp 3 5 = 3`.  Sanity-checks the first few iterations:
    `1 → 2 → 4 → (8 mod 5) = 3`. -/
theorem modp_at_3_5 :
    clever_048_modp.modp 3 5 = RustM.ok 3 := by
  sorry

/-- Unit pin: `modp 10 7 = 2`.  `2^10 = 1024 = 7·146 + 2`. -/
theorem modp_at_10_7 :
    clever_048_modp.modp 10 7 = RustM.ok 2 := by
  sorry

end Clever_048_modpObligations
