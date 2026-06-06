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

/-- Failure condition for `nth_root`: when `n == 0`, the function panics.

The Rust source documents this in its `# Panics` section ("Panics if `n == 0`"),
and the `zeroth_root` test exercises it. The implementation triggers the panic
via `1u64 / (n as u64)`, which on `n == 0` extracts to a `RustM` failure with
`Error.divisionByZero` (the `if y = 0 then .fail .divisionByZero` branch of the
`UInt64` division instance). -/
theorem nth_root_zero_panic (self_val : u64) :
    nth_root_u64.nth_root self_val 0 = RustM.fail .divisionByZero := by
  unfold nth_root_u64.nth_root
  rfl

/-- (LB) for `sqrt_u64`: `result² ≤ a`.

The truncated principal square root is by definition the largest `r` with
`r² ≤ a`. Captures the `prop_sqrt_lower_bound` property test (and the
positive-input branch of the generic `check` used in the `sqrt` test). The
`Nat`-level inequality automatically subsumes the proptest's "no overflow
of `r²`" check, since `r.toNat ^ 2 ≤ a.toNat < 2^64`.

NOTE (left as `sorry`): the proof requires inventing a loop invariant for
the descending Newton sweep `while x > xn { x := xn; xn := (a/x + x) >>> 1 }`,
manually applying `Spec.MonoLoopCombinator.while_loop` (the source-level
`loop_decreases!` only feeds Hax's termination check, not a Lean
invariant), and discharging the integer-Newton convergence argument
"`x ≤ (a/x + x)/2 ⇒ x² ≤ a`". None of the closed-proof reference examples
covers a `while_loop` extraction with a non-trivial postcondition; the
selector explicitly flagged this as an uncovered gap in the example
library. The branches `a == 0` (returns 0) and `1 ≤ a < 4` (returns 1)
discharge cleanly, but the full proof needs the loop-invariant machinery
described in the manual loop-spec section of the proof skill. -/
theorem sqrt_lower_bound (a : u64) :
    ⦃ ⌜ True ⌝ ⦄
    nth_root_u64.sqrt_u64 a
    ⦃ ⇓ r => ⌜ r.toNat ^ 2 ≤ a.toNat ⌝ ⦄ := by
  sorry

/-- (UB) for `sqrt_u64`: `(result + 1)² > a` whenever `(r + 1)²` is
representable in `u64` (vacuous otherwise).

Captures the `prop_sqrt_upper_bound` property test. Together with the lower
bound, this pins down the truncated principal square root uniquely.

NOTE (left as `sorry`): proving the upper bound on the loop's exit value is
the deeper of the two Newton-iteration arguments. It requires that the
initial guess `x₀ := 1u64 << (log2(a)/2 + 1)` strictly exceeds `√a`, that
each Newton step `x ↦ (a/x + x)/2` is monotone non-increasing while
`x > √a`, and that termination at `x ≤ xn` implies `(x+1)² > a`. The
last claim — Newton's monovariant — is uncovered by the example library
(no closed proof traverses a `while_loop`), so the proof would have to
build the descending-fixpoint invariant from scratch and apply
`Spec.MonoLoopCombinator.while_loop` manually. -/
theorem sqrt_upper_bound (a : u64) :
    ⦃ ⌜ True ⌝ ⦄
    nth_root_u64.sqrt_u64 a
    ⦃ ⇓ r => ⌜ (r.toNat + 1) ^ 2 < 2 ^ 64 → a.toNat < (r.toNat + 1) ^ 2 ⌝ ⦄ := by
  sorry

/-- (LB) for `cbrt_u64`: `result³ ≤ a`.

Captures the `prop_cbrt_lower_bound` property test (and the positive-input
branch of the generic `check` used in the `cbrt` test).

NOTE (left as `sorry`): same structural reason as `sqrt_lower_bound`,
plus an extra delegation: for `a ≤ u32::MAX` the body forwards to
`cbrt_u32`, which itself uses a Hacker's-Delight bit-trick `while`-loop
with a per-step branch. Proving `cbrt_u32`'s correctness pre-states the
loop invariant `0 ≤ y ∧ y² = y2 ∧ y³ ≤ a - x_residual_with_shifts`, which
again requires the manual `Spec.MonoLoopCombinator.while_loop` machinery
not exercised in any reference example. The `a > u32::MAX` branch then
runs the same descending Newton sweep as `sqrt_u64`, with the same
loop-invariant gap. -/
theorem cbrt_lower_bound (a : u64) :
    ⦃ ⌜ True ⌝ ⦄
    nth_root_u64.cbrt_u64 a
    ⦃ ⇓ r => ⌜ r.toNat ^ 3 ≤ a.toNat ⌝ ⦄ := by
  sorry

/-- (UB) for `cbrt_u64`: `(result + 1)³ > a` whenever `(r + 1)³` is
representable in `u64` (vacuous otherwise).

Captures the `prop_cbrt_upper_bound` property test. Together with the lower
bound, this pins down the truncated principal cube root uniquely.

NOTE (left as `sorry`): combines the cbrt-via-cbrt_u32 delegation
challenge of `cbrt_lower_bound` with the Newton-monovariant argument of
`sqrt_upper_bound`. No reference example covers either piece; the proof
needs the same manual loop-invariant machinery applied twice (once to
the `cbrt_u32` Hacker's-Delight loop, once to the descending Newton
sweep). -/
theorem cbrt_upper_bound (a : u64) :
    ⦃ ⌜ True ⌝ ⦄
    nth_root_u64.cbrt_u64 a
    ⦃ ⇓ r => ⌜ (r.toNat + 1) ^ 3 < 2 ^ 64 → a.toNat < (r.toNat + 1) ^ 3 ⌝ ⦄ := by
  sorry

/-- (LB) for `nth_root`: `result^n ≤ a` for any valid `n ≥ 1`.

Captures the `prop_nth_root_lower_bound` property test (which exercises
`n ∈ 1..=128`) and the generic `check` used in `nth_root_test` and `bit_size`.
The precondition `n ≥ 1` is mandatory: `n == 0` is the panic case, separately
covered by `nth_root_zero_panic`. The `Nat`-level inequality subsumes the
proptest's "no overflow of `r^n`" requirement, since
`r.toNat ^ n.toNat ≤ a.toNat < 2^64`. -/
theorem nth_root_lower_bound (a : u64) (n : u32) :
    ⦃ ⌜ 1 ≤ n.toNat ⌝ ⦄
    nth_root_u64.nth_root a n
    ⦃ ⇓ r => ⌜ r.toNat ^ n.toNat ≤ a.toNat ⌝ ⦄ := by
  sorry

/-- (UB) for `nth_root`: `(result + 1)^n > a` whenever `(r + 1)^n` is
representable in `u64` (vacuous otherwise).

Captures the `prop_nth_root_upper_bound` property test. Together with the
lower bound and `n ≥ 1`, this pins down the truncated principal `n`-th root
uniquely. -/
theorem nth_root_upper_bound (a : u64) (n : u32) :
    ⦃ ⌜ 1 ≤ n.toNat ⌝ ⦄
    nth_root_u64.nth_root a n
    ⦃ ⇓ r =>
        ⌜ (r.toNat + 1) ^ n.toNat < 2 ^ 64 →
            a.toNat < (r.toNat + 1) ^ n.toNat ⌝ ⦄ := by
  sorry

end Nth_root_u64Obligations
