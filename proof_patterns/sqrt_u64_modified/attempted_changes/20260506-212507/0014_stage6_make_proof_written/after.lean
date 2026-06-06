-- Companion obligations file for the `sqrt_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs are filled in here; the three obligations below remain as `sorry` for
-- the reasons documented in their docstrings.

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

/-- Postcondition (lower bound): the result `r` of `sqrt x` satisfies `r² ≤ x`.

    Stated at the `Nat` level (`r.toNat * r.toNat ≤ x.toNat`) so the square is
    taken in unbounded arithmetic and never wraps. For the correct sqrt value
    `r ≤ ⌊√(2⁶⁴−1)⌋ = 2³² − 1`, so `r * r` would in fact fit in `u64`, but
    the `Nat` form is the cleanest way to state the bound without coupling
    the specification to that totality side condition.

    This is the "lower bound is a square root from below" half of the
    contract — captured by the Rust property test `prop_sqrt_lower_bound`,
    by `sqrt_test`'s `rt_sq <= i` assertion, and (vacuously) by the
    `sqrt_small`/`sqrt_doctest` spot-checks.

    **Proof status: open (`sorry`).**

    The Rust source uses `while`-loops in two places that are extracted to
    `rust_primitives.hax.while_loop`:

      * the `log2` helper (a shift-and-count loop), and
      * the second-phase Babylonian descent loop in `sqrt`.

    Closing this theorem requires manually applying
    `Spec.MonoLoopCombinator.while_loop` (cf. the skill's "Manual loop-spec
    application" section) with a non-trivial invariant.  For the lower bound
    the invariant the Babylonian iteration preserves is essentially

        x ≥ ⌊√a⌋   ∧   xn = ⌊(a/x + x)/2⌋

    together with the AM-GM consequence `(a/x + x)/2 ≥ ⌊√a⌋`.  Establishing
    this in Lean against `UInt64` (i.e. lifting all the divisions and shifts
    to `Nat` and discharging the no-overflow side conditions for `a/x + x`,
    `1 <<< ((log2 a + 1)/2)`, the `>>>? (1 : i32)` shifts, and the
    `_ +? (1 : u32)` increment in `log2`) is a substantial, multi-stage
    proof.  None of the five reference closed-proof obligations files
    referenced for this target use `while_loop` at all (the selector flagged
    this as a gap), so there is no transferable proof skeleton to copy.

    A sketch of the missing argument:
      1. Prove a `log2_spec` Hoare triple: `⦃True⦄ log2 a ⦃⇓ r => r.toNat = ⌊log₂ a⌋⌋` for `a ≥ 1`.
         Requires applying `while_loop.spec` with the invariant
         `v.toNat * 2^result.toNat = a.toNat` (and `v ≥ 1`) and showing the
         body's `result + 1` doesn't overflow because `result ≤ 63`.
      2. Lift the initial guess `g = 1 <<< ((log2 a + 1) / 2)` to its `Nat`
         value `2^⌈log₂ a / 2⌉`, prove `g.toNat ≥ ⌊√a.toNat⌋ / 2` (so the
         first Newton step lands above `⌊√a⌋`).
      3. Apply `while_loop.spec` to the second-phase loop with the invariant
         `x.toNat ≥ ⌊√a.toNat⌋ ∧ xn.toNat = (a.toNat / x.toNat + x.toNat) / 2`
         and prove preservation: a single Newton step from `x ≥ ⌊√a⌋` keeps
         `xn ≥ ⌊√a⌋`, and termination measure `x.toNat` strictly decreases
         in the body.
      4. On loop exit (`¬ x > xn`), conclude `x.toNat = ⌊√a.toNat⌋` and
         from there `x.toNat * x.toNat ≤ a.toNat`. -/
theorem sqrt_lower_bound (x : u64) :
    ⦃ ⌜ True ⌝ ⦄
      sqrt_u64.sqrt x
    ⦃ ⇓ r => ⌜ r.toNat * r.toNat ≤ x.toNat ⌝ ⦄ := by
  sorry

/-- Postcondition (upper bound): the result `r` of `sqrt x` satisfies
    `x < (r + 1)²`. Stated at the `Nat` level so `(r + 1) * (r + 1)` is
    taken in unbounded arithmetic and the bound holds *unconditionally*
    — there is no overflow caveat at the `Nat` level (the Rust property
    test guards `(r+1)²` with `checked_mul` only because it executes in
    `u64`; mathematically the inequality holds whether or not the
    machine-arithmetic square fits).

    This is the "upper bound forces `r` to be the *greatest* such root"
    half of the contract — captured by the Rust property test
    `prop_sqrt_upper_bound` and by `sqrt_test`'s `i < x` assertion. It is
    independent from `sqrt_lower_bound`: returning `0` satisfies the lower
    bound but fails this one for any positive `x`.

    **Proof status: open (`sorry`).**

    Same technical obstacle as `sqrt_lower_bound`: the proof requires a
    manual `while_loop.spec` application with the dual invariant for the
    Babylonian iteration.  Concretely, the upper-bound side of the Newton
    fixed point: once the loop exits with `x ≤ xn`, AM-GM forces
    `x.toNat = ⌊√a.toNat⌋` (so in particular `(x.toNat + 1)² > a.toNat`).
    The same `log2`-spec dependency, the same shift/division non-failure
    side conditions, and the same lack of a transferable example apply.
    See `sqrt_lower_bound` above for the full sketch. -/
theorem sqrt_upper_bound (x : u64) :
    ⦃ ⌜ True ⌝ ⦄
      sqrt_u64.sqrt x
    ⦃ ⇓ r => ⌜ x.toNat < (r.toNat + 1) * (r.toNat + 1) ⌝ ⦄ := by
  sorry

/-- Totality / no-panic: for every `u64` input, `sqrt` returns a value
    (it never fails). The Rust source documents the failure surface
    explicitly as empty ("Failures: none — the function never panics"),
    and the `prop_sqrt_*` proptests would themselves panic on any failed
    call before reaching the postcondition assertion, so this is its own
    contract clause.

    **Proof status: open (`sorry`).**

    This is the most tractable of the three theorems but still requires
    `while_loop.spec` reasoning.  Specifically, even just to prove
    `∃ v, sqrt x = RustM.ok v` we must rule out the four `RustM`
    failure modes that could arise inside `sqrt`'s body:

      * `>>>? (1 : i32)` failing because `1 < 0 ∨ 1 ≥ 64` — discharged by `decide`.
      * `<<<? ((log2 a + 1) / 2)` failing because the shift amount is `≥ 64`.
        Requires the bound `log2 a ≤ 63` for `a < 2⁶⁴`, which is itself a
        consequence of a `log2_spec` Hoare triple over the inner while-loop.
      * `(log2 a) +? (1 : u32)` overflowing — discharged by the same bound `log2 a ≤ 63`.
      * `a /? x` dividing by zero — requires the loop invariant `x ≥ 1`.
      * `(a /? x) +? x` overflowing — requires the loop invariant
        `x ≤ 2³²` (since `⌊√a⌋ ≤ 2³² − 1` and the Newton step keeps `x` above
        `⌊√a⌋`), so `a/x + x ≤ a/x + 2³² ≤ 2³² + 2³² < 2⁶⁴`.

    Discharging the last three requires the same loop-invariant
    infrastructure as the lower/upper-bound theorems above. -/
theorem sqrt_no_failure (x : u64) :
    ∃ v : u64, sqrt_u64.sqrt x = RustM.ok v := by
  sorry

end Sqrt_u64Obligations
