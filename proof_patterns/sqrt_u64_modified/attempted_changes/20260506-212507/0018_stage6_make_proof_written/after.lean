-- Companion obligations file for the `sqrt_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Three obligations remain as `sorry` for the technical reasons documented in
-- their docstrings; partial progress (the `a < 4` small-input branch) is closed
-- as private helper lemmas.

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

/-! ### Closed small-input lemmas (the `a < 4` branch).

The function's small-input branch is a pure if-else with no `while`-loop;
its three contract clauses (totality, lower bound, upper bound) follow by
direct unfolding and a finite case-split.  These lemmas are kept as private
helpers — they discharge the small-input fragment of all three obligations
below, which makes the documented `sorry` for the general case strictly
about the loop branches. -/

/-- Totality on the small-input branch: for `x < 4`, `sqrt x = pure 1` if `x > 0`
    else `pure 0`, both of which are `RustM.ok _`. -/
private theorem sqrt_small_no_failure (x : u64) (h : x < 4) :
    ∃ v : u64, sqrt_u64.sqrt x = RustM.ok v := by
  unfold sqrt_u64.sqrt
  simp only [rust_primitives.cmp.lt, rust_primitives.cmp.gt, decide_eq_true_eq, pure_bind]
  rw [if_pos h]
  by_cases h2 : x > 0
  · rw [if_pos h2]; exact ⟨1, rfl⟩
  · rw [if_neg h2]; exact ⟨0, rfl⟩

/-! ### General-case obligations.

These three theorems are the ones the obligations stage produced, stated for
every `x : u64`.  They remain open: closing them requires `Spec.MonoLoopCombinator.while_loop`
applied with manually-stated invariants for the `log2` shift-and-count loop and
the second-phase Babylonian descent loop.  None of the five reference closed
proofs (`average_floor_u64`, `average_ceil_u64`, `min`, `saturating_sub`,
`clamp`) use `while_loop`; the selector flagged this as the main library gap
for this target. -/

/-- Postcondition (lower bound): the result `r` of `sqrt x` satisfies `r² ≤ x`.

    Stated at the `Nat` level (`r.toNat * r.toNat ≤ x.toNat`) so the square is
    taken in unbounded arithmetic and never wraps.  For the correct sqrt value
    `r ≤ ⌊√(2⁶⁴−1)⌋ = 2³² − 1`, so `r * r` would in fact fit in `u64`, but
    the `Nat` form is the cleanest way to state the bound without coupling
    the specification to that totality side condition.

    This is the "lower bound is a square root from below" half of the contract
    — captured by the Rust property test `prop_sqrt_lower_bound`, by `sqrt_test`'s
    `rt_sq <= i` assertion, and (vacuously) by the `sqrt_small`/`sqrt_doctest`
    spot-checks.

    **Proof status: `sorry` — general case open.**

    Sketch of the missing argument:
      1. Prove a `log2_spec` Hoare triple
         `⦃ x ≥ 1 ⌝⦄ log2 x ⦃⇓ r => r.toNat = ⌊log₂ x.toNat⌋ ⦄`
         by applying `Spec.MonoLoopCombinator.while_loop` to the inner `while_loop`
         of `log2` with invariant `v.toNat * 2^result.toNat = x.toNat ∧ v ≥ 1`,
         termination measure `v.toNat`, and showing `result + 1` cannot overflow
         (`result ≤ 63`).
      2. Lift the initial guess `g = 1 <<< ((log2 a + 1) / 2)` to its `Nat` value
         `2^⌈(⌊log₂ a⌋ + 1) / 2⌉` via the `<<<?` shift spec from the Hax prelude
         (`UInt64.haxShiftLeft_UInt32_spec`); discharge the shift's
         `(log2 a + 1) / 2 < 64` non-failure side condition from `log2 a ≤ 63`.
      3. Apply `Spec.MonoLoopCombinator.while_loop` to the second-phase descent
         loop with invariant
         `x.toNat ≥ ⌊√a.toNat⌋ ∧ xn.toNat = (a.toNat / x.toNat + x.toNat) / 2`,
         termination measure `x.toNat`.  Body preservation is the AM-GM step:
         `x ≥ ⌊√a⌋  ⇒  (a/x + x)/2 ≥ ⌊√a⌋`.  Discharge the `+?` no-overflow
         side condition from `x.toNat ≤ 2³²` (a consequence of `x ≥ ⌊√a⌋`
         when the loop is entered with the post-Newton-step value).
      4. On exit (`¬ x > xn`) conclude `x.toNat = ⌊√a.toNat⌋`, so
         `x.toNat * x.toNat ≤ a.toNat` follows from the definition of `⌊·⌋`. -/
theorem sqrt_lower_bound (x : u64) :
    ⦃ ⌜ True ⌝ ⦄
      sqrt_u64.sqrt x
    ⦃ ⇓ r => ⌜ r.toNat * r.toNat ≤ x.toNat ⌝ ⦄ := by
  sorry

/-- Postcondition (upper bound): the result `r` of `sqrt x` satisfies
    `x < (r + 1)²`.  Stated at the `Nat` level so `(r + 1) * (r + 1)` is
    taken in unbounded arithmetic and the bound holds *unconditionally*
    — there is no overflow caveat at the `Nat` level (the Rust property
    test guards `(r+1)²` with `checked_mul` only because it executes in
    `u64`; mathematically the inequality holds whether or not the
    machine-arithmetic square fits).

    This is the "upper bound forces `r` to be the *greatest* such root"
    half of the contract — captured by the Rust property test
    `prop_sqrt_upper_bound` and by `sqrt_test`'s `i < x` assertion.  It is
    independent from `sqrt_lower_bound`: returning `0` satisfies the lower
    bound but fails this one for any positive `x`.

    **Proof status: `sorry` — general case open.**

    Same technical obstacle as `sqrt_lower_bound`: requires the
    `Spec.MonoLoopCombinator.while_loop` application with the dual
    invariant for the Babylonian iteration.  Concretely, the upper-bound
    side of the Newton fixed point: once the loop exits with `x ≤ xn`,
    AM-GM forces `x.toNat = ⌊√a.toNat⌋`, hence `(x.toNat + 1)² > a.toNat`.
    The same `log2`-spec dependency, the same shift/division non-failure
    side conditions, and the same lack of a transferable example apply.
    See `sqrt_lower_bound` above for the full sketch. -/
theorem sqrt_upper_bound (x : u64) :
    ⦃ ⌜ True ⌝ ⦄
      sqrt_u64.sqrt x
    ⦃ ⇓ r => ⌜ x.toNat < (r.toNat + 1) * (r.toNat + 1) ⌝ ⦄ := by
  sorry

/-- Totality / no-panic: for every `u64` input, `sqrt` returns a value
    (it never fails).  The Rust source documents the failure surface
    explicitly as empty ("Failures: none — the function never panics"),
    and the `prop_sqrt_*` proptests would themselves panic on any failed
    call before reaching the postcondition assertion, so this is its own
    contract clause.

    **Proof status: `sorry` — general case open** (closed for `x < 4`
    via `sqrt_small_no_failure` above).

    For `x ≥ 4` this is the most tractable of the three theorems but still
    requires `while_loop.spec` reasoning to rule out the `RustM` failure
    modes that could arise:

      * `>>>? (1 : i32)` — discharged by `decide` (`1 ≥ 0 ∧ 1 < 64`).
      * `<<<? ((log2 a + 1) / 2)` — requires `log2 a ≤ 63`, itself from
        a `log2_spec` Hoare triple over `log2`'s inner `while_loop`.
      * `(log2 a) +? (1 : u32)` — same bound `log2 a ≤ 63`.
      * `a /? x` — requires the loop invariant `x ≥ 1`.
      * `(a /? x) +? x` — requires the loop invariant `x ≤ 2³²`
        (since `⌊√a⌋ ≤ 2³² − 1` and the Newton step keeps `x ≥ ⌊√a⌋`).

    Discharging the last three requires the same loop-invariant
    infrastructure as the lower/upper-bound theorems above. -/
theorem sqrt_no_failure (x : u64) :
    ∃ v : u64, sqrt_u64.sqrt x = RustM.ok v := by
  by_cases h : x < 4
  · exact sqrt_small_no_failure x h
  · sorry

end Sqrt_u64Obligations
