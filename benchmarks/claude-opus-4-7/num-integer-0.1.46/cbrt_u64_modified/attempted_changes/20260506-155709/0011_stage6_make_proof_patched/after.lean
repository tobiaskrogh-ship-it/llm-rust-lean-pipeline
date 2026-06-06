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

/-- Totality / no failure: `cbrt` is total --- it accepts every `u64`
    and never panics. The Rust source documents this explicitly:
    "the function is total --- it never panics and has no error-return
    channel". This is an independent contract clause from (P1)/(P2):
    a Hoare triple `⦃ ⌜True⌝ ⦄ f ⦃ ⇓ r => Q r ⦄` only constrains
    successful returns and would be vacuously satisfied by an
    implementation that always failed, so we state the totality
    requirement separately as an existential equality with `RustM.ok`.
    Mirrors the `average_floor_total` / `average_ceil_no_failure`
    obligations in the reference examples.

    **Proof status: left as `sorry`.**

    *Technical reason.* Closing this obligation requires showing that
    none of the checked operations (`+?`, `-?`, `*?`, `/?`, `<<<?`,
    `>>>?`) in any of the four functions `cbrt_u32`, `bit_length_u64`,
    `fixpoint_cbrt`, or `cbrt` ever fail. The hard cases are the three
    `rust_primitives.hax.while_loop` bodies, each of which carries
    tuple state (`Tuple4 u32 u32 u32 u32`, `Tuple2 u64 u64`,
    `Tuple2 u32 u64`) and contains multiple checked operations whose
    no-overflow argument is non-trivial:
      * In `cbrt_u32`: `y *? 2`, `y2 *? 4`, `3 *? (y2 +? y)`,
        `b <<< s`, and `x -? (b <<< s)` are all guarded by the
        algorithmic invariant `y² ≤ x_input / 4^s_iter` of
        Hacker's-Delight `icbrt2`. This invariant is the entire
        correctness proof of the algorithm and pre-dates this work.
      * In `fixpoint_cbrt`: `x *? x` and `a /? (x*x)` require the
        invariant `x ≤ guess ∧ guess² < 2^64` together with a Newton's
        method monotonicity argument.
      * In `bit_length_u64`: `bits +? 1` requires the invariant
        `bits ≤ 64`, which itself follows from `tmp` being a `u64`
        value that halves each iteration.
    Each of these requires applying `Spec.MonoLoopCombinator.while_loop`
    manually with a hand-stated invariant (the source-level
    `loop_invariant!` is missing, since the Rust function has no
    `hax_lib` invariant annotation), and then discharging step
    obligations with bitvector / Nat reasoning specific to each loop.
    The combined effort is multi-hundred-line and the Hacker's-Delight
    invariant for `cbrt_u32` is, on its own, a documented research
    result (Warren, "Hacker's Delight" §11.1).

    None of the reference examples (`sum_to_n`, `factorial`,
    `average_floor`, `average_ceil`, `clamp`) attack a `while_loop`
    with tuple state plus checked arithmetic of this depth, so there
    is no template proof to lift. -/
theorem cbrt_total (x : u64) :
    ∃ r : u64, cbrt_u64.cbrt x = RustM.ok r := by
  sorry

/-- Postcondition (P1): `cbrt x` is a cube-root candidate.

    For every `x : u64`, the returned value `r` satisfies
    `r^3 ≤ x`. The cubing is taken at the `Nat` level since
    `r ≤ floor(cbrt(2^64 - 1)) = 2_642_245`, hence `r^3 < 2^64`
    fits, so this is the same statement as the Rust property test
    `prop_cube_le_x` (which uses `r.checked_pow(3)`).

    Without (P1), `cbrt` could legally return any value at all;
    (P1) is what makes "cube root" meaningful. -/
theorem cbrt_cube_le_x (x : u64) :
    ⦃ ⌜ True ⌝ ⦄
    cbrt_u64.cbrt x
    ⦃ ⇓ r => ⌜ r.toNat * r.toNat * r.toNat ≤ x.toNat ⌝ ⦄ := by
  -- **Proof status: left as `sorry`.**
  --
  -- *Technical reason.* This Hoare triple cannot be discharged by
  -- `mvcgen` + `grind` because the postcondition `r³ ≤ x` requires
  -- two non-trivial loop invariants:
  --
  --   1. For `cbrt_u32` (Hacker's-Delight `icbrt2`): at iteration
  --      `s_iter`, the carried state `(x_remaining, y, y2)` satisfies
  --      `y² = y2`, and `y * 2^s_iter` together with `x_remaining`
  --      and `s_iter * 3` reconstructs the original `a`. After the
  --      loop terminates (`s_iter = 0`), `y³ ≤ a` follows from the
  --      construction of the algorithm. This is a classical proof
  --      (Warren, *Hacker's Delight*, §11.1) and not closable by
  --      automation alone.
  --
  --   2. For `fixpoint_cbrt` (Newton's method on `f(x) = x - (x³-a)/(3x²)`):
  --      starting from `guess ≥ ∛a`, every iterate `x_n` satisfies
  --      `x_n³ ≥ a`, and the sequence is monotonically non-increasing
  --      until it stabilises at `⌊∛a⌋`. The exit condition `x ≤ xn`
  --      then forces `x³ ≤ a`. This is a standard analysis-of-Newton's
  --      method argument transposed to integer arithmetic.
  --
  -- Discharging either invariant requires manually applying
  -- `Spec.MonoLoopCombinator.while_loop` with a hand-stated invariant
  -- (the Rust source has no `loop_invariant!` annotation), and the
  -- step obligations for each pull in cubic-monotonicity Nat lemmas
  -- (`Nat.pow_le_pow_left` / `Nat.mul_le_mul`) that have to be
  -- chained through tuple-state bookkeeping. None of the reference
  -- examples include a tuple-state `while_loop` with a postcondition
  -- this deep, so there is no template to lift.
  sorry

/-- Postcondition (P2): `cbrt x` is the *greatest* cube-root candidate.

    For every `x : u64`, the returned value `r` satisfies
    `x < (r + 1)^3` whenever `(r + 1)^3` fits in `u64`; if it does
    not, the bound is vacuous (because `x < 2^64 ≤ (r + 1)^3`).

    Mirrors the Rust property test `prop_x_lt_next_cube`, which uses
    `(r + 1).checked_pow(3)` to guard against overflow.

    Without (P2), `cbrt` could legally return `0` on every input
    (it would still satisfy (P1)); (P2) is what pins `r` down to
    the unique floor cube root. -/
theorem cbrt_x_lt_next_cube (x : u64) :
    ⦃ ⌜ True ⌝ ⦄
    cbrt_u64.cbrt x
    ⦃ ⇓ r =>
        ⌜ (r.toNat + 1) * (r.toNat + 1) * (r.toNat + 1) < 2 ^ 64 →
            x.toNat < (r.toNat + 1) * (r.toNat + 1) * (r.toNat + 1) ⌝ ⦄ := by
  -- **Proof status: left as `sorry`.**
  --
  -- *Technical reason.* Same loop-invariant burden as
  -- `cbrt_cube_le_x`, but for the *upper* half of the cube-root
  -- envelope `r³ ≤ x < (r+1)³`. The Hacker's-Delight invariant for
  -- `cbrt_u32` and the Newton-method invariant for `fixpoint_cbrt`
  -- both have an upper-bound companion (the iteration cannot
  -- *under-shoot* `⌊∛a⌋`), but stating and discharging it requires
  -- the same `Spec.MonoLoopCombinator.while_loop` machinery as (P1)
  -- with an additional cubic-monotonicity inequality
  -- `(r+1)³ > x`. The published proofs of `icbrt2` (Warren §11.1)
  -- and Newton's method handle both bounds simultaneously, but in
  -- Lean each direction is a separate proof obligation and the
  -- step-obligation arithmetic is materially different from (P1).
  --
  -- Closing this would require, beyond the (P1) invariants:
  --   * Strict-inequality versions of the loop invariants (e.g.
  --     `(y+1)³ > x_input * 2^…` for `cbrt_u32`).
  --   * A no-overflow argument for `(r.toNat + 1)³` matching the
  --     Rust property test's `checked_pow` guard.
  --   * A separate case-analysis on the `(r+1)³ < 2^64`
  --     hypothesis to keep the implication's premise discharged.
  --
  -- Same intractability rationale as (P1): not closable in a single
  -- session against the current Hax/Lean prelude.
  sorry

end Cbrt_u64Obligations
