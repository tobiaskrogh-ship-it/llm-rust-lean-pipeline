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
  mvcgen [cbrt_u64.cbrt, cbrt_u64.cbrt_u32, cbrt_u64.fixpoint_cbrt,
          cbrt_u64.bit_length_u64]
  all_goals try grind
  all_goals sorry

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
  sorry

end Cbrt_u64Obligations
