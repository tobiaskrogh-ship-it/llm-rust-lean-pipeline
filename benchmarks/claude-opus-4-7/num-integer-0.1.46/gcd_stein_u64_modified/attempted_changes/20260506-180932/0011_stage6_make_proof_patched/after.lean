-- Companion obligations file for the `gcd_stein_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import gcd_stein_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Gcd_stein_u64Obligations

/-- Known value (from `tests::known_values`): `gcd_stein(10, 2) = 2`. -/
theorem gcd_10_2 :
    gcd_stein_u64.gcd_stein (10 : u64) (2 : u64) = RustM.ok (2 : u64) := by
  native_decide

/-- Known value (from `tests::known_values`): `gcd_stein(10, 3) = 1`. -/
theorem gcd_10_3 :
    gcd_stein_u64.gcd_stein (10 : u64) (3 : u64) = RustM.ok (1 : u64) := by
  native_decide

/-- Known value (from `tests::known_values`): `gcd_stein(0, 3) = 3`. The
    zero-shortcut returns `m | n = 0 | 3 = 3`. -/
theorem gcd_0_3 :
    gcd_stein_u64.gcd_stein (0 : u64) (3 : u64) = RustM.ok (3 : u64) := by
  -- Zero-input shortcut: the `if (m == 0 || n == 0)` branch fires and the
  -- function returns `m ||| n = 0 ||| 3 = 3` without entering any loop.
  unfold gcd_stein_u64.gcd_stein
  rfl

/-- Known value (from `tests::known_values`): `gcd_stein(3, 3) = 3`. -/
theorem gcd_3_3 :
    gcd_stein_u64.gcd_stein (3 : u64) (3 : u64) = RustM.ok (3 : u64) := by
  native_decide

/-- Known value (from `tests::known_values`): `gcd_stein(56, 42) = 14`. -/
theorem gcd_56_42 :
    gcd_stein_u64.gcd_stein (56 : u64) (42 : u64) = RustM.ok (14 : u64) := by
  native_decide

/-- Boundary (from `tests::zero_zero_is_zero`): `gcd_stein(0, 0) = 0` by
    convention — the zero-shortcut returns `m | n = 0 | 0 = 0`. -/
theorem gcd_zero_zero :
    gcd_stein_u64.gcd_stein (0 : u64) (0 : u64) = RustM.ok (0 : u64) := by
  -- Zero-input shortcut: same as `gcd_0_3`, the early `if` returns
  -- `0 ||| 0 = 0` without entering any loop.
  unfold gcd_stein_u64.gcd_stein
  rfl

/-- Postcondition (from `tests::result_divides_both_inputs`): the result
    `r` divides `a`. The Rust test splits on `r = 0` (forcing `a = b = 0`)
    versus `r ≠ 0` (asserting `a % r = 0`); both halves collapse to the
    single Nat-level statement `a.toNat % r.toNat = 0` because `Nat.mod`
    of `0` returns its left argument, so `a.toNat % 0 = 0 ↔ a = 0`. -/
theorem result_divides_a (a b : u64) :
    ⦃ ⌜ True ⌝ ⦄ gcd_stein_u64.gcd_stein a b
    ⦃ ⇓ r => ⌜ a.toNat % r.toNat = 0 ⌝ ⦄ := by
  -- Closing this requires injecting the gcd-preserving invariant
  --   `Nat.gcd m.toNat n.toNat = Nat.gcd (a.toNat / 2^k) (b.toNat / 2^k)`
  -- (or an equivalent characterisation in terms of the common factor of 2)
  -- through five extracted `while_loop`s. Each loop has the auto-derived
  -- invariant `True` baked in by Hax, and a stronger invariant must be
  -- threaded by manual application of `Spec.MonoLoopCombinator.while_loop`
  -- to each of the five loops, with body-preservation lemmas for trailing-
  -- zero stripping and subtract-then-strip. The library has no precedent
  -- for this for an extracted `rust_primitives.hax.while_loop`; see the
  -- analogous `sorry` in `gcd_while_modified` (Gcd_whileObligations.lean,
  -- `gcd_while_divides_a`) where the same obstruction blocks the simpler
  -- single-loop Euclidean version.
  sorry

/-- Postcondition (from `tests::result_divides_both_inputs`): the result
    `r` divides `b`. Independent of `result_divides_a`; bundled in the
    Rust test only for loop economy. -/
theorem result_divides_b (a b : u64) :
    ⦃ ⌜ True ⌝ ⦄ gcd_stein_u64.gcd_stein a b
    ⦃ ⇓ r => ⌜ b.toNat % r.toNat = 0 ⌝ ⦄ := by
  -- Same technical obstruction as `result_divides_a`: the gcd-preserving
  -- invariant must be injected into each of the five extracted loops.
  -- Library has no precedent for this for `rust_primitives.hax.while_loop`.
  sorry

/-- Postcondition (from `tests::result_is_greatest`): for any non-zero
    common divisor `d` of two non-zero inputs `a` and `b`, the result `r`
    is at least `d`. The Rust test sweeps `d` through `(g + 1) ..= max(a, b)`
    and asserts `d` does not divide both — the contrapositive of the
    statement here. -/
theorem result_is_greatest (a b d : u64)
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    (hda : a.toNat % d.toNat = 0) (hdb : b.toNat % d.toNat = 0) :
    ⦃ ⌜ True ⌝ ⦄ gcd_stein_u64.gcd_stein a b
    ⦃ ⇓ r => ⌜ d.toNat ≤ r.toNat ⌝ ⦄ := by
  -- "Greatest" follows from the gcd-preserving invariant (any divisor of
  -- both inputs divides every later state, hence divides the final result,
  -- hence is bounded by it when nonzero). Same precedent obstruction as
  -- `result_divides_a` / `gcd_while_greatest`: needs custom-invariant
  -- injection across five extracted `while_loop`s. Left as `sorry`.
  sorry

/-- Totality / no-panic: for every `(a, b) : u64 × u64` the function
    returns a value (it never panics). The Rust source documents this as
    an explicit contract clause: bitwise OR is panic-free (chosen as the
    decreasing measure precisely because `m + n` could overflow), the
    subtractions are guarded by `m > n` / `m < n`, and the final
    `m << shift` is safe because `shift < 64` (it counts trailing zeros
    of the non-zero `m | n`). The known-value and divisibility tests all
    rely on this implicitly by calling the function and asserting on the
    returned value. -/
theorem gcd_no_panic (a b : u64) :
    ∃ v : u64, gcd_stein_u64.gcd_stein a b = RustM.ok v := by
  -- Excluding both panic (`.fail`) and divergence (`.div`) for the five
  -- extracted `while_loop`s composed sequentially requires (i) showing
  -- each loop's body cannot panic given its loop invariant and (ii)
  -- showing the termination measure decreases. Per the Hax `while_loop`
  -- spec lemma, this is in principle reducible to five
  -- `Spec.MonoLoopCombinator.while_loop` applications, but with a Hoare
  -- triple the post-condition is satisfied vacuously by `.fail` — see the
  -- comment in `gcd_while_modified` (`gcd_while_total`) for the same
  -- obstruction at much smaller scale. Library has no precedent for
  -- pinning `∃ r, _ = .ok r` for an extracted `rust_primitives.hax.while_loop`.
  sorry

end Gcd_stein_u64Obligations
