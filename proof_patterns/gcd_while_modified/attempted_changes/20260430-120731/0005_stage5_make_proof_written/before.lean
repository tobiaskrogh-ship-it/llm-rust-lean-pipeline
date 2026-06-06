-- Companion obligations file for the `gcd_while` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import gcd_while

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Gcd_whileObligations

/-- Totality / no-panic.
    For every pair of `u64` inputs, `gcd_while` returns a value (it never
    panics and never diverges in the `RustM` sense).

    The only Rust operation in the body that could panic is `a % b`,
    which would fail with `divisionByZero` if `b = 0`. The loop guard
    `b !=? 0` excludes that case, so the modulo is always well-defined.
    Termination is witnessed by the `loop_decreases!(b)` measure: after
    one iteration, the new `b` equals `a % b₀ < b₀` whenever `b₀ > 0`.

    ADMITTED. The proof goes through `hax_mvcgen [gcd_while.gcd_while]`
    plus `RustM.Triple_iff_BitVec` to convert a Hoare triple into the
    equational form `gcd_while a b = pure r`. The obstacle is the body's
    decreasing-measure goal: after `mvcgen`, the goal still contains an
    unreduced `wp ⟦...⟧` over `pure { _0 := b, _1 := a %? b }` plus a
    hypothesis `b.toNat ≤ (a % b).toNat`, where `b ≠ 0` is in scope.
    The math is `Nat.mod_lt` after rewriting `(a % b).toNat = a.toNat %
    b.toNat`, but neither `grind` nor `bv_decide` (the closer used by
    every reference example) discharges it: `bv_decide` abstracts the
    `wp` term as opaque, and `grind` cannot bridge between `b.toNat = 0`
    and `b = 0`. No reference example demonstrates a `while_loop` proof
    for `rust_primitives.hax.while_loop`, so the right tactic combination
    is not available from the library. -/
theorem gcd_while_total (a b : u64) :
    ∃ r : u64, gcd_while.gcd_while a b = pure r := by
  sorry

/-- Postcondition (common divisor).
    Whenever `gcd_while a b` returns a value `r`, that value divides both
    inputs (taken as `Nat`s via `.toNat`). At the boundary `a = b = 0`
    the result is `0` and the claim `0 ∣ 0` holds trivially.

    ADMITTED. The Rust source has only `loop_decreases!(b)` and no
    `loop_invariant!()`. Consequently the user-supplied `inv` argument
    in the extracted `rust_primitives.hax.while_loop` reduces — via
    `hax_construct_pure` — to `fun _ => True`, so the strongest
    Hoare-triple postcondition the loop spec lemma yields is `True ∧
    ¬(b !=? 0)`, i.e., the exit value `r` satisfies `b = 0` but nothing
    is known about `a`. This is too weak to prove that `r` divides
    either input. Closing this obligation requires either:

      (a) Adding a `loop_invariant!(|(a, b)| ∀ d, d ∣ a₀ ∧ d ∣ b₀ ↔
          d ∣ a ∧ d ∣ b)` to the Rust source so that the extracted
          `inv` carries the gcd divisor-set invariant.
      (b) Inlining the loop in Lean and applying
          `Spec.MonoLoopCombinator.while_loop` directly with that
          invariant — non-trivial because none of the reference
          examples demonstrate this pattern. -/
theorem gcd_while_divides_both (a b r : u64)
    (h : gcd_while.gcd_while a b = pure r) :
    r.toNat ∣ a.toNat ∧ r.toNat ∣ b.toNat := by
  sorry

/-- Postcondition (greatest, in the divides ordering).
    Any common divisor `d` of the two inputs also divides the returned
    result `r`. This is the strongest form of "greatest common divisor"
    and it is well-defined even at the `(0, 0)` boundary (where `r = 0`
    and `d ∣ 0` holds for every `d`).

    ADMITTED. Same obstacle as `gcd_while_divides_both`: the source
    function lacks the `loop_invariant!()` annotation that would
    propagate the divisor-set invariant from the original inputs to
    the loop's iterating state. -/
theorem gcd_while_greatest (a b r : u64)
    (h : gcd_while.gcd_while a b = pure r)
    (d : u64) (hda : d.toNat ∣ a.toNat) (hdb : d.toNat ∣ b.toNat) :
    d.toNat ∣ r.toNat := by
  sorry

end Gcd_whileObligations
