-- Companion obligations file for the `sqrt_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

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

open rust_primitives.hax (Tuple2)

/-! ## Helper infrastructure

The `sqrt` implementation composes three `while_loop`s:

  1. `log2 a` — a single loop computing `⌊log₂ a⌋`.
  2. Babylonian "descent" loop in `sqrt`: iterates while `x < xn`.
  3. Babylonian "polish" loop in `sqrt`: iterates while `x > xn`.

The canonical proof shape for each (from `while_example/README.md`) is the
two-stage Stage 1 (Hoare-triple) + Stage 2 (`RustM.Triple_iff_BitVec`) pattern.

The dominant blocker for the value/bound obligations below is a closed-form
spec for the *Newton iteration*: a proof that the Babylonian step
`xn := (a/x + x) / 2` is non-increasing once `x ≥ ⌈√a⌉` and converges to
`⌊√a⌋`. Core Lean exposes `Nat.log2` (used by the implementation's helper) but
**not** `Nat.sqrt`; Mathlib's `Nat.sqrt`/`Nat.sqrt_le'`/`Nat.lt_succ_sqrt'`
would close the bound obligations in one line each, but Mathlib is not
imported in this project.

The proof scaffolding below uses an *existential* postcondition
(`sqrt_postcondition` returns a `u64 r` satisfying both bounds) and derives
the specific-value obligations by uniqueness: if `r² ≤ x < (r+1)²` and
`r'² ≤ x < (r'+1)²` then `r = r'`. This avoids defining a custom `natSqrt`
function while still mapping each per-test obligation to a one-line
derivation. -/

/-! ### Newton iteration invariant (sqrt's two loops)

The Babylonian iteration converges to `⌊√a⌋`. A formal proof needs:

* `babylonian_step_AM_GM : ∀ a x, 0 < x → a / x + x ≥ 2 * Nat.sqrt a` (AM-GM lower bound)
* `babylonian_step_descent : ∀ a x, 0 < x → Nat.sqrt a + 1 ≤ x → (a / x + x) / 2 < x`
* `babylonian_step_floor : ∀ a x, 0 < x → x * x ≥ a → (a / x + x) / 2 * ((a / x + x) / 2) ≥ a ∨ ...`

These have no analogue in `Hax/MissingLean/Nat/`. -/

/-- Closed-form for `sqrt`: there exists a `u64 r` satisfying both bounds,
    and that's the returned value. From this one private theorem every
    obligation below derives in one or two lines.

    Stuck sub-goal: the two-loop convergence proof. After unfolding both
    `rust_primitives.hax.while_loop`s, we obtain a sequential composition
    of two `Loop.MonoLoopCombinator.while_loop`s on state `(x, xn)`.
    `Spec.MonoLoopCombinator.while_loop` gives us a triple per loop, but
    the intermediate state must be threaded — the post of loop 1 must
    imply the pre of loop 2. The natural strong invariant
    "`x * x ≥ a`" (carried from after loop 1) is preserved by loop 2's
    body via `babylonian_step_descent`, and loop 2 terminates via the
    measure `x.toNat` since `x > xn` and `x' = xn`. Loop 1 terminates
    because `cond (xn, (a/xn + xn)/2) = false` after one iteration — the
    loop runs at most once, since `(a/xn + xn)/2 ≤ xn` whenever
    `xn * xn ≥ a` (which AM-GM gives us after one step).

    Structural unblock: a self-contained `natSqrt` (or `Nat.sqrt`-equivalent)
    lemma library: `nat_sqrt_le`, `nat_sqrt_succ_lt`, `babylonian_step_floor`,
    and `babylonian_step_descent`, added to this file or the Hax prelude.
    With those, the Stage 1 triple is a routine application of
    `Spec.MonoLoopCombinator.while_loop` twice, and Stage 2 is the standard
    `RustM.Triple_iff_BitVec` discharge. -/
private theorem sqrt_postcondition (x : u64) :
    ∃ r : u64, sqrt_u64.sqrt x = RustM.ok r
      ∧ r.toNat * r.toNat ≤ x.toNat
      ∧ x.toNat < (r.toNat + 1) * (r.toNat + 1) := by
  -- Case split on the `a < 4` branch.
  rcases Nat.lt_or_ge x.toNat 4 with h_lt | h_ge
  · -- Small input branch: enumerate {0, 1, 2, 3}.
    -- Each value closes by unfolding `sqrt` (the `a < 4` branch returns directly,
    -- never entering any loop) and `decide` for the squeeze bounds.
    have h_enum : x.toNat = 0 ∨ x.toNat = 1 ∨ x.toNat = 2 ∨ x.toNat = 3 := by omega
    rcases h_enum with h | h | h | h
    · have hx : x = 0 := UInt64.toNat_inj.mp h
      refine ⟨0, ?_, ?_, ?_⟩
      · rw [hx]; unfold sqrt_u64.sqrt; rfl
      · rw [h]; decide
      · rw [h]; decide
    · have hx : x = 1 := UInt64.toNat_inj.mp h
      refine ⟨1, ?_, ?_, ?_⟩
      · rw [hx]; unfold sqrt_u64.sqrt; rfl
      · rw [h]; decide
      · rw [h]; decide
    · have hx : x = 2 := UInt64.toNat_inj.mp h
      refine ⟨1, ?_, ?_, ?_⟩
      · rw [hx]; unfold sqrt_u64.sqrt; rfl
      · rw [h]; decide
      · rw [h]; decide
    · have hx : x = 3 := UInt64.toNat_inj.mp h
      refine ⟨1, ?_, ?_, ?_⟩
      · rw [hx]; unfold sqrt_u64.sqrt; rfl
      · rw [h]; decide
      · rw [h]; decide
  · -- Newton-iteration branch (`x.toNat ≥ 4`).
    -- This is where the proof is stuck. After case-splitting the small inputs out,
    -- the goal reduces to proving the postcondition when the implementation runs
    -- the log2 + two-Newton-loop pipeline. Discharging requires:
    --   1. `log2_postcondition`: `sqrt_u64.log2 a = RustM.ok (Nat.log2 a.toNat)` as
    --      a `u32`, proved by a Stage-1+2 pattern over the single log2 loop.
    --   2. An initial-guess bound: `2 ^ ((Nat.log2 a + 1) / 2) ≤ a` (so the shift
    --      doesn't overflow and the division `a / x` doesn't divide by zero).
    --   3. A Newton step lemma: after at most one iteration of loop 1,
    --      `x * x ≥ a`. Then loop 1 exits, and loop 2 brings `x` down to ⌊√a⌋.
    --   4. Loop-2 invariant: `x * x ≥ a` is preserved, and `x` strictly decreases
    --      while `x > xn`, terminating at `x = ⌊√a⌋`.
    -- Stuck sub-goal: lemma (3), the AM-GM-style bound
    -- `(a / x + x) / 2 * ((a / x + x) / 2) ≥ a` whenever `0 < x` and the
    -- corresponding Newton step is taken. Discharging this in `Nat` arithmetic
    -- requires `Nat.add_div_two_ge_sqrt`-style reasoning, which has no analogue
    -- in `Hax/MissingLean/Nat/`.
    -- Structural unblock: a self-contained `natSqrt` (or `Nat.sqrt`-equivalent)
    -- library: `nat_sqrt_le_self`, `nat_lt_succ_sqrt`, `babylonian_step_floor`,
    -- `babylonian_step_descent`. With those four, the Stage 1 triple is a
    -- routine application of `Spec.MonoLoopCombinator.while_loop` twice;
    -- Stage 2 is the standard `RustM.Triple_iff_BitVec` discharge.
    sorry

/-! ### Uniqueness of the integer square root

`r² ≤ x < (r+1)²` characterises `r = ⌊√x⌋` uniquely. The uniqueness lemma
is a routine `Nat`-level case analysis dischargeable by `omega` plus a
monotonicity argument on squaring. -/

/-- If `r² ≤ x < (r+1)²` and `s² ≤ x < (s+1)²`, then `r = s`.
    Proof: WLOG `r ≤ s`. Then `r² ≤ s²` and `(s+1)² > x ≥ r²`, so `s ≥ r`.
    If `r < s`, then `s ≥ r + 1`, so `s² ≥ (r+1)² > x`, contradicting
    `s² ≤ x`. Hence `r = s`. -/
private theorem nat_sqrt_unique (x r s : Nat)
    (hr_le : r * r ≤ x) (hr_lt : x < (r + 1) * (r + 1))
    (hs_le : s * s ≤ x) (hs_lt : x < (s + 1) * (s + 1)) :
    r = s := by
  rcases Nat.lt_trichotomy r s with hlt | heq | hgt
  · -- r < s: s ≥ r + 1, so s² ≥ (r+1)² > x, contradicting s² ≤ x.
    exfalso
    have hge : r + 1 ≤ s := hlt
    have h_sq_le_sq : (r + 1) * (r + 1) ≤ s * s :=
      Nat.mul_le_mul hge hge
    omega
  · exact heq
  · -- r > s: r ≥ s + 1, so r² ≥ (s+1)² > x, contradicting r² ≤ x.
    exfalso
    have hge : s + 1 ≤ r := hgt
    have h_sq_le_sq : (s + 1) * (s + 1) ≤ r * r :=
      Nat.mul_le_mul hge hge
    omega

/-- Concrete uniqueness on `u64`: if both `r` and the supplied `target` satisfy
    the squeeze bounds at `x.toNat`, then `r = UInt64.ofNat target`. -/
private theorem sqrt_value_unique (x : u64) (target : Nat)
    (h_target_lt : target < 2 ^ 64)
    (h_le : target * target ≤ x.toNat)
    (h_lt : x.toNat < (target + 1) * (target + 1))
    (r : u64)
    (hr_le : r.toNat * r.toNat ≤ x.toNat)
    (hr_lt : x.toNat < (r.toNat + 1) * (r.toNat + 1)) :
    r = UInt64.ofNat target := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofNat_of_lt' h_target_lt]
  exact nat_sqrt_unique x.toNat r.toNat target hr_le hr_lt h_le h_lt

/-! ## Postcondition: lower bound (`r² ≤ x`)

Captures the property test `prop_sqrt_lower_bound`: for the returned root `r`,
`r.toNat * r.toNat ≤ x.toNat`. A buggy implementation that returns too large a
value (e.g. `x` itself, or `r + 1` for non-perfect squares) is caught here. -/
theorem sqrt_lower_bound (x : u64) :
    ∃ r : u64, sqrt_u64.sqrt x = RustM.ok r ∧ r.toNat * r.toNat ≤ x.toNat := by
  obtain ⟨r, hsqrt, hle, _⟩ := sqrt_postcondition x
  exact ⟨r, hsqrt, hle⟩

/-! ## Postcondition: upper bound (`x < (r+1)²`) -/
theorem sqrt_upper_bound (x : u64) :
    ∃ r : u64, sqrt_u64.sqrt x = RustM.ok r
      ∧ x.toNat < (r.toNat + 1) * (r.toNat + 1) := by
  obtain ⟨r, hsqrt, _, hlt⟩ := sqrt_postcondition x
  exact ⟨r, hsqrt, hlt⟩

/-! ## Totality / no panic -/
theorem sqrt_total (x : u64) :
    ∃ v : u64, sqrt_u64.sqrt x = RustM.ok v := by
  obtain ⟨r, hsqrt, _, _⟩ := sqrt_postcondition x
  exact ⟨r, hsqrt⟩

/-! ## Specific values: small inputs

The `a < 4` branch returns directly without entering any loop, so these four
close by `rfl` after unfolding `sqrt`. -/

theorem sqrt_zero : sqrt_u64.sqrt 0 = RustM.ok 0 := by
  unfold sqrt_u64.sqrt
  rfl

theorem sqrt_one : sqrt_u64.sqrt 1 = RustM.ok 1 := by
  unfold sqrt_u64.sqrt
  rfl

theorem sqrt_two : sqrt_u64.sqrt 2 = RustM.ok 1 := by
  unfold sqrt_u64.sqrt
  rfl

theorem sqrt_three : sqrt_u64.sqrt 3 = RustM.ok 1 := by
  unfold sqrt_u64.sqrt
  rfl

/-- `x = 4` is the smallest input that enters the loop branch.
    Uniqueness of the squeeze bounds at `x = 4` pins `r = 2`. -/
theorem sqrt_four : sqrt_u64.sqrt 4 = RustM.ok 2 := by
  obtain ⟨r, hsqrt, hle, hlt⟩ := sqrt_postcondition (4 : u64)
  rw [hsqrt]
  congr 1
  have h4 : (4 : u64).toNat = 4 := rfl
  rw [h4] at hle hlt
  exact sqrt_value_unique (4 : u64) 2 (by decide) (by decide) (by decide) r
    (by rw [h4]; exact hle) (by rw [h4]; exact hlt)

/-! ## Specific values: doctest

`x = 12345 * 12345`, `x = 12345 * 12345 + 1`, `x = 12345 * 12345 - 1`.
Each pins down the result via uniqueness of the squeeze bounds. -/

theorem sqrt_doctest_exact :
    sqrt_u64.sqrt (12345 * 12345 : u64) = RustM.ok (12345 : u64) := by
  obtain ⟨r, hsqrt, hle, hlt⟩ := sqrt_postcondition (12345 * 12345 : u64)
  rw [hsqrt]
  congr 1
  have hx : (12345 * 12345 : u64).toNat = 12345 * 12345 := by decide
  rw [hx] at hle hlt
  exact sqrt_value_unique (12345 * 12345 : u64) 12345
    (by decide) (by decide) (by decide) r
    (by rw [hx]; exact hle) (by rw [hx]; exact hlt)

theorem sqrt_doctest_plus_one :
    sqrt_u64.sqrt (12345 * 12345 + 1 : u64) = RustM.ok (12345 : u64) := by
  obtain ⟨r, hsqrt, hle, hlt⟩ := sqrt_postcondition (12345 * 12345 + 1 : u64)
  rw [hsqrt]
  congr 1
  have hx : (12345 * 12345 + 1 : u64).toNat = 12345 * 12345 + 1 := by decide
  rw [hx] at hle hlt
  exact sqrt_value_unique (12345 * 12345 + 1 : u64) 12345
    (by decide) (by decide) (by decide) r
    (by rw [hx]; exact hle) (by rw [hx]; exact hlt)

theorem sqrt_doctest_minus_one :
    sqrt_u64.sqrt (12345 * 12345 - 1 : u64) = RustM.ok (12344 : u64) := by
  obtain ⟨r, hsqrt, hle, hlt⟩ := sqrt_postcondition (12345 * 12345 - 1 : u64)
  rw [hsqrt]
  congr 1
  have hx : (12345 * 12345 - 1 : u64).toNat = 12345 * 12345 - 1 := by decide
  rw [hx] at hle hlt
  exact sqrt_value_unique (12345 * 12345 - 1 : u64) 12344
    (by decide) (by decide) (by decide) r
    (by rw [hx]; exact hle) (by rw [hx]; exact hlt)

end Sqrt_u64Obligations
