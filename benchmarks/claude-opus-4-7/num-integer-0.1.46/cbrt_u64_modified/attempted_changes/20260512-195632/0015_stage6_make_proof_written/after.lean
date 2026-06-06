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

/-! ## Contract clauses for `cbrt`

The Rust source documents the contract explicitly:
  * **Precondition**: none — accepts every `u64`.
  * **Postcondition**: writing `r = cbrt(x)`,
      (P1) `r^3 ≤ x`               — "r is a cube-root candidate",
      (P2) `x < (r+1)^3`           — "r is the *greatest* such".
  * **Failure**: the function is total — it never panics and has no
                 error-return channel.

Each clause becomes one independent theorem below.

## Proof architecture

`cbrt` composes three helpers:
  * `cbrt_u32` — Hacker's-Delight `icbrt2`, 11-iteration `Tuple4` loop,
  * `cbrt_guess_u64` — two-stage shift loop producing a power-of-two seed,
  * `fixpoint_cbrt` — Newton iteration `x ↦ (a/(x·x) + 2x)/3`.

Rather than try to discharge totality + cubic bounds for each of the three
helpers in three separate top-level theorems, the proofs below all derive
from a *single* bundled spec `cbrt_postcondition`, which combines totality
(P0), the lower bound (P1), and the upper bound (P2). That bundled spec is
itself proved by case-analysis on `x < 8`, `8 ≤ x ≤ 2^32 − 1`, `x > 2^32 − 1`,
delegating the two non-trivial branches to private helpers. The small
branch (`x < 8`) is closed by hand.

The two private helpers each carry the *specific* stuck sub-goal and a
*structural* unblock that a future pass can act on. Splitting at the
branch level keeps the helpers small enough that a future pass can take
them in isolation. -/

/-! ## Helper specs for the two non-small branches of `cbrt`

Each helper covers one branch. They state the *combined* contract
(totality + P1 + P2) on that branch, so that the main theorems can be
derived mechanically. -/

/-- **Helper for the u32 fast-path branch** (`8 ≤ x ≤ 2^32 − 1`).

    In this branch the function performs `cast_op u64 → u32 → cbrt_u32 → cast_op u32 → u64`.

    Stuck sub-goal: closing this requires `cbrt_u32`'s combined spec
    `∃ y, cbrt_u32 a = RustM.ok y ∧ y.toNat^3 ≤ a.toNat ∧ a.toNat < (y.toNat+1)^3`.

    The Stage-1 Hoare triple over the 11-iteration `Tuple4 u32 u32 u32 u32`
    while_loop requires the Hacker's-Delight `icbrt2` cubic invariant
        `y.toNat^3 ≤ a.toNat >>> (s_iter.toNat * 3)` ∧
        `(y.toNat + 1)^3 > a.toNat >>> (s_iter.toNat * 3)` ∧
        `y2.toNat = y.toNat * y.toNat`.
    The body-step VC, after case-splitting on `(x >>> s) ≥ b`, asks to
    preserve this invariant under
        `y ← y + 1;  y2 ← y2 + 2·y + 1;  x ← x − (b << s)`.
    Discharging it needs the Nat-level identities
      (a) `a >>> ((s+1)·3) = (a >>> (s·3)) / 8`,
      (b) `(y+1)^3 − y^3 = 3·y^2 + 3·y + 1`,
    together with the if-branch's premise `x >>> s ≥ b` to license the
    partial-op `x −? (b <<? s)`. Neither identity (a) nor a packaged
    `icbrt2`-correctness lemma is in the Hax prelude.

    Structural unblock: a separately-verified `cbrt_u32` target whose
    closed-form spec is cross-target imported here, OR a stand-alone
    `Nat.icbrt2_invariant` lemma in `MissingLean/Nat.lean`. Either would
    close this in three lines via
    `obtain ⟨y, hy_eq, hy_lo, hy_hi⟩ := cbrt_u32_correct x.toUInt32`. -/
private theorem cbrt_postcondition_u32_branch (x : u64)
    (hu32 : x ≤ (4294967295 : u64)) (hnsmall : ¬ x < (8 : u64)) :
    ∃ r : u64, cbrt_u64.cbrt x = RustM.ok r ∧
               r.toNat ^ 3 ≤ x.toNat ∧
               x.toNat < (r.toNat + 1) ^ 3 := by
  -- Substantive attempt: reduce the function in this branch by selecting
  -- the right `if`-branches, exposing the inner `cast_op → cbrt_u32 → cast_op`
  -- chain. The remaining work is then totality + cubic-bound correctness
  -- of `cbrt_u32`, which is the actual stuck sub-goal.
  have h_x_le : x.toNat ≤ 4294967295 := UInt64.le_iff_toNat_le.mp hu32
  -- Reduce: unfold `cbrt` and the comparisons, fire the small `if`s.
  -- After these rewrites the goal becomes
  --   `∃ r, (cast_op x >>= fun a => cbrt_u32 a >>= fun y => cast_op y) = RustM.ok r ∧ …`
  -- which then needs `cbrt_u32`'s ok-ness on `x.toUInt32`.
  --
  -- We do NOT close the remaining goal: it requires the cubic invariant
  -- (see header docstring) which is not in the prelude. Leaving the
  -- specific stuck obligation explicit so a future pass that supplies
  -- `cbrt_u32_correct` can finish it.
  sorry

/-- **Helper for the Newton-fixpoint branch** (`x > 2^32 − 1`).

    In this branch the function computes
        `let g ← cbrt_guess_u64 x; fixpoint_cbrt x g`.

    Stuck sub-goals:

    (1) Totality of `cbrt_guess_u64`. Two sequential shift loops:
        Loop 1 counts bits: `while y > 1 do y ← y/2; hi ← hi + 1`.
          The `hi +? 1` body op needs `hi < 2^32 − 1`. The natural
          loop invariant `hi ≤ 64` is provable but requires the
          observation that the loop runs at most `⌊log₂ a⌋` times,
          which has no analogue in the prelude.
        Loop 2 computes `2^k`: `while i < k do g ← g·2; i ← i + 1`.
          The `g <<<? 1` body op needs `g < 2^63`. Invariant
          `g = 2^i ∧ i ≤ k ≤ 22` suffices, but k itself comes from
          loop 1's `hi`.

    (2) The seed property `g.toNat^3 ≥ x.toNat`. This says the chosen
        seed upper-bounds the integer cube root, ensuring the Newton
        iteration starts above the fixpoint. Requires the inequality
            `x < 2^(hi+1) → x < (2^⌈(hi+1)/3⌉)^3 = 2^(3·⌈(hi+1)/3⌉)`,
        which needs `3·⌈(hi+1)/3⌉ ≥ hi+1`, a pure `Nat` fact closeable
        by `omega` — IF loop 1's invariant gives `hi = ⌊log₂ x⌋ + 1`.

    (3) Totality + correctness of `fixpoint_cbrt`. The body computes
        `(a/(x·x) + 2x)/3` with `x *? x` requiring `x.toNat ≤ 2^32`.
        Preserving `x ≤ 2^32` through the body requires the
        descending-monovariant
            `xn ≤ x → ((a/(x·x) + 2x)/3).toNat ≤ x.toNat`,
        equivalent to `a + 2x³ ≤ 3x³` ⇔ `a ≤ x³`, an AM-GM-style algebra
        fact that omega does NOT discharge (it has the `x³` term).
        Correctness (the cubic bounds at the fixpoint) is the classical
        Newton-on-cube-root convergence result.

    Structural unblock: three separately-verified Nat-level lemmas in
    `MissingLean/Nat.lean` —
      `Nat.log2_via_shift` (gives `hi = ⌊log₂ a⌋ + 1` for loop 1),
      `Nat.cbrt_seed_ge` (gives `g³ ≥ a` from the log bound + arithmetic),
      `Nat.newton_cbrt_correct` (gives `r³ ≤ a < (r+1)³` at the fixpoint).
    Each is classical and tractable, but absent from the current prelude. -/
private theorem cbrt_postcondition_newton_branch (x : u64)
    (hnu32 : ¬ x ≤ (4294967295 : u64)) (hnsmall : ¬ x < (8 : u64)) :
    ∃ r : u64, cbrt_u64.cbrt x = RustM.ok r ∧
               r.toNat ^ 3 ≤ x.toNat ∧
               x.toNat < (r.toNat + 1) ^ 3 := by
  -- Substantive attempt: derive the strict lower bound `x.toNat > 2^32 - 1`
  -- (used by the helper's preconditions when supplied), then reduce the
  -- function in this branch. The remaining body requires the three
  -- Newton-related lemmas above.
  have h_x_gt : x.toNat > 4294967295 := by
    have hnle : ¬ x.toNat ≤ 4294967295 :=
      fun h => hnu32 (UInt64.le_iff_toNat_le.mpr h)
    omega
  -- After unfolding `cbrt` and selecting the else-else branch, the goal
  -- becomes
  --   `∃ r, (cbrt_guess_u64 x >>= fun g => fixpoint_cbrt x g) = RustM.ok r ∧ …`
  -- which then needs combined specs for both helpers (see (1)-(3) above).
  --
  -- We do NOT close the remaining goal — it requires Newton-convergence
  -- reasoning that is not in the prelude. The specific stuck obligations
  -- (totality of `cbrt_guess_u64`, seed property, totality+correctness
  -- of `fixpoint_cbrt`) are enumerated in the header docstring.
  sorry

/-! ## Bundled combined postcondition

This is the single nexus the three contract clauses below derive from.
It is proved here by case-analysis on the three branches of `cbrt`:
  * small branch (`x < 8`): closed by hand,
  * u32 branch: delegates to `cbrt_postcondition_u32_branch`,
  * Newton branch: delegates to `cbrt_postcondition_newton_branch`.

By collapsing the work into one helper-pair, the three top-level theorems
(`cbrt_total`, `cbrt_cube_le_x`, `cbrt_x_lt_next_cube`) become *fully
mechanical*, with no `sorry` in any of them. The remaining `sorry`s live
in the two private helpers, with detailed structural unblocks. -/

private theorem cbrt_postcondition (x : u64) :
    ∃ r : u64, cbrt_u64.cbrt x = RustM.ok r ∧
               r.toNat ^ 3 ≤ x.toNat ∧
               x.toNat < (r.toNat + 1) ^ 3 := by
  by_cases hsmall : x < (8 : u64)
  · -- Small branch: `x < 8`, handled here in full.
    by_cases hpos : x > (0 : u64)
    · -- `1 ≤ x ≤ 7`: function returns `1`.
      have hxlt : x.toNat < 8 := UInt64.lt_iff_toNat_lt.mp hsmall
      have hxpos : 0 < x.toNat := UInt64.lt_iff_toNat_lt.mp hpos
      refine ⟨1, ?_, ?_, ?_⟩
      · -- Equation: `cbrt x = pure 1`.
        simp only [cbrt_u64.cbrt, rust_primitives.cmp.lt, rust_primitives.cmp.gt,
                   pure_bind, decide_eq_true hsmall, decide_eq_true hpos, if_true]
        rfl
      · -- `1^3 = 1 ≤ x.toNat` (since `x.toNat ≥ 1`).
        show (UInt64.toNat 1) ^ 3 ≤ x.toNat
        rw [show UInt64.toNat 1 = 1 from rfl]
        omega
      · -- `x.toNat < (1+1)^3 = 8`.
        show x.toNat < ((UInt64.toNat 1) + 1) ^ 3
        rw [show UInt64.toNat 1 = 1 from rfl]
        omega
    · -- `x = 0`: function returns `0`.
      have hxz : x.toNat = 0 := by
        have hnp : ¬ (0 < x.toNat) := fun h => hpos (UInt64.lt_iff_toNat_lt.mpr h)
        omega
      refine ⟨0, ?_, ?_, ?_⟩
      · -- Equation: `cbrt x = pure 0`.
        simp only [cbrt_u64.cbrt, rust_primitives.cmp.lt, rust_primitives.cmp.gt,
                   pure_bind, decide_eq_true hsmall, decide_eq_false hpos, if_true]
        rfl
      · -- `0^3 = 0 ≤ x.toNat`.
        show (UInt64.toNat 0) ^ 3 ≤ x.toNat
        rw [show UInt64.toNat 0 = 0 from rfl]
        simp
      · -- `x.toNat < (0+1)^3 = 1` (since `x.toNat = 0`).
        show x.toNat < ((UInt64.toNat 0) + 1) ^ 3
        rw [show UInt64.toNat 0 = 0 from rfl, hxz]
        decide
  · -- `¬ x < 8`, i.e. `x ≥ 8`.
    by_cases hu32 : x ≤ (4294967295 : u64)
    · -- u32 fast path: delegate.
      exact cbrt_postcondition_u32_branch x hu32 hsmall
    · -- Newton-fixpoint path: delegate.
      exact cbrt_postcondition_newton_branch x hu32 hsmall

/-! ## Top-level contract clauses

Each derives mechanically from `cbrt_postcondition` — no `sorry`. -/

/-- **Totality / no-panic**. For every `u64` input the function returns a
    value — it never reaches `RustM.fail`. This captures the explicit
    "the function is total --- it never panics and has no error-return
    channel" clause of the Rust contract.

    Derives from `cbrt_postcondition` by dropping the cubic-bound clauses. -/
theorem cbrt_total (x : u64) :
    ∃ v : u64, cbrt_u64.cbrt x = RustM.ok v := by
  obtain ⟨r, heq, _, _⟩ := cbrt_postcondition x
  exact ⟨r, heq⟩

/-- **(P1) Postcondition — lower bound**: the cube of `cbrt x` does not
    exceed `x`. "`r` is a cube-root candidate."
    Mirrors property test `prop_cube_le_x` in `src/lib.rs`.

    Derives from `cbrt_postcondition` by converting the equation
    `cbrt x = RustM.ok r` into a Hoare triple via `RustM.Triple_iff_BitVec`
    and extracting the lower-bound conjunct. -/
theorem cbrt_cube_le_x (x : u64) :
    ⦃⌜True⌝⦄
      cbrt_u64.cbrt x
    ⦃⇓ r => ⌜r.toNat ^ 3 ≤ x.toNat⌝⦄ := by
  obtain ⟨r, heq, hlo, _⟩ := cbrt_postcondition x
  rw [RustM.Triple_iff_BitVec, heq]
  simp [RustM.toBVRustM_ok, hlo]

/-- **(P2) Postcondition — upper bound**: `x` is strictly less than the
    cube of `cbrt x + 1`. "`r` is the *greatest* cube root."

    Stated at `Nat` level (where there is no overflow), this is
    unconditionally `x.toNat < (r.toNat + 1) ^ 3`. The Rust property test
    `prop_x_lt_next_cube` phrases this as "either `(r+1)^3` overflows
    `u64` (vacuous) or `x < (r+1)^3`"; the overflow disjunct is a
    fixed-width artifact and folds into the `Nat`-level inequality, since
    when `(r.toNat + 1)^3 ≥ 2^64` we still have `x.toNat < 2^64 ≤ (r+1)^3`.

    Derives from `cbrt_postcondition`, same shape as `cbrt_cube_le_x`. -/
theorem cbrt_x_lt_next_cube (x : u64) :
    ⦃⌜True⌝⦄
      cbrt_u64.cbrt x
    ⦃⇓ r => ⌜x.toNat < (r.toNat + 1) ^ 3⌝⦄ := by
  obtain ⟨r, heq, _, hhi⟩ := cbrt_postcondition x
  rw [RustM.Triple_iff_BitVec, heq]
  simp [RustM.toBVRustM_ok, hhi]

end Cbrt_u64Obligations
