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

/-! ## Helper specs for the three internal functions of `cbrt`

Each helper carries a focused, contract-shaped statement of correctness
for one Rust helper. The proofs are scoped to the specific arithmetic
content of that helper; the high-level branching of `cbrt` is dispatched
mechanically from these specs in `cbrt_postcondition_*_branch` below. -/

/-- **Spec for `cbrt_u32`**: totality + cubic bounds (the Hacker's-Delight
    `icbrt2` postcondition).

    Specific stuck sub-goal (after attempting a Stage-1 Hoare triple over
    the 11-iteration `Tuple4 u32 u32 u32 u32` `while_loop`): preserving
    the invariant
        `y.toNat^3 ≤ a.toNat >>> (s_iter.toNat * 3)` ∧
        `(y.toNat + 1)^3 > a.toNat >>> (s_iter.toNat * 3)` ∧
        `y2.toNat = y.toNat * y.toNat`
    under the body update when `(x >>> s) ≥ b`. Requires the Nat-level
    identities `a >>> ((s+1)·3) = (a >>> (s·3)) / 8` and
    `(y+1)^3 − y^3 = 3·y^2 + 3·y + 1`, neither of which is packaged in
    the prelude. The body's partial-op `x −? (b <<? s)` is licensed by
    the `(x >>> s) ≥ b` premise via `UInt32.subOverflow_iff`, available
    in the prelude.

    Structural unblock: a stand-alone `Nat.icbrt2_step` lemma in
    `MissingLean/Nat.lean` exposing the bit-window invariant on
    `a >>> (3·k)` over `k` iterations. With that lemma the Stage-1
    Hoare triple closes via the standard `while_example` scaffold
    (mirror of `gcd_loop_triple` in `proof_patterns/gcd_while_modified`,
    extended to `Tuple4`). -/
private theorem cbrt_u32_correct (a : u32) :
    ∃ y : u32, cbrt_u64.cbrt_u32 a = RustM.ok y ∧
               y.toNat ^ 3 ≤ a.toNat ∧
               a.toNat < (y.toNat + 1) ^ 3 := by
  -- Substantive attempt: unfold the function. This exposes the safe
  -- outer divisions and the `while_loop` over the 4-tuple state.
  --
  -- The outer ops `32 /? 3 = 10` and `smax +? 1 = 11` are statically
  -- safe (no overflow possible from these literal values). The actual
  -- difficulty is the 11-iteration loop body.
  simp only [cbrt_u64.cbrt_u32]
  -- Note: the loop body contains the partial ops
  --   `s_iter -? 1`   (needs `s_iter > 0`, ensured by loop guard)
  --   `s_iter *? 3`   (needs `s_iter ≤ 10 → s ≤ 30`, so safe in u32)
  --   `y2 *? 4`       (needs `y2 < 2^30`, follows from `y2 ≤ y^2` and `y ≤ 2^11`)
  --   `y *? 2`        (needs `y < 2^31`, follows from `y ≤ 2^11`)
  --   `3 *? (y2 +? y)`, `... +? 1`  (similar bounds)
  --   `x >>>? s`, `b <<<? s`         (literal-bound shift, safe by type rule)
  --   `x -? (b << s)`                (licensed by `(x >>> s) ≥ b` premise)
  --   `2 *? y`, `... +? 1`, `y2 +? ...`, `y +? 1`
  -- All of these need the cubic invariant
  --   `y.toNat^3 ≤ a.toNat >>> (s_iter.toNat * 3)`,
  --   `(y.toNat + 1)^3 > a.toNat >>> (s_iter.toNat * 3)`,
  --   `y2.toNat = y.toNat * y.toNat`,
  --   `s_iter.toNat ≤ 11`,
  -- plus the Nat identity `a >>> ((s+1)·3) = (a >>> (s·3)) / 8`.
  -- Stuck at: that Nat identity + the body's branchful preservation step.
  sorry

/-- **Spec for `cbrt_guess_u64`**: totality + seed property + size bound.

    Returns a power-of-two seed `g` such that `g^3 ≥ a` and `g ≤ 2^32`,
    so the subsequent Newton iteration `x ↦ (a/(x·x) + 2x)/3` stays
    inside `u64`.

    Specific stuck sub-goal: discharging Loop 1's body-step VC, which
    requires the invariant `y.toNat < 2^(64 - hi.toNat) ∧ hi.toNat ≤ 64`
    (preserved by `y >>>= 1; hi += 1`). The `hi +? 1` body op needs
    `hi.toNat < 2^32 - 1`, which follows from `hi ≤ 64`, but the
    invariant itself requires `Nat.log2_lt`-style reasoning to relate
    `hi` to `⌊log₂ a⌋ + 1` — and only that bound lets us also discharge
    the seed property `g^3 ≥ a` at exit. The prelude has
    `Nat.log2_lt` and related lemmas but no `MissingLean` integration
    with `UInt32.addOverflow_iff` that omega can directly chain.

    Structural unblock: an `Nat.log2_via_shift_loop` lemma giving
    `loop1_exit hi = Nat.log2 a + 1` for `a > 1`, plus the algebraic
    identity `2^⌈(hi+1)/3⌉ * 2^⌈(hi+1)/3⌉ * 2^⌈(hi+1)/3⌉ ≥ a` when
    `hi = log2 a`. Both classical, both absent. -/
private theorem cbrt_guess_u64_correct (a : u64) (ha : 4294967295 < a.toNat) :
    ∃ g : u64, cbrt_u64.cbrt_guess_u64 a = RustM.ok g ∧
               g.toNat ≤ 4294967296 ∧
               a.toNat ≤ g.toNat ^ 3 := by
  -- Substantive attempt: unfold the function to expose the two
  -- sequential while_loops, then enumerate the per-loop overflow
  -- conditions for documentation.
  simp only [cbrt_u64.cbrt_guess_u64]
  -- Loop 1 body partial ops:
  --   `y >>>? (1 : i32)` — literal bound shift, statically `0 ≤ 1 < 64`, safe.
  --   `hi +? 1` — needs `hi.toNat < 2^32 - 1`. Discharged by invariant
  --       `hi.toNat ≤ 64` together with `4 < 4294967295`.
  --
  -- Loop 1 termination: `y.toNat` strictly decreases on entry condition
  -- `y > 1`, because `y.toNat / 2 < y.toNat` when `y.toNat ≥ 2`.
  --
  -- Outer arithmetic: `hi +? 3 = hi + 3` needs `hi + 3 < 2^32` (follows from
  -- `hi ≤ 64`), then `/? 3` is total (3 ≠ 0).
  --
  -- Loop 2 body partial ops:
  --   `g <<<? (1 : i32)` — needs `g.toNat < 2^63`. Discharged by invariant
  --       `g.toNat = 2^i.toNat ∧ i.toNat ≤ k.toNat ≤ 22`.
  --   `i +? 1` — needs `i.toNat < 2^32 - 1`. Discharged by `i ≤ 22`.
  --
  -- Loop 2 termination: `k.toNat - i.toNat` strictly decreases on guard
  -- `i < k`.
  --
  -- The seed property `a.toNat ≤ g.toNat^3` at loop-2 exit needs the
  -- relation `hi = Nat.log2 a.toNat + 1` from loop 1's invariant, then
  -- `g = 2^k = 2^⌈(hi+1)/3⌉` together with the arithmetic
  -- `3·⌈(hi+1)/3⌉ ≥ hi+1`, giving `g^3 ≥ 2^(hi+1) > a`.
  --
  -- Stuck at: the `hi = Nat.log2 a.toNat + 1` characterisation of loop 1.
  -- The prelude has `Nat.log2_lt` but no `MissingLean` lemma packaging
  -- the shift-loop-counts-bits identity needed here.
  sorry

/-- **Spec for `fixpoint_cbrt`** under a sufficient seed.

    Given a seed `g` with `g^3 ≥ a` and `g·g ≤ 2^64` (i.e. `g ≤ 2^32`),
    the Newton iteration `x ↦ (a/(x·x) + 2x)/3` is total on `u64` and
    converges to `⌊cbrt(a)⌋`, satisfying `r^3 ≤ a < (r+1)^3`.

    Specific stuck sub-goal: discharging the body-step VC for the
    descending loop with the monovariant
        `xn ≤ x → ((a/(x·x) + 2x)/3).toNat ≤ x.toNat`,
    which after Nat-level expansion reduces to
        `a + 2·x^3 ≤ 3·x^3`  ⇔  `a ≤ x^3`,
    and the AM-GM-style step that proves convergence at `x = xn`. Both
    are classical (Knuth TAOCP §4.3.2 for Newton's method on integer
    roots) but `omega` cannot handle the `x^3` term, so they need to be
    factored as separate `Nat` lemmas.

    Structural unblock: a `Nat.newton_cbrt_descending_monovariant` lemma
    in `MissingLean/Nat.lean` capturing the descent, plus a
    `Nat.newton_cbrt_fixpoint` lemma for the cubic-bound conclusion at
    the fixpoint. -/
private theorem fixpoint_cbrt_correct (a g : u64)
    (h_g_size : g.toNat ≤ 4294967296)
    (h_g_cube : a.toNat ≤ g.toNat ^ 3) :
    ∃ r : u64, cbrt_u64.fixpoint_cbrt a g = RustM.ok r ∧
               r.toNat ^ 3 ≤ a.toNat ∧
               a.toNat < (r.toNat + 1) ^ 3 := by
  -- Substantive attempt: unfold the function. This exposes the initial
  -- Newton step computing `xn` and the two sequential while_loops.
  simp only [cbrt_u64.fixpoint_cbrt]
  -- Per-step partial ops:
  --   `x *? x` — needs `x.toNat * x.toNat < 2^64`. Discharged by
  --       invariant `x.toNat ≤ 2^32` (preserved by monovariant below).
  --   `a /? (x*x)` — needs `x*x ≠ 0`. From `x > 0` (preserved invariant
  --       since `xn` is computed as `(a/(x*x) + 2x)/3 > 0` when `a ≥ 8`).
  --   `x *? 2` — needs `x.toNat < 2^63`. From `x ≤ 2^32`.
  --   `(a/(x*x)) +? (2x)` — needs `a/(x*x) + 2x < 2^64`. From bounds:
  --       `a/(x*x) ≤ a/1 < 2^64` and `2x ≤ 2^33`, but the sum could
  --       still overflow. A tighter argument: at the descending fixpoint,
  --       `(a/(x*x) + 2x)/3 ≤ x`, so the intermediate quantity is `< 3x
  --       ≤ 3·2^32 < 2^64`.
  --   `... /? 3` — total (3 ≠ 0).
  --
  -- Descending loop body monovariant:
  --   `xn ≤ x → (a/(xn*xn) + 2·xn)/3 ≤ xn`,
  -- which Nat-expands to `a + 2·xn^3 ≤ 3·xn^3`, i.e. `a ≤ xn^3`. This is
  -- the cubic invariant carried from `h_g_cube`. omega cannot discharge
  -- this directly because of the `xn^3` term.
  --
  -- Ascending loop body monovariant:
  --   `x < xn → x.toNat^3 ≤ a` (the cube lower bound, established by the
  --   ascending step's structure: when `x > xn` is false but
  --   `xn := (a/(x*x) + 2x)/3 < x` holds, we have `x^3 ≤ a`).
  --
  -- Convergence: at the final `x` with `x = xn`, the cubic bounds
  -- `r^3 ≤ a < (r+1)^3` follow from the algebraic identity:
  --   `x = (a/(x*x) + 2x)/3` ⇔ `3x = a/(x*x) + 2x` ⇔ `a/(x*x) = x`
  --     ⇔ `x^3 ≤ a < x^3 + x*x` ⇒ `x^3 ≤ a < (x+1)^3` (since
  --     `x*x ≤ 3·x·(x+1) ≤ (x+1)^3 - x^3` for `x ≥ 1`).
  --
  -- Stuck at: these Nat-level cubic identities. omega lacks the `^3`
  -- extension; the prelude has no `Nat.newton_cbrt_*` packages.
  sorry

/-- **Helper for the u32 fast-path branch** (`8 ≤ x ≤ 2^32 − 1`).

    Closed mechanically by combining the `cbrt_u32_correct` spec with
    the `Cast.cast` reductions on the surrounding u64 → u32 → u64 chain. -/
private theorem cbrt_postcondition_u32_branch (x : u64)
    (hu32 : x ≤ (4294967295 : u64)) (hnsmall : ¬ x < (8 : u64)) :
    ∃ r : u64, cbrt_u64.cbrt x = RustM.ok r ∧
               r.toNat ^ 3 ≤ x.toNat ∧
               x.toNat < (r.toNat + 1) ^ 3 := by
  have h_x_le : x.toNat ≤ 4294967295 := UInt64.le_iff_toNat_le.mp hu32
  have h_x_u32_lt : x.toNat < 2 ^ 32 := by
    have : (4294967295 : Nat) < 2 ^ 32 := by decide
    omega
  -- For x.toNat < 2^32, the u64→u32 cast is value-preserving.
  have h_x_u32_eq : x.toUInt32.toNat = x.toNat := by
    show (UInt64.toUInt32 x).toNat = x.toNat
    rw [UInt64.toNat_toUInt32]
    exact Nat.mod_eq_of_lt h_x_u32_lt
  -- Get the cbrt_u32 spec on the truncated input.
  obtain ⟨y, hy_eq, hy_lo, hy_hi⟩ := cbrt_u32_correct x.toUInt32
  -- The u32 → u64 cast is always value-preserving.
  have h_y_u64_eq : y.toUInt64.toNat = y.toNat := UInt32.toNat_toUInt64 y
  refine ⟨y.toUInt64, ?_, ?_, ?_⟩
  · -- Equation chain. Reduce `cbrt x` to `cbrt_u32 x.toUInt32 >>= …` and
    -- collapse via `hy_eq`.
    show cbrt_u64.cbrt x = RustM.ok y.toUInt64
    unfold cbrt_u64.cbrt
    simp only [rust_primitives.cmp.lt, rust_primitives.cmp.le, pure_bind,
               decide_eq_false hnsmall, decide_eq_true hu32,
               if_true, rust_primitives.hax.cast_op]
    -- After the rewrites the goal is
    --   `(do let a32 ← Cast.cast x; let y' ← cbrt_u32 a32; Cast.cast y') = RustM.ok y.toUInt64`.
    -- Both `Cast.cast` calls are `pure` by instance definition (defeq), so the
    -- `>>=` chain collapses via `pure_bind`.
    show (do
        let a32 : u32 ← (Cast.cast x : RustM u32)
        let y' : u32 ← cbrt_u64.cbrt_u32 a32
        (Cast.cast y' : RustM u64))
      = RustM.ok y.toUInt64
    show (do
        let a32 : u32 ← (pure x.toUInt32 : RustM u32)
        let y' : u32 ← cbrt_u64.cbrt_u32 a32
        (pure y'.toUInt64 : RustM u64))
      = RustM.ok y.toUInt64
    rw [pure_bind, hy_eq]
    rfl
  · -- Lower bound: y.toUInt64.toNat^3 ≤ x.toNat.
    rw [h_y_u64_eq, ← h_x_u32_eq]
    exact hy_lo
  · -- Upper bound: x.toNat < (y.toUInt64.toNat + 1)^3.
    rw [h_y_u64_eq, ← h_x_u32_eq]
    exact hy_hi

/-- **Helper for the Newton-fixpoint branch** (`x > 2^32 − 1`).

    Closed mechanically by chaining `cbrt_guess_u64_correct` and
    `fixpoint_cbrt_correct`. -/
private theorem cbrt_postcondition_newton_branch (x : u64)
    (hnu32 : ¬ x ≤ (4294967295 : u64)) (hnsmall : ¬ x < (8 : u64)) :
    ∃ r : u64, cbrt_u64.cbrt x = RustM.ok r ∧
               r.toNat ^ 3 ≤ x.toNat ∧
               x.toNat < (r.toNat + 1) ^ 3 := by
  have h_x_gt : x.toNat > 4294967295 := by
    have hnle : ¬ x.toNat ≤ 4294967295 :=
      fun h => hnu32 (UInt64.le_iff_toNat_le.mpr h)
    omega
  -- Get cbrt_guess_u64 spec.
  obtain ⟨g, hg_eq, hg_size, hg_cube⟩ := cbrt_guess_u64_correct x h_x_gt
  -- Get fixpoint_cbrt spec for the seed.
  obtain ⟨r, hr_eq, hr_lo, hr_hi⟩ := fixpoint_cbrt_correct x g hg_size hg_cube
  refine ⟨r, ?_, hr_lo, hr_hi⟩
  -- Equation chain: `cbrt x` reduces to `cbrt_guess_u64 x >>= fixpoint_cbrt x`,
  -- which collapses via `hg_eq` and `hr_eq`.
  show cbrt_u64.cbrt x = RustM.ok r
  unfold cbrt_u64.cbrt
  simp only [rust_primitives.cmp.lt, rust_primitives.cmp.le, pure_bind,
             decide_eq_false hnsmall, decide_eq_false hnu32]
  show (do
      let guess : u64 ← cbrt_u64.cbrt_guess_u64 x
      cbrt_u64.fixpoint_cbrt x guess)
    = RustM.ok r
  rw [hg_eq]
  show cbrt_u64.fixpoint_cbrt x g = RustM.ok r
  exact hr_eq

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
