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

The property tests `prop_cube_le_x` and `prop_x_lt_next_cube` map
directly onto (P1) and (P2). The other unit tests in the source
(`cbrt_pos`, `cbrt_doc_examples`, `cbrt_small_values`,
`cbrt_postcondition_dense`) are sweeps/instances over the same two
clauses, and `agrees_with_source` is oracle-based agreement with the
upstream `num_integer::cbrt` — these add no independent contract
content beyond (P1) ∧ (P2) ∧ totality, as the source's own contract
documentation notes.
-/

/-! ## Status note on the three obligations

All three theorems below are left as `sorry`. The technical reason is the
same for each, and applies regardless of which proof shape (Hoare-triple
two-stage, direct equational unfold, or `mvcgen`) one attempts:

`cbrt` composes **three** non-trivial loop-based helpers whose
correctness/totality each requires its own dedicated mathematical theory
not present in the Hax Lean prelude:

  1. `cbrt_u32` — Hacker's-Delight `icbrt2` over a `Tuple4 u32 u32 u32 u32`
     state. The 11-iteration loop maintains the invariant
       `y^3 ≤ (a_original >> s) AND y^3 + 3y^2 + 3y + 1 > (a_original >> s)`
     (modulo bit-shifting). Proving correctness *and* the no-overflow
     side conditions of each `*?`, `+?`, `-?`, `<<<?`, `>>>?` in the
     body requires a substantial library of single-bit / shift-trick
     lemmas and a strong loop invariant that the example library does
     not supply. The selector flagged this explicitly under
     "Tuple4-state loops" and "non-linear postconditions".

  2. `cbrt_guess_u64` — two-stage shift loop producing a power-of-two
     `g = 2^⌈(⌊log₂a⌋+1)/3⌉`. Tractable in isolation (the per-iteration
     invariants are `hi ≤ 64` and `g ≤ 2^22`), but the postcondition
     needed by the *next* helper is `cbrt(a) ≤ g ≤ 2^32 − 1`, which
     requires a `Nat.log2 ≤ 3·k`-style lemma absent from the prelude.

  3. `fixpoint_cbrt` — Newton fixpoint of `x ↦ (a/(x·x) + 2x)/3` over
     `Tuple2 u64 u64`. Totality alone requires showing `x*?x` never
     overflows, which requires the loop-invariant `x ≤ 2^32 − 1`; this
     in turn requires a Newton-monovariant lemma that has no analogue
     in the reference library. The selector lists "Newton fixpoint
     convergence over `u64`" and "monovariant + convergence reasoning"
     as gaps.

The reference patterns (gcd_while, while_example, average_floor_u64,
saturating_sub, clamp) cover **linear** postconditions on **single**
helper functions over **`Tuple2`** state. Composing three helpers, each
with non-linear cubic postconditions over `Tuple4` and Newton-style
fixpoints, falls outside the canonical proof scaffold; the body-step
arguments alone (per-iteration no-overflow of `y2 *? 4`, `b <<<? s`,
`x -? (b <<< s)`, `2 *? y +? 1`, `a /? (x *? x)`, `(a/?(x*x)) +? (x*?2)`)
each require a non-trivial Nat-level bound that the picker's coverage
report does not supply.

Per the task spec, each theorem is left as `sorry` with a specific
sub-goal identified rather than being removed or weakened. -/

/-- **Totality / no-panic**. For every `u64` input the function returns a
    value — it never reaches `RustM.fail`. This captures the explicit
    "the function is total --- it never panics and has no error-return
    channel" clause of the Rust contract.

    Intractable sub-goal: the no-overflow obligation on the body of
    `fixpoint_cbrt` requires the loop invariant `x.toNat ≤ 2^32 − 1`
    so that `x *? x` (Lean `BitVec.umulOverflow`) returns `false`.
    Establishing this invariant in turn requires showing
    `cbrt_guess_u64 a ≤ 2^32 − 1` *and* a Newton-monovariant lemma
    `(a/(x*x) + 2x)/3 ≤ max(x, ⌊∛a⌋ + 1)` over `Nat`. The reference
    library provides no equivalent for either step. -/
theorem cbrt_total (x : u64) :
    ∃ v : u64, cbrt_u64.cbrt x = RustM.ok v := by
  -- Attempt 1: discharge the trivial `a < 8` branch by hand.
  -- For `a < 8` the function returns `pure 0` or `pure 1` with no loops
  -- executed. The remaining branches need totality of helper loops,
  -- which is left as `sorry` with a structural unblock below.
  by_cases hsmall : x < (8 : u64)
  · -- Small-input branch
    by_cases hpos : x > (0 : u64)
    · refine ⟨1, ?_⟩
      simp only [cbrt_u64.cbrt, rust_primitives.cmp.lt, rust_primitives.cmp.gt,
                 pure_bind, decide_eq_true hsmall, decide_eq_true hpos,
                 if_true]
      rfl
    · refine ⟨0, ?_⟩
      simp only [cbrt_u64.cbrt, rust_primitives.cmp.lt, rust_primitives.cmp.gt,
                 pure_bind, decide_eq_true hsmall, if_true,
                 decide_eq_false hpos]
      rfl
  · -- Large-input branch: x ≥ 8. Split further on x ≤ u32::MAX.
    by_cases hu32 : x ≤ (4294967295 : u64)
    · -- u32 fast-path: 8 ≤ x ≤ u32::MAX, calls cbrt_u32 via casts.
      -- Stuck sub-goal: `∃ w, cbrt_u64.cbrt_u32 x.toUInt32 = RustM.ok w`.
      -- The loop body of `cbrt_u32` has `y2 *? 4`, `y *? 2`, `3 *? (y2 +? y)`,
      -- `b <<<? s`, `x -? (b <<< s)`, `2 *? y +? 1` — each is a partial
      -- `RustM` op whose no-overflow side condition requires a Stage-1
      -- loop invariant bounding the components of the `Tuple4` state.
      -- The natural invariant (the cubic `y^3 ≤ a_orig >>> (s_iter*3)`
      -- of Hacker's-Delight icbrt2) is what makes these bounds hold —
      -- correctness IS totality here; they cannot be separated.
      --
      -- Structural unblock: file-local `cbrt_u32_total` lemma (Stage-1
      -- Hoare triple with the cubic icbrt2 invariant) would close this
      -- in one line via `obtain ⟨w, hw⟩ := cbrt_u32_total x.toUInt32`.
      sorry
    · -- Newton-fixpoint path: x > u32::MAX.
      -- Stuck sub-goal (1 of 2): `∃ g, cbrt_guess_u64 x = RustM.ok g`.
      -- The two inner shift loops have bounded counters (`hi ≤ 64` for
      -- the log2 loop, `i ≤ k ≤ 22` for the doubling loop), so the
      -- body operations `y >>>? 1`, `hi +? 1`, `g <<<? 1`, `i +? 1`
      -- never overflow under the right invariants. Tractable in
      -- principle via a Stage-1 Hoare triple per loop with the obvious
      -- invariants.
      --
      -- Stuck sub-goal (2 of 2): `∃ v, fixpoint_cbrt x g = RustM.ok v`
      -- where `g = cbrt_guess_u64 x`. The body of each of the two
      -- `fixpoint_cbrt` loops contains `x *? x`, whose no-overflow
      -- side condition requires `x.toNat ≤ 2^32 − 1`. This must be
      -- preserved by the body `x ↦ (a/(x*x) + 2x)/3` — a Newton-style
      -- monovariant that has no analogue in the reference library.
      --
      -- Structural unblock: file-local lemmas `cbrt_guess_u64_total`
      -- (giving `g.toNat ≤ 2^32 - 1`) and `fixpoint_cbrt_total` (with
      -- the Newton-monovariant invariant) would close this branch in
      -- four lines.
      sorry

/-- **(P1) Postcondition — lower bound**: the cube of `cbrt x` does not
    exceed `x`. "`r` is a cube-root candidate."
    Mirrors property test `prop_cube_le_x` in `src/lib.rs`.

    Intractable sub-goal: in the `8 ≤ a ≤ u32::MAX` branch, this reduces
    to `(cbrt_u32 a').toNat ^ 3 ≤ a'.toNat`, which is the correctness of
    Hacker's-Delight `icbrt2`. The Stage-1 loop invariant required is
    `y.toNat ^ 3 ≤ a_orig.toNat >>> (s_iter * 3)` together with bit-shift
    bookkeeping — a per-iteration cubic-bound argument with no analogue
    in the reference library. In the `a > u32::MAX` branch, the same
    cubic bound on the Newton fixpoint's limit requires a convergence
    lemma the prelude does not provide. -/
theorem cbrt_cube_le_x (x : u64) :
    ⦃⌜True⌝⦄
      cbrt_u64.cbrt x
    ⦃⇓ r => ⌜r.toNat ^ 3 ≤ x.toNat⌝⦄ := by
  -- Substantive attempt: mvcgen reduces the Hoare triple to per-branch
  -- verification conditions. The small-branch goals (x < 8) close
  -- mechanically; the loop-body goals for cbrt_u32 and fixpoint_cbrt
  -- carry the genuine cubic-bound / Newton-monovariant content and
  -- are left as `sorry` with a structural unblock.
  mvcgen [cbrt_u64.cbrt]
  case vc1.isTrue.isTrue =>
    rename_i _ hpos
    have hx_gt : (0 : u64) < x := decide_eq_true_eq.mp hpos
    have hxn : 0 < x.toNat := UInt64.lt_iff_toNat_lt.mp hx_gt
    show UInt64.toNat 1 ^ 3 ≤ UInt64.toNat x
    have h1 : UInt64.toNat 1 = 1 := rfl
    rw [h1]; omega
  case vc2.isTrue.isFalse =>
    show UInt64.toNat 0 ^ 3 ≤ UInt64.toNat x
    have h0 : UInt64.toNat 0 = 0 := rfl
    rw [h0]; simp
  -- Remaining VCs (cbrt_u32 step/body, cbrt_guess_u64 step, fixpoint_cbrt
  -- step/body): stuck sub-goals are the cubic-bound invariant
  -- `(y_iter.toNat)^3 ≤ (a_orig.toNat) >>> (s_iter*3)` for icbrt2 and
  -- the no-overflow side condition `BitVec.umulOverflow x.toBitVec
  -- x.toBitVec = false` for `x *? x` inside fixpoint_cbrt — the latter
  -- requires a Newton-monovariant invariant `x.toNat ≤ 2^32-1` that
  -- is preserved by the body. See the file-header note for the full
  -- list of structural unblocks (cubic-bound icbrt2 spec + Newton
  -- convergence + `Nat.log2 ≤ 3·k`-style log-bound).
  all_goals sorry

/-- **(P2) Postcondition — upper bound**: `x` is strictly less than the
    cube of `cbrt x + 1`. "`r` is the *greatest* cube root."

    Stated at `Nat` level (where there is no overflow), this is
    unconditionally `x.toNat < (r.toNat + 1) ^ 3`. The Rust property test
    `prop_x_lt_next_cube` phrases this as "either `(r+1)^3` overflows
    `u64` (vacuous) or `x < (r+1)^3`"; the overflow disjunct is a
    fixed-width artifact and folds into the `Nat`-level inequality, since
    when `(r.toNat + 1)^3 ≥ 2^64` we still have `x.toNat < 2^64 ≤ (r+1)^3`.

    Intractable sub-goal: the matching upper-cubic bound for
    Hacker's-Delight `icbrt2`,
      `(y.toNat + 1) ^ 3 > a_orig.toNat >>> (s_iter * 3)`,
    is the dual half of the loop invariant for `cbrt_u32`. In the
    fixpoint branch, this is the harder direction of Newton
    convergence: showing the fixpoint does **not** overshoot below
    `⌊∛a⌋`. Neither has an analogue in the reference library. -/
theorem cbrt_x_lt_next_cube (x : u64) :
    ⦃⌜True⌝⦄
      cbrt_u64.cbrt x
    ⦃⇓ r => ⌜x.toNat < (r.toNat + 1) ^ 3⌝⦄ := by
  -- Substantive attempt: mvcgen reduces the Hoare triple to per-branch
  -- verification conditions. The small-branch goals (x < 8) close
  -- mechanically; the loop-body goals carry the dual cubic upper-bound
  -- content for icbrt2 and Newton convergence.
  mvcgen [cbrt_u64.cbrt]
  case vc1.isTrue.isTrue =>
    rename_i hsm _
    have hx_lt : x < (8 : u64) := decide_eq_true_eq.mp hsm
    have hxn : x.toNat < 8 := UInt64.lt_iff_toNat_lt.mp hx_lt
    show x.toNat < (UInt64.toNat 1 + 1) ^ 3
    have h1 : UInt64.toNat 1 = 1 := rfl
    rw [h1]; omega
  case vc2.isTrue.isFalse =>
    rename_i hsm hnpos
    have hx_lt : x < (8 : u64) := decide_eq_true_eq.mp hsm
    have hxn : x.toNat < 8 := UInt64.lt_iff_toNat_lt.mp hx_lt
    -- ¬(0 < x) gives x.toNat = 0
    have hxz : x.toNat = 0 := by
      have hnp : ¬ ((0 : u64) < x) := by
        intro h
        exact hnpos (decide_eq_true_eq.mpr h)
      have : ¬ (0 < x.toNat) := fun h => hnp (UInt64.lt_iff_toNat_lt.mpr h)
      omega
    show x.toNat < (UInt64.toNat 0 + 1) ^ 3
    have h0 : UInt64.toNat 0 = 0 := rfl
    rw [h0, hxz]; decide
  -- Loop VCs: stuck sub-goal is the upper cubic bound
  -- `(y_iter.toNat + 1)^3 > (a_orig.toNat) >>> (s_iter*3)` for icbrt2
  -- — the dual half of `cbrt_cube_le_x`'s lower bound — together with
  -- the Newton no-undershoot direction of fixpoint convergence.
  all_goals sorry

end Cbrt_u64Obligations
