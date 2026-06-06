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
                 if_true, ite_true]
    · refine ⟨0, ?_⟩
      simp only [cbrt_u64.cbrt, rust_primitives.cmp.lt, rust_primitives.cmp.gt,
                 pure_bind, decide_eq_true hsmall, if_true, ite_true,
                 decide_eq_false hpos, if_false, ite_false]
  · -- Large-input branches: require totality of cbrt_u32 (Hacker's-Delight
    -- icbrt2 over Tuple4 state) and of cbrt_guess_u64 + fixpoint_cbrt
    -- (Newton fixpoint over Tuple2 u64 u64).
    -- Stuck sub-goal (after splitting on `a ≤ u32::MAX`):
    --   * In the u32 branch, the body of `cbrt_u32` contains
    --     `y2 *? 4`, `y *? 2`, `3 *? (y2 +? y)`, `b <<<? s` — each is
    --     a partial `RustM` op whose `false`-overflow side condition
    --     requires a loop-invariant bound `y2 < 2^30 ∧ y < 2^11` etc.
    --     The Stage-1 invariant for icbrt2 (a cubic-bound on `y^3 ≤
    --     a_orig >>> (s_iter*3)`) is what makes these bounds hold —
    --     i.e. correctness IS totality, they cannot be separated.
    --   * In the fixpoint branch, `fixpoint_cbrt`'s body contains
    --     `x *? x`. Totality requires `x.toNat ≤ 2^32 − 1`, which
    --     requires both `cbrt_guess_u64 a ≤ 2^32 − 1` (a `Nat.log2`
    --     bound) AND a Newton-monovariant preservation lemma.
    -- Structural unblock: separately-verified Stage-1 Hoare triples
    -- for `cbrt_u32` and for the two `fixpoint_cbrt` loops, with
    -- their cubic-bound and Newton-monovariant invariants, would
    -- discharge the remaining cases. The library's selector report
    -- flagged both "Tuple4-state loops" and "Newton-fixpoint
    -- convergence" as gaps in the example library.
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
  -- Intractable: requires Hacker's-Delight `icbrt2` correctness for the
  -- u32 branch and Newton-fixpoint convergence for the u64 branch.
  -- The body-step invariant `y^3 ≤ (x_orig >>> s)` is the specific
  -- sub-goal that has no prelude analogue. See file header.
  sorry

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
  -- Intractable: dual of cbrt_cube_le_x. The body-step invariant
  -- `(y+1)^3 > (x_orig >>> s)` for `cbrt_u32` and the no-undershoot
  -- direction of Newton convergence for `fixpoint_cbrt` are the
  -- specific sub-goals with no prelude analogue. See file header.
  sorry

end Cbrt_u64Obligations
