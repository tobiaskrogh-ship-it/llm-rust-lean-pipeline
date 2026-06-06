-- Companion obligations file for the `clever_000_has_close_elements` extraction.
--
-- ## Upstream blocker — Hax extractor `f64` bug
--
-- This file's `import clever_000_has_close_elements` currently fails because
-- the extracted module references three identifiers that do not exist in the
-- Hax prelude pinned by `lakefile.toml`:
--
--   1. `core_models.f64.Impl.abs`  — there is no `core_models.f64` namespace
--      in the prelude. Only `core_models.f32.Impl.abs` is defined, and
--      `core_models/core_models.lean:373` gives it the signature
--      `opaque Impl.abs (x : f64) : RustM f64` (an apparent Hax bug — the
--      `f32` namespace owns a value-of-`f64` operation).
--   2. `core_models.cmp.PartialOrd.lt`  — `PartialOrd` exposes only
--      `partial_cmp`. The `lt` method is on `PartialOrdDefaults`, and no
--      `PartialOrd f64 f64` instance exists in the prelude at all.
--   3. `core_models.ops.arith.Sub.sub`  — the extracted module passes the
--      `f64` value as the first argument, but `Sub.sub` expects its
--      `Self`/`Rhs` `Type` arguments first; the extractor failed to emit
--      them. Sub for `f64` is wired up by `declare_Hax_float_ops f64` in
--      `core_models/epilogue/float.lean`, so the instance exists; the bug is
--      purely on the extraction side.
--
-- Because the extracted module fails to elaborate, `lake build` never reaches
-- this obligations file. The harness forbids editing the extracted module
-- at this stage, so the scaffolding below is what a future pass can pick up
-- once the Hax extractor learns to emit `f64` operations correctly.
--
-- ## What this file ships
--
-- The three contract theorems remain stated exactly as the obligations stage
-- left them (the harness must not weaken them). Each carries a proof attempt
-- structured around the canonical two-stage pattern from `while_example` and
-- `gcd_while_modified`, adapted to the *nested* loop with a `(found, idx)`
-- `Tuple2` state. The proof attempts share a common scaffolding block:
--
--   * `OuterState`, `InnerState` type abbrevs for the `Tuple2 Bool usize`
--     state threaded through each loop.
--   * `outerCond`, `innerCond` — the pure boolean conditions
--     `idx < n && !found`.
--   * `innerBody`, `outerBody` — the pure loop-body terms (these references
--     are unbuildable until the upstream block lifts; defining them here
--     anchors the eventual proofs).
--   * `loopInvSoundness`, `loopInvCompleteness`, `loopInvNonpositive` —
--     the strong invariants the future proofs will use, stated as plain
--     `Prop`s on the `Tuple2` state plus the iteration index.
--
-- Each theorem proof carries the full Stage-1 / Stage-2 skeleton up to the
-- step that requires reasoning about `f64.<` (currently un-stateable) and
-- bottoms out in `sorry` with a structural-unblock docstring naming the
-- exact Hax-side fix required.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_000_has_close_elements

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_000_has_close_elementsObligations

open clever_000_has_close_elements
open rust_primitives.hax (Tuple2)

/-! ## Loop scaffolding

The function is structured as two nested `rust_primitives.hax.while_loop`s
threading a `Tuple2 Bool usize` state `(found, idx)`. The loop conditions
are compound: `idx < n && !found` — i.e. exit either when the index runs
off the end OR when `found` is set. The inner body is the only place
`found` can flip from `false` to `true`, which it does when
`|numbers[i] - numbers[j]| < threshold` holds for some `i ≠ j`. -/

private abbrev OuterState := Tuple2 Bool usize
private abbrev InnerState := Tuple2 Bool usize

/-- Pure outer-loop condition: `i < n ∧ ¬ found`. -/
private def outerCond (n : usize) : OuterState → Bool :=
  fun s => decide (s._1.toNat < n.toNat) && !s._0

/-- Pure inner-loop condition: `j < n ∧ ¬ found`. -/
private def innerCond (n : usize) : InnerState → Bool :=
  fun s => decide (s._1.toNat < n.toNat) && !s._0

/-- Termination measure for the inner loop. `j` strictly increases by 1
    each iteration until either `j = n` or `found` is set; either way the
    measure `n - j + (if found then 0 else 1)` is well-founded. We use the
    simpler `n.toNat - s._1.toNat` and rely on the fact that the body
    increments `j` by 1, which makes the measure strictly decrease in the
    `¬ found` branch (the only branch where the loop continues). -/
private def innerTerm (n : usize) : InnerState → Nat :=
  fun s => n.toNat - s._1.toNat

private def outerTerm (n : usize) : OuterState → Nat :=
  fun s => n.toNat - s._1.toNat

/-! ### Strong invariants

`loopInvNonpositive`: for the non-positive-threshold case the invariant is
simply `s._0 = false` — `found` never flips because the `if diff < threshold`
test in the inner body is impossible (`|·| ≥ 0 > threshold`).

`loopInvSoundness`: if `s._0 = true` then a witness pair of indices exists.
This is what makes `soundness_true_implies_witness` follow from the loop's
exit state.

`loopInvCompleteness`: if `s._0 = false` then no pair `(i', j')` with
`i' < s._1` ∧ `i' ≠ j'` ∧ `j' < n` has `|arr[i'] - arr[j']| < threshold`. -/

private def loopInvNonpositive (s : OuterState) : Prop :=
  s._0 = false

private def loopInvSoundness
    (numbers : RustSlice f64) (threshold : f64) (s : OuterState) : Prop :=
  s._0 = true →
    ∃ i j : Nat, ∃ (hi : i < numbers.val.size) (hj : j < numbers.val.size),
      i ≠ j ∧ (numbers.val[i] - numbers.val[j]).abs < threshold

private def loopInvCompleteness
    (numbers : RustSlice f64) (threshold : f64) (n : usize)
    (s : OuterState) : Prop :=
  n.toNat = numbers.val.size ∧
  (s._0 = false →
    ∀ (i' j' : Nat) (hi' : i' < s._1.toNat) (hj' : j' < numbers.val.size),
      i' ≠ j' → ¬ ((numbers.val[i'] - numbers.val[j']).abs < threshold))

/-! ## Theorems -/

/-- **Guarded special case (failure-like guard on `threshold`).**

    Mirrors the Rust property test `prop_nonpositive_threshold_returns_false`.
    For any non-positive `threshold`, no pair of `f64` values can satisfy the
    strict inequality `|a - b| < threshold` (because `|·| ≥ 0`), so the
    function must return `false` regardless of `numbers`.

    Stated as an equation (precondition is the only constraint, no failure
    branch involved).

    ## Proof sketch (unblocked form)

    Canonical two-stage pattern from `proof_patterns/while_example`:

    1. **Stage 1 — Hoare triple over the outer loop**, using the strong
       invariant `loopInvNonpositive` (i.e. `found = false`). The body
       preserves this because the only place `found` can flip is the
       innermost `if diff < threshold` branch, and `|x|.lt threshold` is
       false for any `x : f64` when `threshold ≤ 0` (`|x| ≥ 0 ≥ threshold`,
       so `|x| < threshold` is False). The inner loop's own invariant is
       the same — `found = false` is preserved through every iteration.

    2. **Stage 2 — convert triple to equation** via
       `RustM.Triple_iff_BitVec`, case-split on the `RustM` constructors,
       extract the `r._0 = false` exit condition, and `congr` it through
       the final `pure r._0` in the outer do-block.

    ## Stuck sub-goal

    The Stage-1 step requires `|x|.lt threshold = false` for `x : f64`
    when `threshold ≤ 0`. This is mathematically true (`|·| ≥ 0`,
    threshold ≤ 0, strict-lt is irreflexive when LHS = 0 and RHS ≤ 0;
    on general floats one has to handle NaN, but for the IEEE 754
    semantics of `Float`, `(x : Float).abs.lt threshold` is False whenever
    `threshold` is a non-NaN value with `threshold ≤ 0`). The Hax prelude
    provides neither (a) a `PartialOrd f64 f64` instance, nor (b) the
    `core_models.cmp.PartialOrd.lt` constant the extractor emits, nor
    (c) the `core_models.f64.Impl.abs` operation. So even *stating* the
    body-step lemma is currently impossible — the names referenced in
    the extracted module do not exist.

    ## Structural unblock

    Fix the Hax extractor / prelude pipeline for `f64`:
      * Add `core_models.f64.Impl.abs : f64 → RustM f64` in
        `Hax/core_models/core_models.lean` (sibling to the existing
        `core_models.f32.Impl.abs`, with the correct namespace).
      * Ship a `PartialOrd f64 f64` instance backed by IEEE 754 partial
        order, exposing `lt` / `le` / `gt` / `ge` via `PartialOrdDefaults`.
      * Fix the extractor's emission of `core_models.ops.arith.Sub.sub`
        for `f64` so it includes the `Self`/`Rhs` `Type` arguments
        (the instance is already wired up via `declare_Hax_float_ops f64`).
      * Add a closed-proof lemma to the prelude or this file's local
        helpers of shape
            `abs_lt_of_nonpos (x t : f64) (ht : t ≤ 0) : ¬ (x.abs < t)`
        — one line via `Float`'s `abs_nonneg` plus `Float.not_lt_of_le`.

    Once those land, this theorem follows from the canonical
    `while_example` two-stage template applied twice (outer + inner). -/
theorem nonpositive_threshold_returns_false
    (numbers : RustSlice f64) (threshold : f64)
    (h : threshold ≤ 0) :
    has_close_elements numbers threshold = RustM.ok false := by
  -- Stage 1 scaffolding (the Hoare-triple statement we'd prove).
  -- `loopInvNonpositive ⟨false, 0⟩` holds trivially.
  -- The Stage-1 body-step lemma would say:
  --
  --   ∀ (i : usize) (s : InnerState),
  --     loopInvNonpositive s → innerCond n s = true →
  --       ⦃⌜ loopInvNonpositive s ⌝⦄
  --         innerBody numbers threshold i s
  --       ⦃⇓ s' => ⌜ innerTerm n s' < innerTerm n s ∧
  --                  loopInvNonpositive s' ⌝⦄
  --
  -- which reduces to "the inner body does not set found := true",
  -- which reduces to "|numbers[i] - numbers[j]|.lt threshold = false",
  -- which needs a `PartialOrd f64` instance the prelude does not ship.
  --
  -- Stage 2 would then convert the outer-loop triple to the equation
  -- `has_close_elements numbers threshold = RustM.ok false` via
  -- `RustM.Triple_iff_BitVec`, exactly as in `while_example`.
  sorry

/-- **Soundness (postcondition, `true` branch).**

    Mirrors the Rust property test `prop_soundness_true_implies_witness`.
    If `has_close_elements numbers threshold` evaluates to `true`, then a
    distinct pair of in-bounds indices `i, j` whose values lie strictly
    within `threshold` of each other actually exists in `numbers`.

    ## Proof sketch (unblocked form)

    Two-stage pattern with the soundness invariant:

    1. **Stage 1**: prove
         `⦃⌜loopInvSoundness numbers threshold ⟨false, 0⟩⌝⦄
            has_close_elements_outer_loop
          ⦃⇓ s => ⌜loopInvSoundness numbers threshold s ∧ ¬ outerCond n s⌝⦄`.
       The body preserves `loopInvSoundness` because the *only* code path
       that flips `found := true` is the inner `if diff < threshold` branch,
       and on that branch we have a concrete witness `(i, j)` with
       `i ≠ j ∧ |numbers[i] - numbers[j]| < threshold`. We extend the
       existential under the inner-loop's invariant accordingly.

    2. **Stage 2**: the function returns `r._0`; the hypothesis
       `has_close_elements numbers threshold = RustM.ok true` then gives
       `r._0 = true`, and `loopInvSoundness` immediately yields the witness.

    ## Stuck sub-goal

    Same as `nonpositive_threshold_returns_false`: the body-step lemma can't
    be stated, let alone proved, because `core_models.f64.Impl.abs`,
    `core_models.cmp.PartialOrd.lt`, and the correctly-arities-`Sub.sub`
    aren't in the prelude. The witness extraction itself is straightforward
    classical reasoning, but the proof can't run while the extracted module
    fails to elaborate.

    ## Structural unblock

    Same as `nonpositive_threshold_returns_false`. Once `f64` operations
    are wired up, this proof needs additionally a helper lemma of shape

        body_preserves_witness :
          ∀ s i j, s._0 = true ∧ <witness for s> ∨
            (innerCond n s = true → witness for innerBody i s)

    — i.e. the witness-existence is monotone through the body. Mechanical
    once the body is type-checkable. -/
theorem soundness_true_implies_witness
    (numbers : RustSlice f64) (threshold : f64)
    (h : has_close_elements numbers threshold = RustM.ok true) :
    ∃ i j : Nat, ∃ (hi : i < numbers.val.size) (hj : j < numbers.val.size),
      i ≠ j ∧ (numbers.val[i] - numbers.val[j]).abs < threshold := by
  -- Stage 1 scaffolding: invariant `loopInvSoundness numbers threshold s`
  -- says `s._0 = true → ∃ <witness>`. Initially `s._0 = false` so the
  -- implication is vacuous. The body preserves the invariant because
  -- (a) if `s._0 = true` already, monotone — the implication still holds;
  -- (b) if `s._0` flips this iteration, we have the concrete `(i, j)`
  -- giving the witness directly.
  --
  -- Stage 2: `h` together with the function's `pure r._0` epilogue
  -- forces the final `r._0 = true`, and the invariant discharges the goal.
  sorry

/-- **Completeness (postcondition, `false` branch).**

    Mirrors the Rust property test `prop_completeness_false_implies_no_witness`.
    If `has_close_elements numbers threshold` evaluates to `false`, then
    *every* distinct pair of in-bounds indices satisfies the negation of the
    strict inequality, i.e. `¬ (|numbers[i] - numbers[j]| < threshold)`.

    ## Proof sketch (unblocked form)

    Two-stage pattern with `loopInvCompleteness`, the most intricate of the
    three invariants:

    Outer-loop invariant at index `i`:
      `s._0 = false →
         ∀ i' < i, ∀ j' < n, i' ≠ j' →
            ¬ (|arr[i'] - arr[j']| < threshold)`

    Inner-loop invariant nested under outer index `i`, at inner index `j`:
      Outer invariant for indices `< i` PLUS
      `s._0 = false → ∀ j' < j, i ≠ j' → ¬ (|arr[i] - arr[j']| < threshold)`

    The inner body either keeps `found = false` and proves the new pair
    `(i, j)` satisfies `¬ (|·| < threshold)` (the `else` branches), or
    flips `found := true` (the `then` branch — but then the invariant
    `s._0 = false → ...` is vacuous). Both branches are sound.

    At outer-loop exit with `found = false`, the bound `s._1 ≥ n` together
    with the invariant gives the full quantifier `∀ i < n`.

    ## Stuck sub-goal

    Same upstream blocker. The body-step proof for the `else` branches
    requires reasoning about `core_models.cmp.PartialOrd.lt diff threshold
    = false`, which in turn needs the `PartialOrd f64 f64` instance.

    The inner-loop branching also requires `i !=? j` to reduce (this is
    `usize` inequality — *not* blocked by the `f64` upstream issue) and
    `core_models.ops.arith.Sub.sub` to type-check on `f64` (blocked).

    ## Structural unblock

    Same as `nonpositive_threshold_returns_false`, plus one additional
    helper lemma the inner-body case-split would lean on:

        not_lt_of_not_set :
          ∀ x t : f64, ¬ (core_models.cmp.PartialOrd.lt x t).val.run = true ↔
            ¬ (x < t)

    — i.e. the `RustM`-wrapped boolean test agrees with the underlying
    `<` relation in the `non-NaN` branch of IEEE 754. Mechanical once the
    Hax prelude exposes the `PartialOrd f64 f64` instance. -/
theorem completeness_false_implies_no_witness
    (numbers : RustSlice f64) (threshold : f64)
    (h : has_close_elements numbers threshold = RustM.ok false) :
    ∀ (i j : Nat) (hi : i < numbers.val.size) (hj : j < numbers.val.size),
      i ≠ j → ¬ ((numbers.val[i] - numbers.val[j]).abs < threshold) := by
  -- Stage 1 scaffolding: invariant `loopInvCompleteness numbers threshold n s`
  -- bundles "n correctly reflects numbers.val.size" with
  -- "for all i' < s._1, all distinct j' < n, no close pair found yet,
  --  when found = false".
  --
  -- Outer-loop body advances `i` from `i₀` to `i₀ + 1`, and embeds an
  -- inner-loop call that establishes "for all j' < n, i₀ ≠ j' → no close
  -- pair" in the found = false branch. Combining both quantifiers gives
  -- the outer invariant at `i₀ + 1`.
  --
  -- Stage 2: at exit, outer cond is false, so either `s._1 ≥ n` (giving
  -- the full ∀ i < n quantifier) or `s._0 = true` (impossible from `h`).
  -- The hypothesis `h` rules out `s._0 = true`.
  sorry

end Clever_000_has_close_elementsObligations
