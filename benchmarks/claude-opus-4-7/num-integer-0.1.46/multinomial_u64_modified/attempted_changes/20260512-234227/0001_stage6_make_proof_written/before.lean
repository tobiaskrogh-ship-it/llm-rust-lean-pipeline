-- Companion obligations file for the `multinomial_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import multinomial_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Multinomial_u64Obligations

/-- Mathematical factorial on `Nat`, defined locally because core Lean 4
    does not ship `Nat.factorial` and we have no Mathlib in this build. -/
private def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Mathematical multinomial coefficient on a `List Nat`:
    `(∑ kᵢ)! / ∏ (kᵢ!)`. Used as the reference in `multinomial_value`. -/
private def multinomialNat (xs : List Nat) : Nat :=
  fact (xs.foldr (· + ·) 0) / xs.foldr (fun x acc => fact x * acc) 1

/-- Local list-permutation relation. Lean core does not ship `List.Perm`
    in this build, so we recreate it here for the symmetry obligation. -/
private inductive ListPerm {α : Type} : List α → List α → Prop where
  | refl  (l : List α) : ListPerm l l
  | cons  (x : α) {l₁ l₂ : List α} : ListPerm l₁ l₂ → ListPerm (x :: l₁) (x :: l₂)
  | swap  (x y : α) (l : List α) : ListPerm (x :: y :: l) (y :: x :: l)
  | trans {l₁ l₂ l₃ : List α} : ListPerm l₁ l₂ → ListPerm l₂ l₃ → ListPerm l₁ l₃

/-! ### Note on the proofs below

All five obligations are left as `sorry`. The blocker is shared by every
clause: the body of `multinomial_u64.multinomial` is built around
`rust_primitives.hax.while_loop`, which the Hax prelude implements via
`Loop.MonoLoopCombinator.while_loop` /
`Loop.MonoLoopCombinator.forIn` defined with `partial_fixpoint`. To
reason about the result of such a loop one must:

  1. Unfold `rust_primitives.hax.while_loop` to its underlying
     `Loop.MonoLoopCombinator.while_loop ...` form;
  2. State a `Prop`-level invariant on the loop's tuple state that is
     strong enough to imply the desired postcondition;
  3. Apply `Spec.MonoLoopCombinator.while_loop` (from
     `Hax/MissingLean/Std/Do/Triple/SpecLemmas.lean`) — which yields a
     Hoare triple, *not* a structural equality — and discharge the
     three resulting subgoals (invariant-at-init, invariant-preserved
     by the body, invariant + ¬cond ⇒ postcondition);
  4. Convert the Hoare-triple conclusion back into the structural
     equality the obligation states (a `RustM`-equality such as
     `multinomial k = RustM.ok 1`).

The selection stage's reference set (factorial, sum_to_n,
saturating_sub, add_one, square) does *not* contain a single instance
of `rust_primitives.hax.while_loop`, so there is no in-library proof
shape to copy. The selector flagged this as the principal gap:
"`rust_primitives.hax.while_loop` — no example uses it. The proof
agent has no in-library reference for setting up loop invariants,
discharging `pureCond`/`pureTermination`, or unfolding the tuple-state
body."

In addition, `multinomial` is built on top of `binomial`, which is
itself built on `multiply_and_divide`, which is itself built on `gcd`
— and `gcd` and `binomial` each contain their own
`rust_primitives.hax.while_loop`. Closing the obligations below
therefore requires the same loop-invariant machinery to be deployed
*three times in nested form*, plus the cross-function composition
("postcondition for one function consumed inside another's proof"),
which the selector also flagged as missing from the example library.

Each theorem's docstring records the additional technical work it
specifically requires beyond this shared blocker. -/

/-- Postcondition (boundary): `multinomial` of the empty slice returns `1`
    (the empty product, anchoring the running `r = 1` initialization).

    Technical reason this is left as `sorry`: even though the outer
    `while_loop` makes zero iterations on an empty slice (the very first
    `cond` test on the initial tuple `(0, 0, 1, 0)` evaluates to `false`
    because `remaining = 0`), we still need to drive `while_loop` to
    `pure init` from a `cond_init = false` hypothesis. The `partial_fixpoint`
    definition of `Loop.MonoLoopCombinator.forIn` does not unfold
    definitionally — there is no `_unfold` simp lemma for it in the
    prelude — and the `Spec.MonoLoopCombinator.while_loop` route would
    have to be combined with a `Triple`-to-equality conversion that is
    also not provided. -/
theorem multinomial_empty
    (k : RustSlice u64) (h : k.val.size = 0) :
    multinomial_u64.multinomial k = RustM.ok 1 := by
  sorry

/-- Postcondition (boundary): every singleton slice returns `1`, regardless
    of the entry's value. The single iteration computes
    `r = 1 * binomial(n, n) = 1`, so `multinomial(&[n]) = 1` for every `n`,
    including the extreme `n = u64::MAX`.

    Technical reason this is left as `sorry`: in addition to the shared
    `while_loop`-reduction blocker described above, this clause also
    requires a *separate* lemma `binomial(n, n) = RustM.ok 1` — which is
    itself a non-trivial `while_loop` correctness proof on `binomial`'s
    inner loop (showing that `k_pick = 0`, hence `steps = 0`, hence the
    loop returns `r = 1`). -/
theorem multinomial_singleton
    (k : RustSlice u64) (n : u64) (h : k.val = #[n]) :
    multinomial_u64.multinomial k = RustM.ok 1 := by
  sorry

/-- Postcondition (functional correctness on small inputs):
    when the sum of the entries is at most 20 — the largest sum for which
    the factorial-based reference fits in `u64` — `multinomial` agrees with
    the mathematical multinomial coefficient `(∑ kᵢ)! / ∏ (kᵢ!)`.

    Technical reason this is left as `sorry`: full functional correctness
    needs three nested `while_loop` invariants (the outer multinomial
    loop, the inner `binomial` loop, and the inner `gcd` loop inside
    `multiply_and_divide`) *and* the cross-function-call accounting
    (`multinomial`'s body consumes a postcondition for `binomial`,
    which itself consumes one for `multiply_and_divide`, which itself
    consumes one for `gcd`). The selector flagged "Multi-function call
    chains — every example is a single function … none demonstrates how a
    postcondition for one function is consumed inside another's proof"
    as a top-level gap. Establishing the chain from scratch is well
    beyond the scope of a single proof-stage attempt. -/
theorem multinomial_value
    (k : RustSlice u64)
    (h : (k.val.toList.map UInt64.toNat).foldr (· + ·) 0 ≤ 20) :
    multinomial_u64.multinomial k =
      RustM.ok (UInt64.ofNat (multinomialNat (k.val.toList.map UInt64.toNat))) := by
  sorry

/-- Postcondition (symmetry): `multinomial` does not depend on the order of
    its argument — if `k₁` and `k₂` are permutations of one another, they
    produce the same result. The Rust test exercises this via cyclic
    rotations, full reversal, and a swap of the first two entries; all of
    those facts follow from this single permutation-invariance clause.

    Technical reason this is left as `sorry`: the implementation iterates
    left-to-right with running state (`r`, `p`), so symmetry is *not*
    visibly true from the code — the proof has to first establish
    functional correctness against an order-independent mathematical
    reference (essentially `multinomial_value` extended past the
    sum-≤-20 regime, since the symmetry test exercises sums above that
    bound) and *then* invoke the order-independence of that reference.
    The selector flagged "Permutation/symmetry-style postconditions … no
    example proves an order-independence property" as a gap. -/
theorem multinomial_perm_invariant
    (k₁ k₂ : RustSlice u64)
    (h : ListPerm k₁.val.toList k₂.val.toList) :
    multinomial_u64.multinomial k₁ = multinomial_u64.multinomial k₂ := by
  sorry

/-- Failure condition: when the running sum `p = p + i` overflows during
    the iteration, the function panics with `Error.integerOverflow`. The
    Rust test exhibits this with `k = [u64::MAX, 1]`: the first iteration
    sets `p = u64::MAX` and `r = binomial(u64::MAX, u64::MAX) = 1`; the
    second iteration's unchecked `p + 1` overflows.

    Technical reason this is left as `sorry`: the proof needs to drive
    the outer `while_loop` through *exactly two* iterations and then
    show that `p +? i` on the second iteration's `p = u64::MAX, i = 1`
    pair returns `RustM.fail .integerOverflow`. The first iteration also
    requires showing `binomial(u64::MAX, u64::MAX) = RustM.ok 1`, which
    is the same auxiliary lemma needed by `multinomial_singleton`.
    Both pieces hit the shared `while_loop`-reduction blocker described
    above. -/
theorem multinomial_sum_overflow_panics
    (k : RustSlice u64)
    (h : k.val = #[UInt64.ofNat (2 ^ 64 - 1), 1]) :
    multinomial_u64.multinomial k = RustM.fail .integerOverflow := by
  sorry

end Multinomial_u64Obligations
