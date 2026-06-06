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

/-- Postcondition (boundary): `multinomial` of the empty slice returns `1`
    (the empty product, anchoring the running `r = 1` initialization). -/
theorem multinomial_empty
    (k : RustSlice u64) (h : k.val.size = 0) :
    multinomial_u64.multinomial k = RustM.ok 1 := by
  unfold multinomial_u64.multinomial
  unfold core_models.slice.Impl.len rust_primitives.slice.slice_length
  simp only [pure_bind]
  -- The loop's initial state has `remaining = USize64.ofNat 0 = 0`, so the cond
  -- evaluates to false on the very first iteration and the loop returns init.
  -- This requires unfolding the while_loop's partial_fixpoint construction.
  -- That construction evaluates `loop init = if cond init then loop (body init)
  -- else pure init`, which is not a definitional reduction in Lean — it
  -- requires either applying `Spec.MonoLoopCombinator.while_loop` (which
  -- yields a Hoare triple, not a structural equality) or proving an
  -- unfolding lemma for the partial_fixpoint definition.  Neither is
  -- available off-the-shelf in the Hax prelude, and the reference examples
  -- (factorial, sum_to_n, saturating_sub, add_one, square) all use plain
  -- recursion rather than `rust_primitives.hax.while_loop`, so there is no
  -- prior pattern to copy here.
  sorry

/-- Postcondition (boundary): every singleton slice returns `1`, regardless
    of the entry's value. The single iteration computes
    `r = 1 * binomial(n, n) = 1`, so `multinomial(&[n]) = 1` for every `n`,
    including the extreme `n = u64::MAX`. -/
theorem multinomial_singleton
    (k : RustSlice u64) (n : u64) (h : k.val = #[n]) :
    multinomial_u64.multinomial k = RustM.ok 1 := by
  sorry

/-- Postcondition (functional correctness on small inputs):
    when the sum of the entries is at most 20 — the largest sum for which
    the factorial-based reference fits in `u64` — `multinomial` agrees with
    the mathematical multinomial coefficient `(∑ kᵢ)! / ∏ (kᵢ!)`. -/
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
    those facts follow from this single permutation-invariance clause. -/
theorem multinomial_perm_invariant
    (k₁ k₂ : RustSlice u64)
    (h : ListPerm k₁.val.toList k₂.val.toList) :
    multinomial_u64.multinomial k₁ = multinomial_u64.multinomial k₂ := by
  sorry

/-- Failure condition: when the running sum `p = p + i` overflows during
    the iteration, the function panics with `Error.integerOverflow`. The
    Rust test exhibits this with `k = [u64::MAX, 1]`: the first iteration
    sets `p = u64::MAX` and `r = binomial(u64::MAX, u64::MAX) = 1`; the
    second iteration's unchecked `p + 1` overflows. -/
theorem multinomial_sum_overflow_panics
    (k : RustSlice u64)
    (h : k.val = #[UInt64.ofNat (2 ^ 64 - 1), 1]) :
    multinomial_u64.multinomial k = RustM.fail .integerOverflow := by
  sorry

end Multinomial_u64Obligations
