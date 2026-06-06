-- Obligations for `modulo_via_subtraction`.
--
-- The Rust source (benchmarks/while_example/src/lib.rs) computes `a % b` by
-- repeated subtraction. The natural invariant `x % b == a % b` cannot be
-- expressed at the Rust level (Hax's `pureP/grind` synthesis can't lift
-- partial-op expressions to `Prop`), so we recover it here in Lean using
-- `Spec.MonoLoopCombinator.while_loop` directly.
--
-- The Rust source carries a *weak* `loop_invariant!(b > 0)` (a comparison-
-- only invariant — workable at the Rust level). It propagates the
-- precondition through the loop body and lets the auto-spec at least try
-- (it still fails because `bv_decide` can't see `UInt64.toNat` hypotheses;
-- the auto-spec uses `sorry` via a fallback tactic chain in
-- `while_example.lean`). The *real* spec — the postcondition that the
-- result equals `a % b` — lives below.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import while_example

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace While_exampleObligations

/-- Strong invariant for the loop. Includes `b > 0` so the body step (which
    needs no-underflow) has access to it. `b` doesn't change so this is
    trivially preserved. -/
private def loopInv (a b x : u64) : Prop :=
  b.toNat > 0 ∧ x.toNat ≤ a.toNat ∧ x.toNat % b.toNat = a.toNat % b.toNat

/-- Termination measure: the loop variable `x` (as a Nat) strictly decreases
    each iteration since `b > 0`. -/
private def loopTerm (x : u64) : Nat := x.toNat

/-- Body-step properties as plain Nat-level facts (no Hoare triples involved).
    These are the *content* of the body step; lifting them into a triple is
    mechanical and reusable. -/
private theorem body_step_nat (a b x : u64)
    (hinv : loopInv a b x) (hxb : b.toNat ≤ x.toNat) :
    -- (1) body produces `x - b`, no underflow
    UInt64.subOverflow x b = false ∧
    -- (2) termination strictly decreases
    (x - b).toNat < x.toNat ∧
    -- (3) invariant preserved
    loopInv a b (x - b) := by
  obtain ⟨hb, hxa, hres⟩ := hinv
  refine ⟨?_, ?_, hb, ?_, ?_⟩
  · -- (1) no underflow
    generalize hbo : UInt64.subOverflow x b = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      rw [UInt64.subOverflow_iff] at hbo
      omega
  · -- (2) termination decreases: (x - b).toNat = x.toNat - b.toNat < x.toNat
    rw [UInt64.toNat_sub_of_le' hxb]
    omega
  · -- (3a) (x - b).toNat ≤ a.toNat
    rw [UInt64.toNat_sub_of_le' hxb]
    omega
  · -- (3b) residue invariance: (x - b).toNat % b.toNat = a.toNat % b.toNat
    rw [UInt64.toNat_sub_of_le' hxb]
    have hmod : (x.toNat - b.toNat) % b.toNat = x.toNat % b.toNat := by
      have hxeq : (x.toNat - b.toNat) + b.toNat = x.toNat := by omega
      have := Nat.add_mod_right (x.toNat - b.toNat) b.toNat
      rw [hxeq] at this
      exact this.symm
    rw [hmod]
    exact hres

/-- Hoare-triple form of the postcondition: under `b > 0`, the loop terminates
    with `r = UInt64.ofNat (a.toNat % b.toNat)`.

    Proof structure:
    1. Unfold `modulo_via_subtraction` and `rust_primitives.hax.while_loop`
       to expose the underlying `Loop.MonoLoopCombinator.while_loop`.
    2. Build a Hoare triple over the loop with the strong invariant `loopInv`
       and termination measure `loopTerm` via `Spec.MonoLoopCombinator.while_loop`.
       The body step uses `body_step_nat` (Nat-level facts) lifted through
       a no-underflow rewrite (`x -? b = pure (x - b)`).
    3. Strengthen the postcondition: `loopInv a b r ∧ ¬(r ≥ b)` ⟹
       `r = UInt64.ofNat (a.toNat % b.toNat)` using `Nat.mod_eq_of_lt`.
    4. Weaken the precondition: `b.toNat > 0` ⟹ `loopInv a b a` (trivial).

    This is the canonical pattern for "u64 loop where the natural invariant
    uses partial ops": carry a comparison-only invariant at the Rust level
    (`b > 0`), recover the strong invariant in Lean. -/
theorem modulo_via_subtraction_triple (a b : u64) :
    ⦃⌜ b.toNat > 0 ⌝⦄
      while_example.modulo_via_subtraction a b
    ⦃⇓ r => ⌜ r = UInt64.ofNat (a.toNat % b.toNat) ⌝⦄ := by
  unfold while_example.modulo_via_subtraction
  unfold rust_primitives.hax.while_loop
  simp only [bind_pure]
  -- Build the loop triple from the underlying spec, using our strong invariant.
  have h_loop :
      ⦃⌜loopInv a b a⌝⦄
        Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk
          (fun x => decide (UInt64.toNat x ≥ UInt64.toNat b))
          a
          (fun x => x -? b)
      ⦃⇓ r => ⌜loopInv a b r ∧ ¬ (decide (UInt64.toNat r ≥ UInt64.toNat b) = true)⌝⦄ := by
    apply Std.Do.Spec.MonoLoopCombinator.while_loop a Lean.Loop.mk
      (fun x => decide (UInt64.toNat x ≥ UInt64.toNat b))
      (fun x => x -? b)
      (loopInv a b) loopTerm
    intro x hcond hinv
    have hxb : b.toNat ≤ x.toNat := by
      rw [decide_eq_true_iff] at hcond
      omega
    obtain ⟨h_no_overflow, h_term, h_inv'⟩ := body_step_nat a b x hinv hxb
    -- Reduce `x -? b` to `pure (x - b)` using the no-overflow fact.
    have h_eq : (x -? b : RustM u64) = pure (x - b) := by
      show (rust_primitives.ops.arith.Sub.sub x b : RustM u64) = pure (x - b)
      show (if BitVec.usubOverflow x.toBitVec b.toBitVec then
              (.fail .integerOverflow : RustM u64)
            else pure (x - b)) = pure (x - b)
      rw [show BitVec.usubOverflow x.toBitVec b.toBitVec = false from h_no_overflow]
      rfl
    rw [h_eq]
    -- wp⟦pure (x - b)⟧ Q reduces to Q.fst (x - b), which is the conjunction.
    exact ⟨h_term, h_inv'⟩
  -- Strengthen the postcondition: (loopInv ∧ ¬cond) → (r = UInt64.ofNat (a%b))
  have h_loop' :
      ⦃⌜loopInv a b a⌝⦄
        Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk
          (fun x => decide (UInt64.toNat x ≥ UInt64.toNat b))
          a
          (fun x => x -? b)
      ⦃⇓ r => ⌜r = UInt64.ofNat (UInt64.toNat a % UInt64.toNat b)⌝⦄ := by
    apply Triple.of_entails_right _ _ _ _ h_loop
    apply PostCond.entails.of_left_entails
    intro r h
    obtain ⟨⟨hb, hra, hres⟩, hncond⟩ := h
    have hrlt : r.toNat < b.toNat := by
      rw [decide_eq_true_iff] at hncond
      omega
    -- r.toNat < b → r.toNat % b = r.toNat → r.toNat = a.toNat % b.toNat
    have heq_nat : r.toNat = a.toNat % b.toNat := by
      rw [← Nat.mod_eq_of_lt hrlt, hres]
    -- Lift to UInt64 equality
    apply UInt64.toNat_inj.mp
    rw [heq_nat]
    -- Now: a.toNat % b.toNat = (UInt64.ofNat (a.toNat % b.toNat)).toNat
    have hb_lt : b.toNat ≤ 2^64 := by
      have := UInt64.toNat_lt b
      omega
    have h_amod_lt : a.toNat % b.toNat < 2^64 := by
      have := Nat.mod_lt a.toNat (by omega : 0 < b.toNat)
      omega
    rw [UInt64.toNat_ofNat']
    omega
  -- Weaken the precondition: (b > 0) → loopInv a b a
  apply Triple.of_entails_left _ _ _ _ h_loop'
  intro h
  exact ⟨h, Nat.le_refl _, rfl⟩

/-- Equational form. Follows from the Hoare triple by case-analysis on the
    `RustM` result, in the standard pattern used elsewhere in the library
    (e.g. `average_floor_unfold`). -/
theorem modulo_via_subtraction_postcondition (a b : u64) (hb : b.toNat > 0) :
    while_example.modulo_via_subtraction a b
      = RustM.ok (UInt64.ofNat (a.toNat % b.toNat)) := by
  have h := modulo_via_subtraction_triple a b
  rw [RustM.Triple_iff_BitVec] at h
  rw [show decide (b.toNat > 0) = true from decide_eq_true hb] at h
  simp only [Bool.not_true, Bool.false_or,
             Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hok, hval⟩ := h
  cases hf : while_example.modulo_via_subtraction a b with
  | none =>
    rw [hf] at hok
    simp [RustM.toBVRustM] at hok
  | some result =>
    cases result with
    | ok v =>
      rw [hf] at hval
      simp [RustM.toBVRustM] at hval
      exact congrArg RustM.ok hval
    | error e =>
      rw [hf] at hok
      cases e <;> simp [RustM.toBVRustM] at hok

end While_exampleObligations
