-- Companion obligations file for the `while_count_up` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- The proofs follow the canonical two-stage `while`-loop pattern from
-- `proof_patterns/while_example/README.md`:
--   Stage 1: prove a Hoare triple for the loop via
--            `Std.Do.Spec.MonoLoopCombinator.while_loop`.
--   Stage 2: convert the triple to the equation `f n = RustM.ok n` via
--            `RustM.Triple_iff_BitVec`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import while_count_up

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace While_count_upObligations

/-! ## Loop infrastructure (mirrors `gcd_while_modified`). -/

private def countInv (n i : u64) : Prop := i.toNat ≤ n.toNat

private def countTerm (n : u64) (i : u64) : Nat := n.toNat - i.toNat

private abbrev countCond (n : u64) : u64 → Bool :=
  fun i => decide (UInt64.toNat i < UInt64.toNat n)

private abbrev countBody : u64 → RustM u64 :=
  fun i =>
    (do
      let i : u64 ← (i +? (1 : u64))
      pure i : RustM u64)

private abbrev countLoop (n : u64) : RustM u64 :=
  Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk (countCond n) (0 : u64) countBody

/-! ## Stage 1: Hoare triple for the loop. -/

private theorem count_loop_triple (n : u64) :
    ⦃⌜ countInv n (0 : u64) ⌝⦄
      countLoop n
    ⦃⇓ r => ⌜ countInv n r ∧ ¬ countCond n r = true ⌝⦄ := by
  apply Std.Do.Spec.MonoLoopCombinator.while_loop
    (0 : u64) Lean.Loop.mk (countCond n) countBody (countInv n) (countTerm n)
  intro i hcond hinv
  -- Decode the loop condition and the invariant.
  have hi_lt_n : i.toNat < n.toNat := by
    have h : decide (UInt64.toNat i < UInt64.toNat n) = true := hcond
    exact decide_eq_true_iff.mp h
  -- i + 1 cannot overflow: i < n ≤ 2^64 - 1, so i + 1 ≤ n < 2^64.
  have hn_lt : n.toNat < 2 ^ 64 := UInt64.toNat_lt n
  have h_no_ovf : BitVec.uaddOverflow i.toBitVec ((1 : u64).toBitVec) = false := by
    cases hb : BitVec.uaddOverflow i.toBitVec ((1 : u64).toBitVec) with
    | false => rfl
    | true =>
      exfalso
      have h : UInt64.addOverflow i (1 : u64) = true := hb
      rw [UInt64.addOverflow_iff] at h
      have h1 : (1 : UInt64).toNat = 1 := rfl
      rw [h1] at h
      omega
  -- The body reduces to `pure (i + 1)`.
  have h_add : (i +? (1 : u64) : RustM u64) = pure (i + 1) := by
    show (rust_primitives.ops.arith.Add.add i (1 : u64) : RustM u64) = pure (i + 1)
    show (if BitVec.uaddOverflow i.toBitVec (1 : u64).toBitVec then
            (.fail .integerOverflow : RustM u64)
          else pure (i + 1)) = pure (i + 1)
    rw [h_no_ovf]
    rfl
  -- (i + 1).toNat = i.toNat + 1
  have h_i1 : (i + (1 : u64)).toNat = i.toNat + 1 := by
    apply UInt64.toNat_add_of_lt
    show i.toNat + (1 : UInt64).toNat < 2 ^ 64
    have h1 : (1 : UInt64).toNat = 1 := rfl
    rw [h1]
    omega
  -- Unfold the body abbrev and apply the rewrite.
  dsimp only [countBody]
  rw [h_add]
  simp only [pure_bind]
  refine ⟨?_, ?_⟩
  · -- termination: n - (i + 1) < n - i
    show countTerm n (i + 1) < countTerm n i
    show n.toNat - (i + 1).toNat < n.toNat - i.toNat
    rw [h_i1]; omega
  · -- invariant: (i + 1).toNat ≤ n.toNat
    show countInv n (i + 1)
    show (i + 1).toNat ≤ n.toNat
    rw [h_i1]; omega

/-! ## Stage 2: function-level triple `count_up_while n = n`. -/

private theorem count_function_triple (n : u64) :
    ⦃⌜ True ⌝⦄
      while_count_up.count_up_while n
    ⦃⇓ r => ⌜ r = n ⌝⦄ := by
  have h_loop := count_loop_triple n
  -- Strengthen the postcondition: loopInv r ∧ ¬cond r ⟹ r = n.
  have h_loop' :
      ⦃⌜ countInv n (0 : u64) ⌝⦄
        countLoop n
      ⦃⇓ r => ⌜ r = n ⌝⦄ := by
    apply Triple.of_entails_right _ _ _ _ h_loop
    apply PostCond.entails.of_left_entails
    intro r ⟨hinv, hncond⟩
    -- hncond : ¬ decide (r.toNat < n.toNat) = true → n ≤ r.
    have hr_ge_n : n.toNat ≤ r.toNat := by
      have h : ¬ decide (UInt64.toNat r < UInt64.toNat n) = true := hncond
      rw [decide_eq_true_iff] at h
      omega
    -- Combined with the invariant r ≤ n, we get r = n.
    unfold countInv at hinv
    apply UInt64.toNat_inj.mp
    omega
  -- Weaken the precondition: True ⟹ countInv n 0.
  have h_loop'' :
      ⦃⌜ True ⌝⦄
        countLoop n
      ⦃⇓ r => ⌜ r = n ⌝⦄ := by
    apply Triple.of_entails_left _ _ _ _ h_loop'
    intro _
    show (0 : u64).toNat ≤ n.toNat
    have h0 : (0 : u64).toNat = 0 := rfl
    rw [h0]; omega
  -- Reformulate the function: after unfolding it reduces to `countLoop n >>= pure`,
  -- which is `countLoop n` by `bind_pure`.
  unfold while_count_up.count_up_while
  unfold rust_primitives.hax.while_loop
  show ⦃⌜True⌝⦄ (countLoop n >>= pure) ⦃⇓ r => ⌜r = n⌝⦄
  simp only [bind_pure]
  exact h_loop''

/-! ## Stage 3: equational form via `RustM.Triple_iff_BitVec`. -/

/-- Main postcondition: for every `u64` input `n`, `count_up_while n` returns
    `n`. This single equation captures all three contract-style tests in the
    Rust source:
      * `zero_returns_zero` (n = 0 boundary)
      * `known_values` (n = 1, 5, 100)
      * `returns_n` proptest (n in 0..10_000)

    The statement is universal over all `u64` (not bounded like the proptest):
    each loop iteration computes `i + 1` only when `i < n` holds, so
    `i + 1 ≤ n ≤ 2^64 - 1` and no `u64` add-overflow ever occurs, even at
    `n = u64::MAX`. -/
theorem count_up_while_postcondition (n : u64) :
    while_count_up.count_up_while n = RustM.ok n := by
  have h := count_function_triple n
  rw [RustM.Triple_iff_BitVec] at h
  simp only [decide_true, Bool.not_true, Bool.false_or,
             Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hok, hval⟩ := h
  cases hf : while_count_up.count_up_while n with
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

/-- Boundary clause: `count_up_while 0 = 0` (loop body never executes).
    Captures the `zero_returns_zero` test explicitly. Derived from the
    universal postcondition. -/
theorem count_up_while_zero :
    while_count_up.count_up_while 0 = RustM.ok 0 :=
  count_up_while_postcondition 0

/-- Totality / no-panic: for every `u64` input the function returns a value
    (it never overflows). Derived from the universal postcondition. -/
theorem count_up_while_total (n : u64) :
    ∃ v : u64, while_count_up.count_up_while n = RustM.ok v :=
  ⟨n, count_up_while_postcondition n⟩

end While_count_upObligations
