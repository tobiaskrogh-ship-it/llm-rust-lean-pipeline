# while_example — canonical proof pattern for `while`-loop targets

Closed-proof demonstration of how to verify a Hax-extracted function whose Rust source uses a `while` loop. If the proof generator selected this example, the target almost certainly needs the same pattern — read this file before attempting tactics, and **read [`proofs/lean/extraction/While_exampleObligations.lean`](proofs/lean/extraction/While_exampleObligations.lean) alongside it**: it is the closed-proof reference, not just an illustration.

## When this pattern applies

The rewrite stage typically leaves the Rust source minimal (no `loop_invariant!`, often no `loop_decreases!` either) and pushes all proof work down to the Lean side. In the extracted Lean you will see `rust_primitives.hax.while_loop` wrapped in a `do`-block.

## The two-stage shape

Equational obligations like `f a b = RustM.ok <expr>` are **not** discharged by direct unfolding of the loop combinator — the partial-fixpoint definition does not reduce past one iteration. The canonical discharge is two stages:

1. **Stage 1 — prove a Hoare-triple form** of the postcondition using `Spec.MonoLoopCombinator.while_loop`.
2. **Stage 2 — convert the triple to the equation** using `RustM.Triple_iff_BitVec` and a case-split on the `RustM` constructors.

`While_exampleObligations.lean` ships both stages: `modulo_via_subtraction_triple` (Stage 1, lines 95–163) and `modulo_via_subtraction_postcondition` (Stage 2, lines 168–189). When you adapt this pattern, write both theorems for your target.

## Stage 1: prove the Hoare-triple form

1. **Unfold the function and `rust_primitives.hax.while_loop`** to expose the underlying `Loop.MonoLoopCombinator.while_loop` term, then `simp only [bind_pure]` to clean up the surrounding do-block (`do { let x := init; let x ← loop; pure x }` reduces to the loop call itself).
2. **State the strong invariant as a Lean `Prop`** over loop state. Function inputs are theorem parameters, so reference them directly — no Rust-side freeze. Define a `loopTerm : β → Nat` measure if termination needs a non-trivial witness.
3. **Apply `Std.Do.Spec.MonoLoopCombinator.while_loop` from `Hax/MissingLean/Std/Do/Triple/SpecLemmas.lean`.** You get a Hoare triple about the loop with the invariant you chose; the conclusion has shape `⦃inv init⦄ loop ⦃⇓ r => inv r ∧ ¬ cond r⦄`. The body-step subgoal is the only manual Nat-level work — discharge it via a `body_step_nat`-style helper lemma asserting (a) no panic, (b) measure decreases, (c) invariant preserved.
4. **Apply consequence rules** (`Triple.of_entails_left` for weakening pre, `Triple.of_entails_right` for strengthening post) plus `PostCond.entails.of_left_entails` to bridge the `inv ∧ ¬ cond` exit shape to your target postcondition.

## Stage 2: convert the triple to the equation

**This stage is required for any obligation written as `f a b = RustM.ok <expr>` or `∃ v, f a b = pure v`. Do not skip it. Do not claim "the prelude has no triple-to-equation conversion" — it does, see below.**

5. **Apply `RustM.Triple_iff_BitVec`** (defined at [`Hax/rust_primitives/BVDecide.lean:81`](proofs/lean/extraction/.lake/packages/Hax/proof-libs/lean/Hax/rust_primitives/BVDecide.lean#L81)). The lemma has shape:

   ```lean
   ⦃ ⌜ a ⌝ ⦄ x ⦃ ⇓ r => ⌜ b r ⌝ ⦄ ↔
     (!decide a || (x.toBVRustM.ok && decide (b x.toBVRustM.val)))
   ```

   Use it as `rw [RustM.Triple_iff_BitVec] at h` on your Stage-1 result, then simplify the boolean to extract `x.toBVRustM.ok` and `decide (b x.toBVRustM.val) = true`.

6. **Case-split on the `RustM` constructors** (`none` / `some .ok v` / `some .error e`) using `cases hf : <fn-call> with`. The `none` and `error` branches are closed by the `ok` fact; the `ok` branch yields `congrArg RustM.ok` of the value equality. The full template is in `modulo_via_subtraction_postcondition`.

## Common failure mode — verify before bailing out

If you find yourself drafting a `sorry`-justification along the lines of *"the prelude does not provide a conversion lemma between Hoare triples and equations"* or *"the loop combinator does not reduce definitionally past one iteration so we cannot continue"* — **stop and re-read this file**. The first claim is false (`RustM.Triple_iff_BitVec` is exactly that lemma; line numbers above). The second claim is true but irrelevant (you do not unfold past one iteration; you reason about the loop via its Hoare-triple spec). Both bailouts indicate that you stopped at Stage 1 and never attempted Stage 2.

If after honestly attempting both stages a sub-goal is intractable, leave it as `sorry` with a justification that names the *specific* sub-goal (e.g. "`body_step_nat` clause (3) requires `Nat.gcd_rec`-style reasoning that exceeds the current invariant"). Do not name missing prelude lemmas without first grepping the prelude.

## Reusable shape (full two-stage)

```lean
-- Stage 1: Hoare triple
theorem <fn>_triple (<args>) (<precond>) :
    ⦃⌜<precond>⌝⦄ <crate>.<fn> <args> ⦃⇓ r => ⌜<postcond> r⌝⦄ := by
  unfold <crate>.<fn>
  unfold rust_primitives.hax.while_loop
  simp only [bind_pure]
  -- (1) build the strong-pre/spec-post triple
  have h_loop : ⦃⌜<strongInv> init⌝⦄ Lean.Loop.MonoLoopCombinator.while_loop _ _ init _
                ⦃⇓ r => ⌜<strongInv> r ∧ ¬ <pureCond> r⌝⦄ := by
    apply Std.Do.Spec.MonoLoopCombinator.while_loop init Lean.Loop.mk _ _ <strongInv> <termMeasure>
    intro x hcond hinv
    -- discharge body using <bodyStepNat>: no-panic, decrease, invariant preserved
    ...
  -- (2) strengthen post
  have h_loop' := Triple.of_entails_right _ _ _ _ h_loop ?postEntail
  case postEntail =>
    apply PostCond.entails.of_left_entails
    intro r h
    -- derive <postcond> r from <strongInv> r ∧ ¬ <pureCond> r
    ...
  -- (3) weaken pre
  apply Triple.of_entails_left _ _ _ _ h_loop'
  intro h
  -- derive <strongInv> init from <precond>
  ...

-- Stage 2: equation
theorem <fn>_postcondition (<args>) (<precond>) :
    <crate>.<fn> <args> = RustM.ok <expr> := by
  have h := <fn>_triple <args> <precond>
  rw [RustM.Triple_iff_BitVec] at h
  rw [show decide <precond> = true from decide_eq_true ‹_›] at h
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hok, hval⟩ := h
  cases hf : <crate>.<fn> <args> with
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
```

Read the spec lemma's signature in the prelude before applying — argument order may have shifted.
