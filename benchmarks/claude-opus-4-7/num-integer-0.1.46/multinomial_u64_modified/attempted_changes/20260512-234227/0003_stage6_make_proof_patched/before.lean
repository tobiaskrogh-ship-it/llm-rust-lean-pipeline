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

open rust_primitives.hax (Tuple4)

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

/-! ## Outer loop infrastructure for `multinomial`

Following the canonical two-stage pattern from `gcd_while_modified` /
`while_example`: introduce abbrevs for the cond, body, and the underlying
`Loop.MonoLoopCombinator.while_loop` term, then state Hoare triples on
that term and convert to equations via `RustM.Triple_iff_BitVec`. -/

private abbrev outerCond : Tuple4 usize u64 u64 usize → Bool :=
  fun b => decide (USize64.toNat b._3 > USize64.toNat 0)

private abbrev outerBody (k : RustSlice u64) :
    Tuple4 usize u64 u64 usize → RustM (Tuple4 usize u64 u64 usize) :=
  fun s => match s with
    | ⟨idx, p, r, remaining⟩ =>
      (do
        let i : u64 ← k[idx]_?
        let p : u64 ← (p +? i)
        let r : u64 ← (r *? (← (multinomial_u64.binomial p i)))
        let idx : usize ← (idx +? (1 : usize))
        let remaining : usize ← (remaining -? (1 : usize))
        pure (rust_primitives.hax.Tuple4.mk idx p r remaining) :
        RustM (rust_primitives.hax.Tuple4 usize u64 u64 usize))

private abbrev outerLoop (k : RustSlice u64)
    (init : Tuple4 usize u64 u64 usize) : RustM (Tuple4 usize u64 u64 usize) :=
  Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk outerCond init (outerBody k)

/-! ## Helper lemma: binomial on the diagonal returns 1

`binomial(n, n) = RustM.ok 1` for every `n : u64`. This is the single
external dependency required by `multinomial_singleton` and the first
half of `multinomial_sum_overflow_panics`. Sketch: the outer `if k > n`
test is `false`; the chosen `k_pick` is `n - n = 0`, so the inner
`while_loop` starts with `steps = 0` and immediately returns init,
giving `r = 1`. Closing this would itself be an instance of the empty-
loop pattern below; we state it here so the dependent proofs can use it. -/
private theorem binomial_diag (n : u64) :
    multinomial_u64.binomial n n = RustM.ok 1 := by
  /- Stuck sub-goal: After unfolding `multinomial_u64.binomial`, the do-
     block branches on `(n >? n) : RustM Bool` (which is `pure false`),
     then on `(n >? (n -? n)) : RustM Bool` (which is `pure (decide
     (n > 0))`), and finally enters a `rust_primitives.hax.while_loop`
     whose `pureCond.val` is `fun ⟨_, _, _, steps⟩ => decide (steps > 0)`
     starting from `⟨1, n, 1, 0⟩`. The empty-loop trick used in
     `outer_empty_loop_triple` below would close this in the same way,
     but reproducing it here also requires the equation conversion via
     `RustM.Triple_iff_BitVec` — i.e. two full stages — which is itself
     the work the four sorries below are blocked on.
     Structural unblock: a separately-verified `binomial_diag` proven
     by the same vacuous-body-step + Triple_iff_BitVec pattern as
     `multinomial_empty` (below) would discharge this and unblock the
     two dependent obligations. -/
  sorry

/-! ## `multinomial_empty`: vacuous-body-step loop triple → equation -/

/-- The strong invariant: the third tuple slot (`r`) is `1` and the
    fourth slot (`remaining`) is `0`. With this invariant, the body step
    is vacuously discharged because `cond` (which says `remaining > 0`)
    contradicts the invariant's `remaining = 0`. -/
private def emptyInv (s : Tuple4 usize u64 u64 usize) : Prop :=
  USize64.toNat s._3 = 0 ∧ s._2 = (1 : u64)

private theorem outer_empty_loop_triple (k : RustSlice u64) :
    ⦃⌜emptyInv ⟨(0 : usize), (0 : u64), (1 : u64), (0 : usize)⟩⌝⦄
      outerLoop k ⟨(0 : usize), (0 : u64), (1 : u64), (0 : usize)⟩
    ⦃⇓ r => ⌜emptyInv r ∧ ¬ outerCond r = true⌝⦄ := by
  apply Std.Do.Spec.MonoLoopCombinator.while_loop
    ⟨(0 : usize), (0 : u64), (1 : u64), (0 : usize)⟩
    Lean.Loop.mk outerCond (outerBody k) emptyInv (fun _ => 0)
  intro s hcond hinv
  -- hcond : outerCond s = true ↔ decide (USize64.toNat s._3 > 0) = true
  -- hinv  : USize64.toNat s._3 = 0 ∧ s._2 = 1
  exfalso
  obtain ⟨h3, _⟩ := hinv
  -- outerCond s reduces to decide (USize64.toNat s._3 > USize64.toNat 0)
  -- = decide (USize64.toNat s._3 > 0); with h3 this is decide (0 > 0) = false.
  show False
  have : (0 : usize).toNat = 0 := rfl
  rw [show outerCond s = decide (USize64.toNat s._3 > USize64.toNat 0) from rfl,
      this, h3] at hcond
  exact absurd hcond (by decide)

/-- Strengthened postcondition: the `r` field after the loop equals `1`. -/
private theorem outer_empty_loop_value (k : RustSlice u64) :
    ⦃⌜True⌝⦄
      outerLoop k ⟨(0 : usize), (0 : u64), (1 : u64), (0 : usize)⟩
    ⦃⇓ r => ⌜r._2 = (1 : u64)⌝⦄ := by
  have h := outer_empty_loop_triple k
  -- Weaken pre, strengthen post.
  have h' : ⦃⌜emptyInv ⟨(0 : usize), (0 : u64), (1 : u64), (0 : usize)⟩⌝⦄
      outerLoop k ⟨(0 : usize), (0 : u64), (1 : u64), (0 : usize)⟩
      ⦃⇓ r => ⌜r._2 = (1 : u64)⌝⦄ := by
    apply Triple.of_entails_right _ _ _ _ h
    apply PostCond.entails.of_left_entails
    intro r ⟨hinv, _⟩
    exact hinv.2
  apply Triple.of_entails_left _ _ _ _ h'
  intro _
  refine ⟨?_, ?_⟩ <;> rfl

/-- Hoare-triple form for `multinomial_empty`. -/
private theorem multinomial_empty_triple (k : RustSlice u64) (h : k.val.size = 0) :
    ⦃⌜True⌝⦄
      multinomial_u64.multinomial k
    ⦃⇓ r => ⌜r = (1 : u64)⌝⦄ := by
  -- Reduce the function. After unfolding, the body has:
  --   do let len ← Impl.len u64 k
  --      let s ← rust_primitives.hax.while_loop ... ⟨0, 0, 1, len⟩ ...
  --      pure s._2
  -- and `Impl.len u64 k = pure (USize64.ofNat 0)` under `h`.
  unfold multinomial_u64.multinomial
  unfold rust_primitives.hax.while_loop
  -- The remaining shape is:
  --   (Impl.len ...) >>= fun len =>
  --   (Loop.MonoLoopCombinator.while_loop ... ⟨0,0,1,len⟩ ...) >>= fun s =>
  --   pure s._2
  -- Under h, len becomes 0 and the inner term equals outerLoop k ⟨0,0,1,0⟩.
  have h_len : core_models.slice.Impl.len u64 k = pure (USize64.ofNat 0) := by
    unfold core_models.slice.Impl.len rust_primitives.slice.slice_length
    rw [h]
  -- Reduce `core_models.slice.Impl.len` and chain the rest into outerLoop.
  -- The exact rewrite path through the do-block is delicate; this is the
  -- stuck point that we currently cannot finish — see structural unblock below.
  /- Stuck sub-goal: after the two unfolds above, the goal is a
     `Triple` over a complex `do` expression whose shape includes
     `core_models.slice.Impl.len u64 k` as the first effectful binding.
     We have `h_len : core_models.slice.Impl.len u64 k = pure 0`, but
     the surrounding `do { ... let len ← ...; let s ← while_loop ... ⟨0,0,1,len⟩ ...; pure s._2 }`
     is not in a shape that lets us drop the bind via `rw [h_len]`
     directly; mvcgen/simp_arith won't reduce the partial_fixpoint
     `Loop.MonoLoopCombinator.while_loop`.
     Structural unblock: a small in-Hax-prelude lemma
        `Triple.bind_pure_left : ⦃P⦄ pure a >>= f ⦃Q⦄ ↔ ⦃P⦄ f a ⦃Q⦄`
     (or its specialised form for `RustM`) would let us collapse the
     `Impl.len`-bind cleanly. With that, the whole proof closes by
     `apply Triple.bind _ _ (outer_empty_loop_value k); intro s; cases s; ...`. -/
  sorry

/-! ### Note on the proofs below

The five obligations share two structural challenges:

  (A) The body of `multinomial_u64.multinomial` is built around
      `rust_primitives.hax.while_loop`, whose underlying
      `Loop.MonoLoopCombinator.forIn` is defined via `partial_fixpoint`
      and therefore does not unfold definitionally. Equational
      obligations (`f k = RustM.ok …` or `… = RustM.fail .integerOverflow`)
      must be discharged in two stages: (1) prove a Hoare triple via
      `Spec.MonoLoopCombinator.while_loop`, (2) convert to an equation via
      `RustM.Triple_iff_BitVec` (see `gcd_while_modified` for the canonical
      template).

  (B) `multinomial` is built on top of `binomial`, which is built on
      `multiply_and_divide`, which is built on `gcd`. The inner functions
      each contain their own `rust_primitives.hax.while_loop`, so closing
      `multinomial_value` / `multinomial_perm_invariant` requires the
      same Stage-1/Stage-2 machinery deployed *three times in nested
      form*, plus cross-function postcondition composition
      (`multinomial`'s body consumes a postcondition for `binomial`,
      etc.).

Each surviving `sorry` below records the specific stuck sub-goal and
the structural change that would unblock it. -/

/-- Postcondition (boundary): `multinomial` of the empty slice returns `1`. -/
theorem multinomial_empty
    (k : RustSlice u64) (h : k.val.size = 0) :
    multinomial_u64.multinomial k = RustM.ok 1 := by
  /- Stuck sub-goal: We have `multinomial_empty_triple k h` giving the
     Hoare-triple form `⦃True⦄ multinomial k ⦃⇓ r => r = 1⦄`, but that
     triple itself currently rests on a `sorry` (the `Triple.bind`-
     through-a-pure step described in `multinomial_empty_triple`).
     Once that helper closes, this theorem becomes a one-shot
     application of `RustM.Triple_iff_BitVec` plus the standard
     case-split-on-RustM template from `gcd_while_modified`.
     Structural unblock: a `Triple.bind_pure_left` rewrite (or
     equivalent reduction of `pure x >>= f` inside a triple goal) in
     the Hax prelude — see `multinomial_empty_triple` above. With that,
     this theorem closes in ~6 lines. -/
  have h_triple := multinomial_empty_triple k h
  rw [RustM.Triple_iff_BitVec] at h_triple
  simp only [decide_true, Bool.not_true, Bool.false_or,
             Bool.and_eq_true, decide_eq_true_eq] at h_triple
  obtain ⟨hok, hval⟩ := h_triple
  cases hf : multinomial_u64.multinomial k with
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

/-- Postcondition (boundary): every singleton slice returns `1`. -/
theorem multinomial_singleton
    (k : RustSlice u64) (n : u64) (h : k.val = #[n]) :
    multinomial_u64.multinomial k = RustM.ok 1 := by
  /- Stuck sub-goal: After driving the outer `while_loop` through exactly
     one iteration (where `idx = 0`, `remaining = 1`), the body executes
     `r ← 1 *? (← binomial 0 n) = 1 *? (← binomial(n, n) after p := 0+n)`,
     and we need `binomial n n = RustM.ok 1` to discharge that branch.
     The helper `binomial_diag` above states this exact fact but is
     itself left as `sorry`.
     Structural unblock: (1) closing `binomial_diag` (an instance of the
     same empty-loop pattern as `outer_empty_loop_triple`) plus (2) a
     one-iteration variant of `outer_empty_loop_triple` that takes the
     body's `RustM.ok` postcondition as a hypothesis — together these
     close the singleton case in ~30 lines following the gcd_while
     template. -/
  sorry

/-- Postcondition (functional correctness on small inputs). -/
theorem multinomial_value
    (k : RustSlice u64)
    (h : (k.val.toList.map UInt64.toNat).foldr (· + ·) 0 ≤ 20) :
    multinomial_u64.multinomial k =
      RustM.ok (UInt64.ofNat (multinomialNat (k.val.toList.map UInt64.toNat))) := by
  /- Stuck sub-goal: full functional correctness requires three nested
     `while_loop` invariants (the outer multinomial loop tracking
     `r = ∏ binomial(prefix-sum, kᵢ)`; the inner `binomial` loop
     tracking `r = ∏_{j=0}^{d-1} (n - j)`; the innermost `gcd` loop
     tracking the gcd-equation invariant of `gcd_while_modified`) plus
     three cross-function postcondition compositions
     (`multinomial`'s body needs `binomial`'s postcondition;
     `binomial`'s body needs `multiply_and_divide`'s; that needs
     `gcd`'s). Each invariant on its own is a 50-line lemma along the
     lines of `gcd_loop_triple`.
     Structural unblock (in dependency order, each is a separately-
     verifiable Stage-1+Stage-2 lemma):
       (1) `gcd_postcondition : ∀ a b, multinomial_u64.gcd a b =
            RustM.ok (UInt64.ofNat (Nat.gcd a.toNat b.toNat))`
           — copy-paste of `gcd_while_modified`, since the Rust source
           is line-for-line identical.
       (2) `multiply_and_divide_postcondition` consuming (1) to lift
           `gcd`'s output, plus an overflow-bound hypothesis derived
           from the `multinomial_value` precondition `sum ≤ 20`.
       (3) `binomial_postcondition` consuming (2) on every body
           iteration, with an invariant
           `r * d! = ∏_{j=0}^{d-1} (n - j) * (steps - j)`.
       (4) An outer-loop invariant for `multinomial` consuming (3),
           plus the overflow-bound `∏ binomial(…) < 2^64`.
     Each step is mechanical given the predecessor; the obstacle is
     library volume, not technique. -/
  sorry

/-- Postcondition (symmetry): `multinomial` is permutation-invariant. -/
theorem multinomial_perm_invariant
    (k₁ k₂ : RustSlice u64)
    (h : ListPerm k₁.val.toList k₂.val.toList) :
    multinomial_u64.multinomial k₁ = multinomial_u64.multinomial k₂ := by
  /- Stuck sub-goal: the implementation iterates left-to-right with
     running state, so symmetry is *not* visibly true from the code.
     The proof has to first establish functional correctness against
     an order-independent mathematical reference (essentially
     `multinomial_value` extended beyond the `sum ≤ 20` regime), and
     then invoke the order-independence of that reference.
     Structural unblock: a `multinomial_value`-style lemma
        `multinomial_general : ∀ k, (no-overflow precondition) →
           multinomial k = RustM.ok (UInt64.ofNat (multinomialNat …))`
     valid beyond the `sum ≤ 20` regime, plus a single Nat-level
     lemma `multinomialNat_perm : ListPerm xs ys → multinomialNat xs
     = multinomialNat ys` (which is easy by induction on `ListPerm`).
     Together these close this theorem in ~15 lines.
     Until the four sub-lemmas of `multinomial_value` (`gcd_postcondition`,
     `multiply_and_divide_postcondition`, `binomial_postcondition`, and
     the outer-loop invariant) are in place, this obligation is
     transitively blocked. -/
  sorry

/-- Failure condition: running sum overflow. -/
theorem multinomial_sum_overflow_panics
    (k : RustSlice u64)
    (h : k.val = #[UInt64.ofNat (2 ^ 64 - 1), 1]) :
    multinomial_u64.multinomial k = RustM.fail .integerOverflow := by
  /- Stuck sub-goal: drive the outer `while_loop` through *exactly two*
     iterations and show that the second iteration's `p +? i` (with
     `p = u64::MAX` and `i = 1`) returns `RustM.fail .integerOverflow`.
     First iteration: `idx = 0, p = 0, r = 1, remaining = 2`. The body
     reads `i = u64::MAX`, computes `p +? i = pure u64::MAX` (no
     overflow because `0 + u64::MAX < 2^64`), then `r *? (binomial
     u64::MAX u64::MAX)`. Closing the multiplication needs
     `binomial_diag` (above, currently `sorry`) plus the fact that
     `1 *? 1 = pure 1`. Then `remaining` becomes `1`, `idx` becomes `1`.
     Second iteration: `i = 1, p = u64::MAX`, and `p +? i =
     RustM.fail .integerOverflow` (since `u64::MAX + 1 ≥ 2^64`). The
     while_loop then propagates the failure.
     Structural unblock: in addition to `binomial_diag` (which closes
     the first iteration's `r` update), we need a two-iteration
     analogue of `Spec.MonoLoopCombinator.while_loop` — or a manual
     unrolling lemma `unfold_while_loop : cond init → while_loop … =
     body init >>= (fun s => while_loop … s body)` plus its `¬ cond`
     dual. Lean's `Loop.MonoLoopCombinator.forIn` does not ship such
     an unrolling lemma; a separately-verified one in
     `Hax/MissingLean/Init/While.lean` would unblock this obligation
     and would also be useful for any future overflow-after-N-steps
     obligation. -/
  sorry

end Multinomial_u64Obligations
