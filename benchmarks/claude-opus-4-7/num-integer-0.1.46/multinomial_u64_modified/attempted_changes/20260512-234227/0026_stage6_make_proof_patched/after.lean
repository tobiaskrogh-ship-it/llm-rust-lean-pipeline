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

/-! ## Helper: the binomial inner while_loop, abbrevs

We mirror the outer-loop abbrevs for `binomial`'s inner `while_loop` so
that `binomial_diag` (binomial(n, n) = ok 1) can re-use the
vacuous-body-step pattern of `outer_empty_loop_triple`. The state is
`Tuple4 u64 u64 u64 u64` with components `⟨d, n_var, r, steps⟩` (so
`_2 = r` and `_3 = steps`). -/

private abbrev binomialCond : Tuple4 u64 u64 u64 u64 → Bool :=
  fun b => decide (UInt64.toNat b._3 > UInt64.toNat 0)

private abbrev binomialBody :
    Tuple4 u64 u64 u64 u64 → RustM (Tuple4 u64 u64 u64 u64) :=
  fun x =>
    (do
      let r : u64 ← (multinomial_u64.multiply_and_divide x._2 x._1 x._0)
      let n_var : u64 ← (x._1 -? (1 : u64))
      let d : u64 ← (x._0 +? (1 : u64))
      let steps : u64 ← (x._3 -? (1 : u64))
      pure (rust_primitives.hax.Tuple4.mk d n_var r steps) :
      RustM (rust_primitives.hax.Tuple4 u64 u64 u64 u64))

private abbrev binomialLoop (init : Tuple4 u64 u64 u64 u64) :
    RustM (Tuple4 u64 u64 u64 u64) :=
  Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk binomialCond init binomialBody

private def binomialEmptyInv (s : Tuple4 u64 u64 u64 u64) : Prop :=
  UInt64.toNat s._3 = 0 ∧ s._2 = (1 : u64)

private theorem binomial_empty_loop_triple (n : u64) :
    ⦃⌜binomialEmptyInv ⟨(1 : u64), n, (1 : u64), (0 : u64)⟩⌝⦄
      binomialLoop ⟨(1 : u64), n, (1 : u64), (0 : u64)⟩
    ⦃⇓ r => ⌜binomialEmptyInv r ∧ ¬ binomialCond r = true⌝⦄ := by
  apply Std.Do.Spec.MonoLoopCombinator.while_loop
    ⟨(1 : u64), n, (1 : u64), (0 : u64)⟩
    Lean.Loop.mk binomialCond binomialBody binomialEmptyInv (fun _ => 0)
  intro s hcond hinv
  exfalso
  obtain ⟨h3, _⟩ := hinv
  have : (0 : u64).toNat = 0 := rfl
  rw [show binomialCond s = decide (UInt64.toNat s._3 > UInt64.toNat 0) from rfl,
      this, h3] at hcond
  exact absurd hcond (by decide)

private theorem binomial_empty_loop_value (n : u64) :
    ⦃⌜True⌝⦄
      binomialLoop ⟨(1 : u64), n, (1 : u64), (0 : u64)⟩
    ⦃⇓ r => ⌜r._2 = (1 : u64)⌝⦄ := by
  have h := binomial_empty_loop_triple n
  have h' :
      ⦃⌜binomialEmptyInv ⟨(1 : u64), n, (1 : u64), (0 : u64)⟩⌝⦄
        binomialLoop ⟨(1 : u64), n, (1 : u64), (0 : u64)⟩
      ⦃⇓ r => ⌜r._2 = (1 : u64)⌝⦄ := by
    apply Triple.of_entails_right _ _ _ _ h
    apply PostCond.entails.of_left_entails
    intro r ⟨hinv, _⟩
    exact hinv.2
  apply Triple.of_entails_left _ _ _ _ h'
  intro _
  refine ⟨?_, ?_⟩ <;> rfl

/-! ## Helper lemma: binomial on the diagonal returns 1 -/

/-- Helper: `n -? n = pure 0` for any `n : u64`. -/
private theorem u64_sub_self (n : u64) : (n -? n : RustM u64) = pure (0 : u64) := by
  show (rust_primitives.ops.arith.Sub.sub n n : RustM u64) = pure 0
  show (if BitVec.usubOverflow n.toBitVec n.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (n - n)) = pure 0
  have h_no_overflow : BitVec.usubOverflow n.toBitVec n.toBitVec = false := by
    simp [BitVec.usubOverflow]
  rw [h_no_overflow]
  have h_nn : n - n = (0 : u64) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le' (Nat.le_refl n.toNat)]
    simp
  rw [h_nn]
  rfl

/-- Helper: `n >? n = pure false` for any `n : u64`. -/
private theorem u64_gt_self (n : u64) : (n >? n : RustM Bool) = pure false := by
  show rust_primitives.cmp.gt n n = pure false
  show pure (decide (n > n)) = pure false
  simp

/-- `binomial(n, n) = RustM.ok 1` for every `n : u64`. The proof goes via
    a Hoare triple, using `binomial_empty_loop_value` for the inner loop.

    Outline:
      1. Build the triple `⦃True⦄ binomial n n ⦃⇓ r => r = 1⦄`.
      2. Convert to an equation via `RustM.Triple_iff_BitVec`. -/
private theorem binomial_diag_triple (n : u64) :
    ⦃⌜True⌝⦄ multinomial_u64.binomial n n ⦃⇓ r => ⌜r = (1 : u64)⌝⦄ := by
  unfold multinomial_u64.binomial
  -- After unfolding, the outer test (k >? n) becomes (n >? n) = pure false.
  rw [u64_gt_self n]
  simp only [pure_bind, Bool.false_eq_true, ↓reduceIte]
  -- Now: ⦃True⦄ do { let k_pick ← (do let v ← n -? n; let c ← n >? v; if c then n -? n else pure n); ...; while_loop ... } ⦃r = 1⦄
  -- Reduce (n -? n) = pure 0 (appears twice in the inner if-then-else)
  rw [u64_sub_self n]
  simp only [pure_bind]
  -- Now: ⦃True⦄ do { let k_pick ← (do let c ← n >? 0; if c then pure 0 else pure n); ...; while_loop ... } ⦃r = 1⦄
  -- Reduce (n >? 0) = pure (decide (n.toNat > 0))
  have h_gt_zero : (n >? (0 : u64) : RustM Bool) = pure (decide (n.toNat > 0)) := by
    show pure (decide (n > (0 : u64))) = pure (decide (n.toNat > 0))
    apply congrArg pure
    apply decide_eq_decide.mpr
    show (0 : u64) < n ↔ 0 < n.toNat
    rw [UInt64.lt_iff_toNat_lt]
    rfl
  rw [h_gt_zero]
  simp only [pure_bind]
  -- Now we have: ⦃True⦄ (if decide (n.toNat > 0) then pure 0 else pure n) >>= fun k_pick => ... while_loop ⟨1, n, 1, k_pick⟩ ... ⦃r = 1⦄
  -- Case split on whether n > 0
  by_cases hn : n.toNat > 0
  · -- n > 0 case: k_pick = 0
    rw [show decide (n.toNat > 0) = true from decide_eq_true hn]
    simp only [↓reduceIte]
    -- Goal: ⦃True⦄ (while_loop ... ⟨1, n, 1, 0⟩ ...) >>= fun s => pure s._2 ⦃r = 1⦄
    -- This is exactly binomial_empty_loop_value bound to pure.
    show ⦃⌜True⌝⦄
        (binomialLoop ⟨(1 : u64), n, (1 : u64), (0 : u64)⟩ >>=
          fun s => match s with | ⟨_, _, r, _⟩ => pure r)
        ⦃⇓ r => ⌜r = (1 : u64)⌝⦄
    apply Triple.bind _ _ (binomial_empty_loop_value n)
    intro s
    cases s with
    | mk d n_var r steps =>
      refine Triple.pure r ?_
      intro hr; exact hr
  · -- n = 0 case: k_pick = n, but n = 0
    have hn_eq : n.toNat = 0 := by omega
    have hn0 : n = 0 := by
      apply UInt64.toNat_inj.mp; rw [hn_eq]; rfl
    rw [show decide (n.toNat > 0) = false from decide_eq_false hn]
    simp only [Bool.false_eq_true, ↓reduceIte]
    -- After Bool.false_eq_true + ↓reduceIte the if collapses. Now substitute n = 0.
    rw [hn0]
    show ⦃⌜True⌝⦄
        (binomialLoop ⟨(1 : u64), (0 : u64), (1 : u64), (0 : u64)⟩ >>=
          fun s => match s with | ⟨_, _, r, _⟩ => pure r)
        ⦃⇓ r => ⌜r = (1 : u64)⌝⦄
    apply Triple.bind _ _ (binomial_empty_loop_value 0)
    intro s
    cases s with
    | mk d n_var r steps =>
      refine Triple.pure r ?_
      intro hr; exact hr

private theorem binomial_diag (n : u64) :
    multinomial_u64.binomial n n = RustM.ok 1 := by
  have h := binomial_diag_triple n
  rw [RustM.Triple_iff_BitVec] at h
  simp only [decide_true, Bool.not_true, Bool.false_or,
             Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hok, hval⟩ := h
  cases hf : multinomial_u64.binomial n n with
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

/-- Hoare-triple form for `multinomial_empty`. The proof reduces
    `core_models.slice.Impl.len u64 k` to `pure 0` using the empty-slice
    hypothesis, then uses `Triple.bind` twice: once to step through the
    `Impl.len` call, and once to step through the outer `while_loop`
    via `outer_empty_loop_value`. -/
private theorem multinomial_empty_triple (k : RustSlice u64) (h : k.val.size = 0) :
    ⦃⌜True⌝⦄
      multinomial_u64.multinomial k
    ⦃⇓ r => ⌜r = (1 : u64)⌝⦄ := by
  have h_len : core_models.slice.Impl.len u64 k = pure (0 : usize) := by
    unfold core_models.slice.Impl.len rust_primitives.slice.slice_length
    rw [h]
    rfl
  unfold multinomial_u64.multinomial
  unfold rust_primitives.hax.while_loop
  rw [h_len]
  -- Goal is now: ⦃True⦄ (pure 0 >>= fun len => ... outerLoop k ⟨0,0,1,len⟩ ... ) ⦃r = 1⦄
  -- which should reduce via pure_bind to ⦃True⦄ (outerLoop k ⟨0,0,1,0⟩ >>= ...) ⦃r = 1⦄
  show ⦃⌜True⌝⦄
      (outerLoop k ⟨(0 : usize), (0 : u64), (1 : u64), (0 : usize)⟩ >>=
        fun s => match s with | ⟨_, _, r, _⟩ => pure r)
      ⦃⇓ r => ⌜r = (1 : u64)⌝⦄
  apply Triple.bind _ _ (outer_empty_loop_value k)
  intro s
  cases s with
  | mk idx p r remaining =>
    refine Triple.pure r ?_
    intro hr
    exact hr

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

/-- Postcondition (boundary): `multinomial` of the empty slice returns `1`
    (the empty product, anchoring the running `r = 1` initialization).

    Closed by the canonical Stage-1/Stage-2 pattern from
    `gcd_while_modified`/`while_example`:
      Stage 1 — `multinomial_empty_triple` builds the Hoare triple
        `⦃True⦄ multinomial k ⦃⇓ r => r = 1⦄`. It uses
        `core_models.slice.Impl.len u64 k = pure 0` (from `h`), reduces
        the do-block via `pure_bind`/`rw`, and discharges the outer
        `while_loop` with `outer_empty_loop_value` whose body step is
        vacuously discharged (`emptyInv` carries `remaining = 0`, so
        `cond` — `remaining > 0` — contradicts `emptyInv`).
      Stage 2 — convert the triple to the equation via
        `RustM.Triple_iff_BitVec` and the standard `cases hf : multinomial k`
        template. -/
theorem multinomial_empty
    (k : RustSlice u64) (h : k.val.size = 0) :
    multinomial_u64.multinomial k = RustM.ok 1 := by
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

/-! ## Singleton case infrastructure

The outer loop runs through exactly one iteration. We use a two-point
invariant `s = init ∨ s = afterOne` and let the body step compute
deterministically. -/

/-- Two-point invariant: state is either the initial `⟨0,0,1,1⟩` or the
    post-iteration `⟨1, n, 1, 0⟩`. -/
private def singletonInv (n : u64) (s : Tuple4 usize u64 u64 usize) : Prop :=
  s = ⟨(0 : usize), (0 : u64), (1 : u64), (1 : usize)⟩ ∨
  s = ⟨(1 : usize), n, (1 : u64), (0 : usize)⟩

/-- The deterministic computation of one body iteration on the initial state. -/
private theorem singleton_body_init_step
    (k : RustSlice u64) (n : u64) (h : k.val = #[n]) :
    outerBody k ⟨(0 : usize), (0 : u64), (1 : u64), (1 : usize)⟩ =
    pure ⟨(1 : usize), n, (1 : u64), (0 : usize)⟩ := by
  -- 1) k[0]_? reduces to pure n using h
  have h_size : k.val.size = 1 := by rw [h]; rfl
  have h_bound : USize64.toNat (0 : usize) < k.val.size := by
    rw [h_size]; decide
  have h_val_idx : k.val[(0 : usize).toNat]'h_bound = n := by
    simp [h]
  have h_idx : (k[(0 : usize)]_? : RustM u64) = pure n := by
    show (if hh : USize64.toNat (0 : usize) < k.val.size then pure (k.val[(0 : usize).toNat]'hh)
          else (RustM.fail .arrayOutOfBounds : RustM u64)) = pure n
    rw [dif_pos h_bound]
    exact congrArg pure h_val_idx
  -- 2) (0 +? n) = pure n  (since 0 + n = n always)
  have h_add0n : ((0 : u64) +? n : RustM u64) = pure n := by
    show (rust_primitives.ops.arith.Add.add (0 : u64) n : RustM u64) = pure n
    show (if BitVec.uaddOverflow (0 : u64).toBitVec n.toBitVec then
            (RustM.fail .integerOverflow : RustM u64)
          else pure ((0 : u64) + n)) = pure n
    have h_no : BitVec.uaddOverflow (0 : u64).toBitVec n.toBitVec = false := by
      simp [BitVec.uaddOverflow]; exact n.toNat_lt
    rw [h_no]
    have h_zero_add : (0 : u64) + n = n := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add_of_lt (by simp; exact n.toNat_lt)]
      simp
    rw [h_zero_add]
    rfl
  -- 3) (1 *? 1) = pure 1  (since 1*1 = 1 always, no overflow)
  have h_mul11 : ((1 : u64) *? (1 : u64) : RustM u64) = pure 1 := by
    show (rust_primitives.ops.arith.Mul.mul (1 : u64) 1 : RustM u64) = pure 1
    show (if BitVec.umulOverflow (1 : u64).toBitVec (1 : u64).toBitVec then
            (RustM.fail .integerOverflow : RustM u64)
          else pure ((1 : u64) * 1)) = pure 1
    have h_no : BitVec.umulOverflow (1 : u64).toBitVec (1 : u64).toBitVec = false := by
      decide
    rw [h_no]
    rfl
  -- 4) (0 +? 1 : usize) = pure 1
  have h_idx_inc : ((0 : usize) +? (1 : usize) : RustM usize) = pure (1 : usize) := by
    show (rust_primitives.ops.arith.Add.add (0 : usize) (1 : usize) : RustM usize) = pure 1
    show (if BitVec.uaddOverflow (0 : usize).toBitVec (1 : usize).toBitVec then
            (RustM.fail .integerOverflow : RustM usize)
          else pure ((0 : usize) + 1)) = pure 1
    have h_no : BitVec.uaddOverflow (0 : usize).toBitVec (1 : usize).toBitVec = false := by
      decide
    rw [h_no]
    rfl
  -- 5) (1 -? 1 : usize) = pure 0
  have h_rem_dec : ((1 : usize) -? (1 : usize) : RustM usize) = pure (0 : usize) := by
    show (rust_primitives.ops.arith.Sub.sub (1 : usize) (1 : usize) : RustM usize) = pure 0
    show (if BitVec.usubOverflow (1 : usize).toBitVec (1 : usize).toBitVec then
            (RustM.fail .integerOverflow : RustM usize)
          else pure ((1 : usize) - 1)) = pure 0
    have h_no : BitVec.usubOverflow (1 : usize).toBitVec (1 : usize).toBitVec = false := by
      decide
    rw [h_no]
    rfl
  -- Now combine: the body's do-block reduces step-by-step.
  show (do
        let i : u64 ← k[(0 : usize)]_?
        let p : u64 ← ((0 : u64) +? i)
        let r : u64 ← ((1 : u64) *? (← multinomial_u64.binomial p i))
        let idx : usize ← ((0 : usize) +? (1 : usize))
        let remaining : usize ← ((1 : usize) -? (1 : usize))
        pure (rust_primitives.hax.Tuple4.mk idx p r remaining) :
        RustM (rust_primitives.hax.Tuple4 usize u64 u64 usize)) =
        pure ⟨(1 : usize), n, (1 : u64), (0 : usize)⟩
  -- Convert binomial_diag to a pure-flavoured rewrite so simp can fire.
  have h_binom : multinomial_u64.binomial n n = pure (1 : u64) := binomial_diag n
  rw [h_idx]
  simp only [pure_bind]
  rw [h_add0n]
  simp only [pure_bind]
  rw [h_binom]
  simp only [pure_bind]
  rw [h_mul11]
  simp only [pure_bind]
  rw [h_idx_inc]
  simp only [pure_bind]
  rw [h_rem_dec]
  simp only [pure_bind]

/-- Hoare triple for the outer loop in the singleton case. -/
private theorem singleton_outer_loop_triple
    (k : RustSlice u64) (n : u64) (h : k.val = #[n]) :
    ⦃⌜singletonInv n ⟨(0 : usize), (0 : u64), (1 : u64), (1 : usize)⟩⌝⦄
      outerLoop k ⟨(0 : usize), (0 : u64), (1 : u64), (1 : usize)⟩
    ⦃⇓ r => ⌜singletonInv n r ∧ ¬ outerCond r = true⌝⦄ := by
  apply Std.Do.Spec.MonoLoopCombinator.while_loop
    ⟨(0 : usize), (0 : u64), (1 : u64), (1 : usize)⟩
    Lean.Loop.mk outerCond (outerBody k) (singletonInv n)
    (fun s => USize64.toNat s._3)
  intro s hcond hinv
  cases hinv with
  | inl hinv1 =>
    -- s = ⟨0, 0, 1, 1⟩. Body produces ⟨1, n, 1, 0⟩ deterministically.
    subst hinv1
    rw [singleton_body_init_step k n h]
    -- Goal: wp⟦pure ⟨1,n,1,0⟩⟧ Q reduces to Q ⟨1,n,1,0⟩.
    refine ⟨?_, ?_⟩
    · -- termination: USize64.toNat 0 < USize64.toNat 1, i.e., 0 < 1
      show USize64.toNat (0 : usize) < USize64.toNat (1 : usize)
      decide
    · -- invariant: ⟨1, n, 1, 0⟩ satisfies singletonInv (right disjunct)
      right; rfl
  | inr hinv2 =>
    -- s = ⟨1, n, 1, 0⟩, but cond says s._3 > 0; contradiction.
    exfalso
    subst hinv2
    show False
    have h_cond_eq : outerCond ⟨(1 : usize), n, (1 : u64), (0 : usize)⟩ =
                     decide (USize64.toNat (0 : usize) > USize64.toNat (0 : usize)) := rfl
    rw [h_cond_eq] at hcond
    exact absurd hcond (by decide)

/-- Strengthened postcondition for singleton: `r = 1` at loop exit. -/
private theorem singleton_outer_loop_value
    (k : RustSlice u64) (n : u64) (h : k.val = #[n]) :
    ⦃⌜True⌝⦄
      outerLoop k ⟨(0 : usize), (0 : u64), (1 : u64), (1 : usize)⟩
    ⦃⇓ r => ⌜r._2 = (1 : u64)⌝⦄ := by
  have h_triple := singleton_outer_loop_triple k n h
  have h' :
      ⦃⌜singletonInv n ⟨(0 : usize), (0 : u64), (1 : u64), (1 : usize)⟩⌝⦄
        outerLoop k ⟨(0 : usize), (0 : u64), (1 : u64), (1 : usize)⟩
      ⦃⇓ r => ⌜r._2 = (1 : u64)⌝⦄ := by
    apply Triple.of_entails_right _ _ _ _ h_triple
    apply PostCond.entails.of_left_entails
    intro r ⟨hinv, _⟩
    cases hinv with
    | inl heq => rw [heq]; rfl
    | inr heq => rw [heq]; rfl
  apply Triple.of_entails_left _ _ _ _ h'
  intro _
  left; rfl

/-- Hoare triple for the function: `multinomial #[n] = ok 1`. -/
private theorem multinomial_singleton_triple
    (k : RustSlice u64) (n : u64) (h : k.val = #[n]) :
    ⦃⌜True⌝⦄
      multinomial_u64.multinomial k
    ⦃⇓ r => ⌜r = (1 : u64)⌝⦄ := by
  have h_len : core_models.slice.Impl.len u64 k = pure (1 : usize) := by
    unfold core_models.slice.Impl.len rust_primitives.slice.slice_length
    rw [h]
    rfl
  unfold multinomial_u64.multinomial
  unfold rust_primitives.hax.while_loop
  rw [h_len]
  show ⦃⌜True⌝⦄
      (outerLoop k ⟨(0 : usize), (0 : u64), (1 : u64), (1 : usize)⟩ >>=
        fun s => match s with | ⟨_, _, r, _⟩ => pure r)
      ⦃⇓ r => ⌜r = (1 : u64)⌝⦄
  apply Triple.bind _ _ (singleton_outer_loop_value k n h)
  intro s
  cases s with
  | mk idx p r remaining =>
    refine Triple.pure r ?_
    intro hr
    exact hr

/-- Postcondition (boundary): every singleton slice returns `1`. -/
theorem multinomial_singleton
    (k : RustSlice u64) (n : u64) (h : k.val = #[n]) :
    multinomial_u64.multinomial k = RustM.ok 1 := by
  have h_triple := multinomial_singleton_triple k n h
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

/-! ## Overflow case infrastructure

For overflow we cannot use `Spec.MonoLoopCombinator.while_loop` directly:
the Hoare triple in `noThrow` form asserts the function returns `ok`,
not `fail`. We instead use the auto-generated `eq_def` unfolding lemma
for the `partial_fixpoint`-built `Loop.MonoLoopCombinator.forIn.loop`,
unroll the loop twice manually, and exhibit the failure via `bind`. -/

/-- Body of one iteration on the initial overflow state `⟨0, 0, 1, 2⟩`.
    Reads `k[0] = u64::MAX`, sets `p = MAX`, computes `binomial(MAX, MAX) = 1`,
    finishes with `r = 1`, `idx = 1`, `remaining = 1`. -/
private theorem overflow_body_init_step
    (k : RustSlice u64) (h : k.val = #[UInt64.ofNat (2 ^ 64 - 1), 1]) :
    outerBody k ⟨(0 : usize), (0 : u64), (1 : u64), (2 : usize)⟩ =
    pure ⟨(1 : usize), UInt64.ofNat (2 ^ 64 - 1), (1 : u64), (1 : usize)⟩ := by
  -- 1) k[0]_? reduces to pure (UInt64.ofNat (2^64-1)) using h
  have h_size : k.val.size = 2 := by rw [h]; rfl
  have h_bound : USize64.toNat (0 : usize) < k.val.size := by
    rw [h_size]; decide
  have h_val_idx : k.val[(0 : usize).toNat]'h_bound = UInt64.ofNat (2 ^ 64 - 1) := by
    simp [h]
  have h_idx : (k[(0 : usize)]_? : RustM u64) = pure (UInt64.ofNat (2 ^ 64 - 1)) := by
    show (if hh : USize64.toNat (0 : usize) < k.val.size then pure (k.val[(0 : usize).toNat]'hh)
          else (RustM.fail .arrayOutOfBounds : RustM u64)) = pure (UInt64.ofNat (2 ^ 64 - 1))
    rw [dif_pos h_bound]
    exact congrArg pure h_val_idx
  -- 2) (0 +? MAX) = pure MAX
  have h_add0MAX : ((0 : u64) +? UInt64.ofNat (2 ^ 64 - 1) : RustM u64) = pure (UInt64.ofNat (2 ^ 64 - 1)) := by
    show (rust_primitives.ops.arith.Add.add (0 : u64) (UInt64.ofNat (2 ^ 64 - 1)) : RustM u64) = pure _
    show (if BitVec.uaddOverflow (0 : u64).toBitVec (UInt64.ofNat (2 ^ 64 - 1)).toBitVec then
            (RustM.fail .integerOverflow : RustM u64)
          else pure ((0 : u64) + UInt64.ofNat (2 ^ 64 - 1))) = pure (UInt64.ofNat (2 ^ 64 - 1))
    have h_no : BitVec.uaddOverflow (0 : u64).toBitVec (UInt64.ofNat (2 ^ 64 - 1)).toBitVec = false := by
      decide
    rw [h_no]
    have h_zero_add : (0 : u64) + UInt64.ofNat (2 ^ 64 - 1) = UInt64.ofNat (2 ^ 64 - 1) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add_of_lt (by decide)]
      simp
    rw [h_zero_add]
    rfl
  -- 3) binomial MAX MAX = ok 1 — diagonal case
  have h_binom : multinomial_u64.binomial (UInt64.ofNat (2 ^ 64 - 1)) (UInt64.ofNat (2 ^ 64 - 1))
      = pure (1 : u64) := binomial_diag (UInt64.ofNat (2 ^ 64 - 1))
  -- 4) (1 *? 1) = pure 1
  have h_mul11 : ((1 : u64) *? (1 : u64) : RustM u64) = pure 1 := by
    show (rust_primitives.ops.arith.Mul.mul (1 : u64) 1 : RustM u64) = pure 1
    show (if BitVec.umulOverflow (1 : u64).toBitVec (1 : u64).toBitVec then
            (RustM.fail .integerOverflow : RustM u64)
          else pure ((1 : u64) * 1)) = pure 1
    have h_no : BitVec.umulOverflow (1 : u64).toBitVec (1 : u64).toBitVec = false := by
      decide
    rw [h_no]
    rfl
  -- 5) (0 +? 1 : usize) = pure 1
  have h_idx_inc : ((0 : usize) +? (1 : usize) : RustM usize) = pure (1 : usize) := by
    show (rust_primitives.ops.arith.Add.add (0 : usize) (1 : usize) : RustM usize) = pure 1
    show (if BitVec.uaddOverflow (0 : usize).toBitVec (1 : usize).toBitVec then
            (RustM.fail .integerOverflow : RustM usize)
          else pure ((0 : usize) + 1)) = pure 1
    have h_no : BitVec.uaddOverflow (0 : usize).toBitVec (1 : usize).toBitVec = false := by
      decide
    rw [h_no]
    rfl
  -- 6) (2 -? 1 : usize) = pure 1
  have h_rem_dec : ((2 : usize) -? (1 : usize) : RustM usize) = pure (1 : usize) := by
    show (rust_primitives.ops.arith.Sub.sub (2 : usize) (1 : usize) : RustM usize) = pure 1
    show (if BitVec.usubOverflow (2 : usize).toBitVec (1 : usize).toBitVec then
            (RustM.fail .integerOverflow : RustM usize)
          else pure ((2 : usize) - 1)) = pure 1
    have h_no : BitVec.usubOverflow (2 : usize).toBitVec (1 : usize).toBitVec = false := by
      decide
    rw [h_no]
    rfl
  -- Combine
  show (do
        let i : u64 ← k[(0 : usize)]_?
        let p : u64 ← ((0 : u64) +? i)
        let r : u64 ← ((1 : u64) *? (← multinomial_u64.binomial p i))
        let idx : usize ← ((0 : usize) +? (1 : usize))
        let remaining : usize ← ((2 : usize) -? (1 : usize))
        pure (rust_primitives.hax.Tuple4.mk idx p r remaining) :
        RustM (rust_primitives.hax.Tuple4 usize u64 u64 usize)) =
        pure ⟨(1 : usize), UInt64.ofNat (2 ^ 64 - 1), (1 : u64), (1 : usize)⟩
  rw [h_idx]
  simp only [pure_bind]
  rw [h_add0MAX]
  simp only [pure_bind]
  rw [h_binom]
  simp only [pure_bind]
  rw [h_mul11]
  simp only [pure_bind]
  rw [h_idx_inc]
  simp only [pure_bind]
  rw [h_rem_dec]
  simp only [pure_bind]

/-- Body of the second iteration on state `⟨1, MAX, 1, 1⟩`.
    Reads `k[1] = 1`. The first arithmetic op `MAX +? 1` overflows. -/
private theorem overflow_body_second_step
    (k : RustSlice u64) (h : k.val = #[UInt64.ofNat (2 ^ 64 - 1), 1]) :
    outerBody k ⟨(1 : usize), UInt64.ofNat (2 ^ 64 - 1), (1 : u64), (1 : usize)⟩ =
    RustM.fail .integerOverflow := by
  have h_size : k.val.size = 2 := by rw [h]; rfl
  have h_bound : USize64.toNat (1 : usize) < k.val.size := by
    rw [h_size]; decide
  have h_val_idx : k.val[(1 : usize).toNat]'h_bound = (1 : u64) := by
    simp [h]
  have h_idx : (k[(1 : usize)]_? : RustM u64) = pure (1 : u64) := by
    show (if hh : USize64.toNat (1 : usize) < k.val.size then pure (k.val[(1 : usize).toNat]'hh)
          else (RustM.fail .arrayOutOfBounds : RustM u64)) = pure (1 : u64)
    rw [dif_pos h_bound]
    exact congrArg pure h_val_idx
  -- The critical step: MAX +? 1 overflows
  have h_add_overflow :
      (UInt64.ofNat (2 ^ 64 - 1) +? (1 : u64) : RustM u64) = RustM.fail .integerOverflow := by
    show (rust_primitives.ops.arith.Add.add (UInt64.ofNat (2 ^ 64 - 1)) (1 : u64) : RustM u64) = _
    show (if BitVec.uaddOverflow (UInt64.ofNat (2 ^ 64 - 1)).toBitVec (1 : u64).toBitVec then
            (RustM.fail .integerOverflow : RustM u64)
          else pure (UInt64.ofNat (2 ^ 64 - 1) + 1)) = RustM.fail .integerOverflow
    have h_yes : BitVec.uaddOverflow (UInt64.ofNat (2 ^ 64 - 1)).toBitVec (1 : u64).toBitVec = true := by
      decide
    rw [h_yes]
    rfl
  show (do
        let i : u64 ← k[(1 : usize)]_?
        let p : u64 ← (UInt64.ofNat (2 ^ 64 - 1) +? i)
        let r : u64 ← ((1 : u64) *? (← multinomial_u64.binomial p i))
        let idx : usize ← ((1 : usize) +? (1 : usize))
        let remaining : usize ← ((1 : usize) -? (1 : usize))
        pure (rust_primitives.hax.Tuple4.mk idx p r remaining) :
        RustM (rust_primitives.hax.Tuple4 usize u64 u64 usize)) =
        RustM.fail .integerOverflow
  rw [h_idx]
  simp only [pure_bind]
  rw [h_add_overflow]
  rfl

/-- Unrolling lemma: `outerLoop k init` with `cond init = true` equals
    `body init >>= (fun s => outerLoop k s)`. Generated from the
    `partial_fixpoint` definition via `Loop.MonoLoopCombinator.forIn.loop.eq_def`. -/
private theorem outerLoop_unfold (k : RustSlice u64) (init : Tuple4 usize u64 u64 usize)
    (hcond : outerCond init = true) :
    outerLoop k init = outerBody k init >>= fun s => outerLoop k s := by
  show Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk outerCond init (outerBody k) =
       outerBody k init >>= fun s => outerLoop k s
  unfold Lean.Loop.MonoLoopCombinator.while_loop
  unfold Lean.Loop.MonoLoopCombinator.forIn
  rw [Lean.Loop.MonoLoopCombinator.forIn.loop.eq_def]
  unfold Lean.Loop.loopCombinator
  -- The if-then-else is inside a lambda `(fun () s => ...) () init`. Beta-reduce.
  simp only []
  -- Now the goal has `if outerCond init = true then ... else ...`. Apply hcond.
  rw [if_pos hcond]
  -- Now reduce the bind chain.
  rw [bind_assoc]
  apply congrArg ((outerBody k init) >>= ·)
  funext s
  rw [pure_bind]
  rfl

/-- Failure condition: running sum overflow. -/
theorem multinomial_sum_overflow_panics
    (k : RustSlice u64)
    (h : k.val = #[UInt64.ofNat (2 ^ 64 - 1), 1]) :
    multinomial_u64.multinomial k = RustM.fail .integerOverflow := by
  -- Step 1: reduce `multinomial k` to the outer loop applied to the initial state.
  have h_size : k.val.size = 2 := by rw [h]; rfl
  have h_len : core_models.slice.Impl.len u64 k = pure (2 : usize) := by
    unfold core_models.slice.Impl.len rust_primitives.slice.slice_length
    rw [h_size]
    rfl
  unfold multinomial_u64.multinomial
  unfold rust_primitives.hax.while_loop
  rw [h_len]
  show (outerLoop k ⟨(0 : usize), (0 : u64), (1 : u64), (2 : usize)⟩ >>=
       fun s => match s with | ⟨_, _, r, _⟩ => pure r) = RustM.fail .integerOverflow
  -- Step 2: Unroll the loop one iteration (state has cond = true).
  have h_cond_init : outerCond ⟨(0 : usize), (0 : u64), (1 : u64), (2 : usize)⟩ = true := by
    show decide (USize64.toNat (2 : usize) > USize64.toNat (0 : usize)) = true
    decide
  rw [outerLoop_unfold k _ h_cond_init]
  rw [overflow_body_init_step k h]
  simp only [pure_bind]
  -- Now goal: outerLoop k ⟨1, MAX, 1, 1⟩ >>= ... = fail .integerOverflow
  -- Unroll once more.
  have h_cond_2 : outerCond ⟨(1 : usize), UInt64.ofNat (2 ^ 64 - 1), (1 : u64), (1 : usize)⟩ = true := by
    show decide (USize64.toNat (1 : usize) > USize64.toNat (0 : usize)) = true
    decide
  rw [outerLoop_unfold k _ h_cond_2]
  rw [overflow_body_second_step k h]
  rfl

end Multinomial_u64Obligations
