-- Companion obligations file for the `map_fold_method_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import map_fold_method_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Map_fold_method_u64Obligations

open map_fold_method_u64
open core_models.ops.range
open rust_primitives.hax (Tuple2)

/-! ## Reference fold

The Rust loop iterates `i` over `[start, _end)` and accumulates
`acc := g(acc, f(i))`. The canonical Lean-side reference is a `List.foldl`
over `List.range' start (end − start)`, which materialises the same
left-to-right iteration order. -/

private def specFold (s e : u64) (f' : u64 → u64) (g' : u64 → u64 → u64)
    (init : u64) : u64 :=
  (List.range' s.toNat (e.toNat - s.toNat)).foldl
    (fun acc i => g' acc (f' (UInt64.ofNat i))) init

/-! ## Loop infrastructure (canonical two-stage shape, see `while_example/README.md`). -/

/-- Pure condition. Matches the auto-derived form of `i <? _end`. -/
private abbrev mapCond (_end : u64) : Tuple2 u64 u64 → Bool :=
  fun b => decide (UInt64.toNat b._1 < UInt64.toNat _end)

/-- Body, matching the lambda in `Impl.fold` after unfolding. -/
private abbrev mapBody (f : u64 → RustM u64) (g : u64 → u64 → RustM u64) :
    Tuple2 u64 u64 → RustM (Tuple2 u64 u64) :=
  fun x => match x with
    | ⟨acc, i⟩ =>
      (do
        let acc : u64 ← g acc (← f i)
        let i : u64 ← (i +? (1 : u64))
        pure (rust_primitives.hax.Tuple2.mk acc i) :
        RustM (rust_primitives.hax.Tuple2 u64 u64))

/-- The loop as an explicit Lean term, matching the unfolded
    `rust_primitives.hax.while_loop` form. -/
private abbrev mapLoop (s _end init : u64)
    (f : u64 → RustM u64) (g : u64 → u64 → RustM u64) :
    RustM (Tuple2 u64 u64) :=
  Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk (mapCond _end)
    (rust_primitives.hax.Tuple2.mk init s) (mapBody f g)

/-! ## Helper: one-step unfolding of `specFold`. -/

private theorem specFold_step (s i : u64)
    (f' : u64 → u64) (g' : u64 → u64 → u64) (init : u64)
    (hs : s.toNat ≤ i.toNat) (hi1 : i.toNat + 1 < 2 ^ 64) :
    specFold s (i + 1) f' g' init
      = g' (specFold s i f' g' init) (f' i) := by
  unfold specFold
  -- (i+1).toNat = i.toNat + 1, no overflow
  have h1 : (1 : u64).toNat = 1 := rfl
  have hadd : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt64.toNat_add_of_lt (by rw [h1]; omega)]
    rw [h1]
  rw [hadd]
  -- rewrite the length: (i+1) - s = (i - s) + 1
  have hsub : i.toNat + 1 - s.toNat = (i.toNat - s.toNat) + 1 := by omega
  rw [hsub]
  -- range' s (n+1) = range' s n ++ [s + n]
  rw [List.range'_1_concat]
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  -- s + (i - s) = i
  have hsum : s.toNat + (i.toNat - s.toNat) = i.toNat := by omega
  rw [hsum]
  -- UInt64.ofNat i.toNat = i
  rw [show UInt64.ofNat i.toNat = i from (UInt64.ofNat_toNat (x := i))]

/-! ## Stage 1a: Hoare triple for the empty case (`s = e`). -/

private theorem mapLoop_empty_triple (init s _end : u64)
    (hse : _end.toNat ≤ s.toNat)
    (f : u64 → RustM u64) (g : u64 → u64 → RustM u64) :
    ⦃⌜ True ⌝⦄
      mapLoop s _end init f g
    ⦃⇓ r => ⌜ r = (⟨init, s⟩ : Tuple2 u64 u64) ⌝⦄ := by
  -- Step 1: prove with the strong precondition `b = ⟨init, s⟩`
  have h_loop :
      ⦃⌜ ((⟨init, s⟩ : Tuple2 u64 u64) = ⟨init, s⟩) ⌝⦄
        Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk (mapCond _end)
          (⟨init, s⟩ : Tuple2 u64 u64) (mapBody f g)
      ⦃⇓ r => ⌜ r = (⟨init, s⟩ : Tuple2 u64 u64) ∧
                     ¬ mapCond _end r = true ⌝⦄ := by
    apply Std.Do.Spec.MonoLoopCombinator.while_loop ⟨init, s⟩ Lean.Loop.mk
      (mapCond _end) (mapBody f g)
      (fun b => b = ⟨init, s⟩) (fun _ => 0)
    intro b hcond hinv
    subst hinv
    -- hcond : mapCond _end ⟨init, s⟩ = true → contradiction since _end ≤ s
    simp [mapCond] at hcond
    omega
  -- Step 2: strengthen post to drop ¬cond clause
  have h_loop' :
      ⦃⌜ ((⟨init, s⟩ : Tuple2 u64 u64) = ⟨init, s⟩) ⌝⦄
        Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk (mapCond _end)
          (⟨init, s⟩ : Tuple2 u64 u64) (mapBody f g)
      ⦃⇓ r => ⌜ r = (⟨init, s⟩ : Tuple2 u64 u64) ⌝⦄ := by
    apply Triple.of_entails_right _ _ _ _ h_loop
    apply PostCond.entails.of_left_entails
    intro r ⟨h, _⟩
    exact h
  -- Step 3: weaken pre to True
  show ⦃⌜ True ⌝⦄
      Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk (mapCond _end)
        (⟨init, s⟩ : Tuple2 u64 u64) (mapBody f g)
    ⦃⇓ r => ⌜ r = (⟨init, s⟩ : Tuple2 u64 u64) ⌝⦄
  apply Triple.of_entails_left _ _ _ _ h_loop'
  intro _
  show (⟨init, s⟩ : Tuple2 u64 u64) = ⟨init, s⟩
  rfl

/-! ## Stage 1b: Hoare triple for the full fold case. -/

/-- Strong invariant: counter is in `[s, e]`, and the accumulator equals
    the partial fold of `[s, i)`. -/
private def loopInv (s e : u64) (f' : u64 → u64) (g' : u64 → u64 → u64)
    (init : u64) (st : Tuple2 u64 u64) : Prop :=
  s.toNat ≤ st._1.toNat ∧ st._1.toNat ≤ e.toNat ∧
    st._0 = specFold s st._1 f' g' init

/-- Termination measure: distance to `e`. -/
private def loopTerm (e : u64) (st : Tuple2 u64 u64) : Nat :=
  e.toNat - st._1.toNat

private theorem mapLoop_full_triple (s e init : u64)
    (f : u64 → RustM u64) (g : u64 → u64 → RustM u64)
    (f' : u64 → u64) (g' : u64 → u64 → u64)
    (hf : ∀ x, f x = RustM.ok (f' x))
    (hg : ∀ a b, g a b = RustM.ok (g' a b)) :
    ⦃⌜ loopInv s e f' g' init ⟨init, s⟩ ⌝⦄
      mapLoop s e init f g
    ⦃⇓ r => ⌜ loopInv s e f' g' init r ∧ ¬ mapCond e r = true ⌝⦄ := by
  show ⦃⌜ loopInv s e f' g' init ⟨init, s⟩ ⌝⦄
      Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk (mapCond e)
        (⟨init, s⟩ : Tuple2 u64 u64) (mapBody f g)
    ⦃⇓ r => ⌜ loopInv s e f' g' init r ∧ ¬ mapCond e r = true ⌝⦄
  apply Std.Do.Spec.MonoLoopCombinator.while_loop ⟨init, s⟩ Lean.Loop.mk
    (mapCond e) (mapBody f g) (loopInv s e f' g' init) (loopTerm e)
  intro b hcond hinv
  cases b with
  | mk acc i =>
    -- After cases, b._0 = acc and b._1 = i (reduces via iota)
    -- Decompose invariant and condition
    unfold loopInv at hinv
    dsimp only at hinv
    obtain ⟨hsi, hie, hacc⟩ := hinv
    -- hcond : decide (i.toNat < e.toNat) = true → i.toNat < e.toNat
    have hie_strict : i.toNat < e.toNat := by
      simp [mapCond] at hcond
      exact hcond
    -- e ≤ 2^64 - 1, so i + 1 ≤ e ≤ 2^64 - 1 < 2^64
    have hi1 : i.toNat + 1 < 2 ^ 64 := by
      have : e.toNat < 2 ^ 64 := e.toNat_lt
      omega
    have hadd : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt64.toNat_add_of_lt hi1]; rfl
    -- The body: g acc (f i) = pure (g' acc (f' i)); i+1 doesn't overflow
    have h_f : f i = pure (f' i) := hf i
    have h_g : g acc (f' i) = pure (g' acc (f' i)) := hg acc (f' i)
    have h_add : (i +? (1 : u64) : RustM u64) = pure (i + 1) := by
      show (rust_primitives.ops.arith.Add.add i 1 : RustM u64) = pure (i + 1)
      show (if BitVec.uaddOverflow i.toBitVec (1 : u64).toBitVec then
              (.fail .integerOverflow : RustM u64)
            else pure (i + 1)) = pure (i + 1)
      rw [show BitVec.uaddOverflow i.toBitVec (1 : u64).toBitVec = false from ?_]
      · rfl
      · have h1 : (1 : u64).toNat = 1 := rfl
        have hno : ¬ UInt64.addOverflow i 1 := by
          rw [UInt64.addOverflow_iff]
          rw [h1]; omega
        exact (Bool.not_eq_true _).mp hno
    -- Compute the body
    dsimp only [mapBody]
    rw [h_f, pure_bind, h_g, pure_bind, h_add, pure_bind]
    -- Goal: wp⟦pure ⟨g' acc (f' i), i + 1⟩⟧ → (term decrease ∧ inv (i+1))
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- termination decreases
      show e.toNat - (i + 1).toNat < e.toNat - i.toNat
      rw [hadd]; omega
    · -- s ≤ (i+1)
      show s.toNat ≤ (i + 1).toNat
      rw [hadd]; omega
    · -- (i+1) ≤ e
      show (i + 1).toNat ≤ e.toNat
      rw [hadd]; omega
    · -- new acc = specFold s (i+1) f' g' init
      show g' acc (f' i) = specFold s (i + 1) f' g' init
      rw [specFold_step s i f' g' init hsi hi1]
      rw [hacc]

/-! ## Stage 2: convert triples to equations. -/

/-- Edge-case contract clause (mirror of `empty_range_returns_init`):
    when the range is empty (`start = _end`), the loop body never runs
    and the function returns `init` unchanged. -/
theorem empty_range_returns_init (init s : u64)
    (f : u64 → RustM u64) (g : u64 → u64 → RustM u64) :
    Impl.fold { iter := { start := s, _end := s }, f := f } init g
      = RustM.ok init := by
  -- Stage 1: triple
  have h_triple :
      ⦃⌜ True ⌝⦄
        Impl.fold { iter := { start := s, _end := s }, f := f } init g
      ⦃⇓ r => ⌜ r = init ⌝⦄ := by
    unfold Impl.fold
    unfold rust_primitives.hax.while_loop
    show ⦃⌜ True ⌝⦄
        (mapLoop s s init f g >>= fun s => match s with | ⟨a, _⟩ => pure a)
      ⦃⇓ r => ⌜ r = init ⌝⦄
    apply Triple.bind _ _ (mapLoop_empty_triple init s s (Nat.le_refl _) f g)
    intro b
    cases b with
    | mk a c =>
      refine Triple.pure a ?_
      intro h
      exact congrArg (·._0) h
  -- Stage 2: convert
  have h := h_triple
  rw [RustM.Triple_iff_BitVec] at h
  simp only [decide_true, Bool.not_true, Bool.false_or,
             Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hok, hval⟩ := h
  cases hf : Impl.fold { iter := { start := s, _end := s }, f := f } init g with
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

/-- Canonical postcondition (mirror of `matches_composed_fold`): when
    `f` and `g` are total (always return `RustM.ok`), the Rust fold
    equals the Lean reference fold over `[s, e)` with `g` applied to
    `f`-mapped elements in left-to-right order. -/
theorem fold_matches_composed_fold (s e init : u64)
    (f : u64 → RustM u64) (g : u64 → u64 → RustM u64)
    (f' : u64 → u64) (g' : u64 → u64 → u64)
    (hf : ∀ x, f x = RustM.ok (f' x))
    (hg : ∀ a b, g a b = RustM.ok (g' a b)) :
    Impl.fold { iter := { start := s, _end := e }, f := f } init g
      = RustM.ok (specFold s e f' g' init) := by
  -- We split on whether s ≤ e (general case) or s > e (empty case).
  by_cases hse : s.toNat ≤ e.toNat
  · -- General case via mapLoop_full_triple
    have h_loop_triple := mapLoop_full_triple s e init f g f' g' hf hg
    -- Strengthen postcondition to `r._0 = specFold s e f' g' init`
    have h_loop' :
        ⦃⌜ loopInv s e f' g' init ⟨init, s⟩ ⌝⦄
          mapLoop s e init f g
        ⦃⇓ r => ⌜ r._0 = specFold s e f' g' init ⌝⦄ := by
      apply Triple.of_entails_right _ _ _ _ h_loop_triple
      apply PostCond.entails.of_left_entails
      intro r ⟨⟨hsi, hie, hacc⟩, hncond⟩
      have h_ge : r._1.toNat ≥ e.toNat := by
        simp [mapCond] at hncond
        omega
      have h_eq : r._1.toNat = e.toNat := by omega
      rw [hacc]
      show specFold s r._1 f' g' init = specFold s e f' g' init
      unfold specFold
      rw [show r._1.toNat - s.toNat = e.toNat - s.toNat from by omega]
    -- Weaken the precondition: True → loopInv ⟨init, s⟩
    have h_loop'' :
        ⦃⌜ True ⌝⦄
          mapLoop s e init f g
        ⦃⇓ r => ⌜ r._0 = specFold s e f' g' init ⌝⦄ := by
      apply Triple.of_entails_left _ _ _ _ h_loop'
      intro _
      show s.toNat ≤ s.toNat ∧ s.toNat ≤ e.toNat ∧ init = specFold s s f' g' init
      refine ⟨Nat.le_refl _, hse, ?_⟩
      unfold specFold
      rw [show s.toNat - s.toNat = 0 from Nat.sub_self _]
      rfl
    -- Stage 1: triple for Impl.fold
    have h_triple :
        ⦃⌜ True ⌝⦄
          Impl.fold { iter := { start := s, _end := e }, f := f } init g
        ⦃⇓ r => ⌜ r = specFold s e f' g' init ⌝⦄ := by
      unfold Impl.fold
      unfold rust_primitives.hax.while_loop
      show ⦃⌜ True ⌝⦄
          (mapLoop s e init f g >>= fun s => match s with | ⟨a, _⟩ => pure a)
        ⦃⇓ r => ⌜ r = specFold s e f' g' init ⌝⦄
      apply Triple.bind _ _ h_loop''
      intro b
      cases b with
      | mk a c =>
        refine Triple.pure a ?_
        intro h
        exact h
    -- Stage 2: convert
    have h := h_triple
    rw [RustM.Triple_iff_BitVec] at h
    simp only [decide_true, Bool.not_true, Bool.false_or,
               Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hok, hval⟩ := h
    cases hf' : Impl.fold { iter := { start := s, _end := e }, f := f } init g with
    | none =>
      rw [hf'] at hok
      simp [RustM.toBVRustM] at hok
    | some result =>
      cases result with
      | ok v =>
        rw [hf'] at hval
        simp [RustM.toBVRustM] at hval
        exact congrArg RustM.ok hval
      | error err =>
        rw [hf'] at hok
        cases err <;> simp [RustM.toBVRustM] at hok
  · -- Empty case: e < s, so specFold = init and loop doesn't run.
    have hse_lt : e.toNat ≤ s.toNat := by omega
    have hspec : specFold s e f' g' init = init := by
      unfold specFold
      rw [show e.toNat - s.toNat = 0 from by omega]
      rfl
    rw [hspec]
    -- Same proof as empty_range_returns_init but with different e
    have h_triple :
        ⦃⌜ True ⌝⦄
          Impl.fold { iter := { start := s, _end := e }, f := f } init g
        ⦃⇓ r => ⌜ r = init ⌝⦄ := by
      unfold Impl.fold
      unfold rust_primitives.hax.while_loop
      show ⦃⌜ True ⌝⦄
          (mapLoop s e init f g >>= fun s => match s with | ⟨a, _⟩ => pure a)
        ⦃⇓ r => ⌜ r = init ⌝⦄
      apply Triple.bind _ _ (mapLoop_empty_triple init s e hse_lt f g)
      intro b
      cases b with
      | mk a c =>
        refine Triple.pure a ?_
        intro h
        exact congrArg (·._0) h
    have h := h_triple
    rw [RustM.Triple_iff_BitVec] at h
    simp only [decide_true, Bool.not_true, Bool.false_or,
               Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hok, hval⟩ := h
    cases hf' : Impl.fold { iter := { start := s, _end := e }, f := f } init g with
    | none =>
      rw [hf'] at hok
      simp [RustM.toBVRustM] at hok
    | some result =>
      cases result with
      | ok v =>
        rw [hf'] at hval
        simp [RustM.toBVRustM] at hval
        exact congrArg RustM.ok hval
      | error err =>
        rw [hf'] at hok
        cases err <;> simp [RustM.toBVRustM] at hok

end Map_fold_method_u64Obligations
