-- Companion obligations file for the `gcd_while` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import gcd_while

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Gcd_whileObligations

open rust_primitives.hax (Tuple2)

/-! ## Loop infrastructure

Canonical two-stage proof from `while_example/README.md`: prove a Hoare triple
over the underlying `Loop.MonoLoopCombinator.while_loop`, then convert to an
equation via `RustM.Triple_iff_BitVec`.

The strong invariant is `Nat.gcd s._0 s._1 = Nat.gcd a₀ b₀`, preserved by
`(a, b) ↦ (b, a % b)` thanks to `Nat.gcd_rec` + commutativity. -/

private def loopInv (a₀ b₀ : u64) (s : Tuple2 u64 u64) : Prop :=
  Nat.gcd s._0.toNat s._1.toNat = Nat.gcd a₀.toNat b₀.toNat

private def loopTerm (s : Tuple2 u64 u64) : Nat := s._1.toNat

private theorem gcd_lt_2_64 (a b : u64) : Nat.gcd a.toNat b.toNat < 2 ^ 64 := by
  by_cases hb : b.toNat = 0
  · rw [hb, Nat.gcd_zero_right]
    exact a.toNat_lt
  · have h_le : Nat.gcd a.toNat b.toNat ≤ b.toNat :=
      Nat.gcd_le_right a.toNat (Nat.pos_of_ne_zero hb)
    exact Nat.lt_of_le_of_lt h_le b.toNat_lt

private theorem gcd_toNat_ofNat (a b : u64) :
    (UInt64.ofNat (Nat.gcd a.toNat b.toNat)).toNat = Nat.gcd a.toNat b.toNat :=
  UInt64.toNat_ofNat_of_lt' (gcd_lt_2_64 a b)

/-! ## The loop as an explicit Lean term -/

private abbrev gcdCond : Tuple2 u64 u64 → Bool :=
  fun b => UInt64.toNat b._1 != UInt64.toNat 0

private abbrev gcdBody : Tuple2 u64 u64 → RustM (Tuple2 u64 u64) :=
  fun x =>
    match x with
    | ⟨a, b⟩ =>
      (do
        let t : u64 := b
        let b : u64 ← (a %? b)
        let a : u64 := t
        pure (rust_primitives.hax.Tuple2.mk a b) :
        RustM (rust_primitives.hax.Tuple2 u64 u64))

private abbrev gcdLoop (a b : u64) : RustM (Tuple2 u64 u64) :=
  Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk gcdCond ⟨a, b⟩ gcdBody

/-! ## Stage 1: Hoare triple for the loop -/

private theorem gcd_loop_triple (a₀ b₀ : u64) :
    ⦃⌜ loopInv a₀ b₀ ⟨a₀, b₀⟩ ⌝⦄
      gcdLoop a₀ b₀
    ⦃⇓ r => ⌜ loopInv a₀ b₀ r ∧ ¬ gcdCond r = true ⌝⦄ := by
  apply Std.Do.Spec.MonoLoopCombinator.while_loop ⟨a₀, b₀⟩ Lean.Loop.mk
    gcdCond gcdBody (loopInv a₀ b₀) loopTerm
  intro s hcond hinv
  -- Use `cases` to destructure and trigger iota reduction in the body.
  cases s with
  | mk a b =>
    -- Now `s` is `⟨a, b⟩`; the body's outer match iota-reduces.
    -- `hcond : gcdCond ⟨a, b⟩ = true`, which unfolds to
    -- `(UInt64.toNat b != UInt64.toNat 0) = true`, hence `b ≠ 0`.
    have hb_ne : b ≠ 0 := by
      intro hb_eq
      rw [hb_eq] at hcond
      simp at hcond
    have hb_pos : 0 < b.toNat := by
      rcases Nat.eq_zero_or_pos b.toNat with h | h
      · exfalso; apply hb_ne; apply UInt64.toNat_inj.mp; rw [h]; rfl
      · exact h
    have h_term_lt : (a % b).toNat < b.toNat := by
      rw [UInt64.toNat_mod]; exact Nat.mod_lt _ hb_pos
    have h_inv' : Nat.gcd b.toNat (a % b).toNat = Nat.gcd a₀.toNat b₀.toNat := by
      rw [UInt64.toNat_mod, Nat.gcd_comm b.toNat, ← Nat.gcd_rec, Nat.gcd_comm]
      exact hinv
    have h_rem : (a %? b : RustM u64) = pure (a % b) := by
      show (rust_primitives.ops.arith.Rem.rem a b : RustM u64) = pure (a % b)
      show (if b = 0 then (.fail .divisionByZero : RustM u64) else pure (a % b))
            = pure (a % b)
      rw [if_neg hb_ne]
    -- After `cases`, the gcdBody ⟨a, b⟩ should reduce. Force it via dsimp only.
    dsimp only [gcdBody]
    rw [h_rem]
    simp only [pure_bind]
    exact ⟨h_term_lt, h_inv'⟩

/-! ## Stage 2: Hoare triple for the whole function -/

private theorem gcd_while_triple (a₀ b₀ : u64) :
    ⦃⌜ True ⌝⦄
      gcd_while.gcd_while a₀ b₀
    ⦃⇓ r => ⌜ r = UInt64.ofNat (Nat.gcd a₀.toNat b₀.toNat) ⌝⦄ := by
  have h_loop := gcd_loop_triple a₀ b₀
  have h_loop' :
      ⦃⌜ loopInv a₀ b₀ ⟨a₀, b₀⟩ ⌝⦄
        gcdLoop a₀ b₀
      ⦃⇓ r => ⌜ r._0 = UInt64.ofNat (Nat.gcd a₀.toNat b₀.toNat) ⌝⦄ := by
    apply Triple.of_entails_right _ _ _ _ h_loop
    apply PostCond.entails.of_left_entails
    intro r ⟨hinv, hncond⟩
    -- Derive `r._1.toNat = 0` from `¬gcdCond r = true`.
    have hb_zero_nat : r._1.toNat = 0 := by
      rcases Nat.eq_zero_or_pos r._1.toNat with h | h
      · exact h
      · exfalso
        apply hncond
        -- Goal: gcdCond r = true, which abbrev-unfolds to
        -- (UInt64.toNat r._1 != UInt64.toNat 0) = true
        show (UInt64.toNat r._1 != UInt64.toNat 0) = true
        exact bne_iff_ne.mpr (Nat.pos_iff_ne_zero.mp h)
    unfold loopInv at hinv
    rw [hb_zero_nat, Nat.gcd_zero_right] at hinv
    apply UInt64.toNat_inj.mp
    rw [hinv]
    exact (gcd_toNat_ofNat a₀ b₀).symm
  have h_loop'' :
      ⦃⌜ True ⌝⦄
        gcdLoop a₀ b₀
      ⦃⇓ r => ⌜ r._0 = UInt64.ofNat (Nat.gcd a₀.toNat b₀.toNat) ⌝⦄ := by
    apply Triple.of_entails_left _ _ _ _ h_loop'
    intro _
    show Nat.gcd a₀.toNat b₀.toNat = Nat.gcd a₀.toNat b₀.toNat
    rfl
  -- Reformulate the function as `gcdLoop a₀ b₀ >>= (fun s => match s with | ⟨a,b⟩ => pure a)`.
  -- After unfolding `gcd_while.gcd_while` and `rust_primitives.hax.while_loop`,
  -- the abbrev `gcdLoop` should match the auto-derived form via defeq.
  unfold gcd_while.gcd_while
  unfold rust_primitives.hax.while_loop
  show ⦃⌜True⌝⦄
      (gcdLoop a₀ b₀ >>= fun s => match s with | ⟨a, _⟩ => pure a)
      ⦃⇓ r => ⌜r = UInt64.ofNat (Nat.gcd a₀.toNat b₀.toNat)⌝⦄
  apply Triple.bind _ _ h_loop''
  intro s
  cases s with
  | mk a b =>
    refine Triple.pure a ?_
    intro h
    exact h

/-! ## Stage 3: equational form via `Triple_iff_BitVec` -/

theorem gcd_while_postcondition (a b : u64) :
    gcd_while.gcd_while a b
      = RustM.ok (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) := by
  have h := gcd_while_triple a b
  rw [RustM.Triple_iff_BitVec] at h
  simp only [decide_true, Bool.not_true, Bool.false_or,
             Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hok, hval⟩ := h
  cases hf : gcd_while.gcd_while a b with
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

/-! ## Contract clauses derived from the closed form -/

theorem gcd_while_total (a b : u64) :
    ∃ v : u64, gcd_while.gcd_while a b = RustM.ok v :=
  ⟨_, gcd_while_postcondition a b⟩

theorem gcd_while_b_zero (a : u64) :
    gcd_while.gcd_while a 0 = RustM.ok a := by
  rw [gcd_while_postcondition]
  congr 1
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofNat_of_lt' (gcd_lt_2_64 a 0)]
  rw [show (0 : u64).toNat = 0 from rfl, Nat.gcd_zero_right]

theorem gcd_while_a_zero (b : u64) :
    gcd_while.gcd_while 0 b = RustM.ok b := by
  rw [gcd_while_postcondition]
  congr 1
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofNat_of_lt' (gcd_lt_2_64 0 b)]
  rw [show (0 : u64).toNat = 0 from rfl, Nat.gcd_zero_left]

theorem gcd_while_divides_a (a b : u64) :
    ∃ v : u64, gcd_while.gcd_while a b = RustM.ok v ∧ v.toNat ∣ a.toNat := by
  refine ⟨_, gcd_while_postcondition a b, ?_⟩
  rw [gcd_toNat_ofNat]
  exact Nat.gcd_dvd_left a.toNat b.toNat

theorem gcd_while_divides_b (a b : u64) :
    ∃ v : u64, gcd_while.gcd_while a b = RustM.ok v ∧ v.toNat ∣ b.toNat := by
  refine ⟨_, gcd_while_postcondition a b, ?_⟩
  rw [gcd_toNat_ofNat]
  exact Nat.gcd_dvd_right a.toNat b.toNat

theorem gcd_while_greatest (a b : u64) :
    ∃ v : u64, gcd_while.gcd_while a b = RustM.ok v ∧
      ∀ d : Nat, d ∣ a.toNat → d ∣ b.toNat → d ∣ v.toNat := by
  refine ⟨_, gcd_while_postcondition a b, ?_⟩
  intro d hda hdb
  rw [gcd_toNat_ofNat]
  exact Nat.dvd_gcd hda hdb

end Gcd_whileObligations
