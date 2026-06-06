-- Companion obligations file for the `map_rfold_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import map_rfold_u64

open Std.Do
open Std.Tactic
open map_rfold_u64
open core_models.ops.range

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Map_rfold_u64Obligations

open rust_primitives.hax (Tuple2)

/-- Reference specification of `Map.rfold`: the recursive right-to-left
    fold of the range `[start, _end)`, applying `f` to each element and
    combining the result with the accumulator via `g`. Mirrors the body
    of the Rust loop step-for-step (`acc := g(acc, f(end))` with `end`
    decreasing from `_end - 1` down to `start`).

    `n` is the iteration count (intended to be called with
    `n = self.iter._end.toNat - self.iter.start.toNat`). The partiality
    of `f` and `g` is preserved: a failure in either propagates up. -/
def rfoldSpec (n : Nat) (init : u64) (_end : u64)
    (f : u64 → RustM u64) (g : u64 → u64 → RustM u64) : RustM u64 :=
  match n with
  | 0 => RustM.ok init
  | n + 1 =>
      f (_end - 1) >>= fun v =>
        g init v >>= fun acc =>
          rfoldSpec n acc (_end - 1) f g

/-! ## Loop-shape lemmas

We need to unfold `Loop.MonoLoopCombinator.while_loop` one step at a time.
`partial_fixpoint` gives us this for `forIn.loop`. -/

private theorem forIn_loop_unfold_step {β : Type}
    (f : Unit → β → RustM (ForInStep β)) (init : β) :
    Lean.Loop.MonoLoopCombinator.forIn.loop f init =
      (do let r ← f () init
          match r with
          | ForInStep.done b => pure b
          | ForInStep.yield b => Lean.Loop.MonoLoopCombinator.forIn.loop f b) := by
  show Lean.Loop.MonoLoopCombinator.forIn.loop f init =
    Lean.Loop.loopCombinator f (Lean.Loop.MonoLoopCombinator.forIn.loop f) init
  unfold Lean.Loop.MonoLoopCombinator.forIn.loop
  rfl

private theorem while_loop_unfold {β : Type} (cond : β → Bool) (body : β → RustM β) (init : β) :
    Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk cond init body =
      (if cond init then body init >>= fun next =>
         Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk cond next body
       else pure init) := by
  show Lean.Loop.MonoLoopCombinator.forIn Lean.Loop.mk init
        (fun (_ : Unit) (s : β) =>
          if cond s = true then do let s ← body s; pure (ForInStep.yield s)
          else pure (ForInStep.done s))
       = _
  unfold Lean.Loop.MonoLoopCombinator.forIn
  rw [forIn_loop_unfold_step]
  by_cases hc : cond init
  · simp only [hc, if_true, bind_assoc, pure_bind]
    rfl
  · simp only [hc, Bool.false_eq_true, if_false, pure_bind]

/-! ## Helpers for the body's discharges. -/

/-- When `_end > start`, `_end -? 1 = pure (_end - 1)`. -/
private theorem sub_one_succeeds (start _end : u64) (h : start < _end) :
    (_end -? (1 : u64) : RustM u64) = pure (_end - 1) := by
  show (rust_primitives.ops.arith.Sub.sub _end (1 : u64) : RustM u64) = pure (_end - 1)
  show (if BitVec.usubOverflow _end.toBitVec (1 : u64).toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (_end - 1)) = pure (_end - 1)
  have h_no_uf : BitVec.usubOverflow _end.toBitVec (1 : u64).toBitVec = false := by
    cases hb : BitVec.usubOverflow _end.toBitVec (1 : u64).toBitVec with
    | false => rfl
    | true =>
      exfalso
      have h_uf : UInt64.subOverflow _end (1 : u64) = true := hb
      rw [UInt64.subOverflow_iff] at h_uf
      have hs_pos : 0 < _end.toNat := by
        have : start.toNat < _end.toNat := UInt64.lt_iff_toNat_lt.mp h
        omega
      have h1 : (1 : UInt64).toNat = 1 := rfl
      rw [h1] at h_uf; omega
  rw [h_no_uf]; rfl

/-- Toggled cond — the value of the loop's pure cond at state `⟨acc, _end⟩`. -/
private abbrev loopCond (start : u64) : Tuple2 u64 u64 → Bool :=
  fun s => decide (UInt64.toNat s._1 > UInt64.toNat start)

/-- The body of the loop, separated out as a named function for cleaner reasoning. -/
private abbrev loopBody (self : Map) (g : u64 → u64 → RustM u64) :
    Tuple2 u64 u64 → RustM (Tuple2 u64 u64) :=
  fun x => match x with
    | ⟨acc, _end⟩ =>
      (do
        let _end : u64 ← (_end -? (1 : u64))
        let __do_lift : u64 ← self.f _end
        let acc : u64 ← g acc __do_lift
        pure (Tuple2.mk acc _end) : RustM (Tuple2 u64 u64))

/-- The loop as an explicit Lean expression. -/
private abbrev rfoldLoop (self : Map) (init : u64) (g : u64 → u64 → RustM u64) :
    RustM (Tuple2 u64 u64) :=
  Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk
    (loopCond self.iter.start)
    (Tuple2.mk init self.iter._end)
    (loopBody self g)

/-- `Impl.rfold` is the loop followed by projecting out the accumulator. -/
private theorem rfold_eq_loop (self : Map) (init : u64) (g : u64 → u64 → RustM u64) :
    Impl.rfold self init g =
      (rfoldLoop self init g >>= fun s => match s with | ⟨acc, _⟩ => pure acc) := by
  rfl

/-! ## Main equation by induction on the iteration count. -/

/-- Auxiliary form: `while_loop ⟨acc, _end⟩` projected through the outer
    `>>= fun ⟨a, _⟩ => pure a` equals `rfoldSpec n acc _end f g` whenever
    `n = _end.toNat - start.toNat`. -/
private theorem loop_eq_rfoldSpec (self : Map) (g : u64 → u64 → RustM u64)
    (n : Nat) (acc : u64) (_end : u64)
    (hn : _end.toNat - self.iter.start.toNat = n) :
    (Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk
        (loopCond self.iter.start) (Tuple2.mk acc _end) (loopBody self g)
      >>= fun s => match s with | ⟨a, _⟩ => pure a)
      = rfoldSpec n acc _end self.f g := by
  induction n generalizing acc _end with
  | zero =>
      -- _end.toNat ≤ start.toNat, so cond is false; loop exits immediately.
      have h_le : _end.toNat ≤ self.iter.start.toNat := by omega
      have h_not_gt : ¬ _end.toNat > self.iter.start.toNat := by omega
      have h_cond_false : loopCond self.iter.start ⟨acc, _end⟩ = false := by
        show decide (UInt64.toNat _end > UInt64.toNat self.iter.start) = false
        exact decide_eq_false h_not_gt
      rw [while_loop_unfold]
      rw [h_cond_false]
      simp only [Bool.false_eq_true, if_false, pure_bind]
      rfl
  | succ n ih =>
      -- _end.toNat > start.toNat, so cond is true; loop steps once.
      have h_gt : _end.toNat > self.iter.start.toNat := by omega
      have h_lt : self.iter.start < _end := UInt64.lt_iff_toNat_lt.mpr h_gt
      have h_cond_true : loopCond self.iter.start ⟨acc, _end⟩ = true := by
        show decide (UInt64.toNat _end > UInt64.toNat self.iter.start) = true
        exact decide_eq_true h_gt
      rw [while_loop_unfold]
      rw [h_cond_true]
      simp only [if_true]
      -- Body computation: _end -? 1 reduces to pure (_end - 1).
      have h_sub : (_end -? (1 : u64) : RustM u64) = pure (_end - 1) :=
        sub_one_succeeds self.iter.start _end h_lt
      -- Reduce body.
      have h_body : loopBody self g ⟨acc, _end⟩ =
          (self.f (_end - 1) >>= fun v =>
            g acc v >>= fun new_acc =>
              pure (Tuple2.mk new_acc (_end - 1))) := by
        show (do let _end : u64 ← (_end -? (1 : u64))
                 let v : u64 ← self.f _end
                 let acc : u64 ← g acc v
                 pure (Tuple2.mk acc _end) : RustM (Tuple2 u64 u64)) = _
        rw [h_sub]
        simp only [pure_bind]
      rw [h_body]
      -- Now: (self.f (_end-1) >>= fun v => g acc v >>= fun new_acc => pure ⟨new_acc, _end-1⟩) >>= continue
      --     = self.f (_end-1) >>= fun v => g acc v >>= fun new_acc => continue ⟨new_acc, _end-1⟩
      simp only [bind_assoc, pure_bind]
      -- Apply IH at new_acc, _end - 1.
      have h_end_sub_toNat : (_end - 1).toNat = _end.toNat - 1 := by
        apply UInt64.toNat_sub_of_le'
        show (1 : UInt64).toNat ≤ _end.toNat
        have h1 : (1 : UInt64).toNat = 1 := rfl
        rw [h1]; omega
      have h_ih_arg : (_end - 1).toNat - self.iter.start.toNat = n := by
        rw [h_end_sub_toNat]; omega
      -- Unfold rfoldSpec on the RHS.
      show (self.f (_end - 1) >>= fun v => g acc v >>= fun new_acc =>
              Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk
                (loopCond self.iter.start) (Tuple2.mk new_acc (_end - 1)) (loopBody self g)
              >>= fun s => match s with | ⟨a, _⟩ => pure a)
            = rfoldSpec (n + 1) acc _end self.f g
      show (self.f (_end - 1) >>= fun v => g acc v >>= fun new_acc =>
              (Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk
                  (loopCond self.iter.start) (Tuple2.mk new_acc (_end - 1)) (loopBody self g)
                >>= fun s => match s with | ⟨a, _⟩ => pure a))
            = rfoldSpec (n + 1) acc _end self.f g
      unfold rfoldSpec
      apply bind_congr
      intro v
      apply bind_congr
      intro new_acc
      exact ih new_acc (_end - 1) h_ih_arg

theorem rfold_empty_range_returns_init
    (self : Map) (init : u64) (g : u64 → u64 → RustM u64)
    (h : self.iter._end ≤ self.iter.start) :
    Impl.rfold self init g = RustM.ok init := by
  rw [rfold_eq_loop]
  have h_le : self.iter._end.toNat ≤ self.iter.start.toNat := UInt64.le_iff_toNat_le.mp h
  have h_n : self.iter._end.toNat - self.iter.start.toNat = 0 := by omega
  have := loop_eq_rfoldSpec self g 0 init self.iter._end h_n
  rw [this]
  unfold rfoldSpec
  rfl

theorem rfold_matches_spec
    (self : Map) (init : u64) (g : u64 → u64 → RustM u64) :
    Impl.rfold self init g =
      rfoldSpec (self.iter._end.toNat - self.iter.start.toNat)
        init self.iter._end self.f g := by
  rw [rfold_eq_loop]
  exact loop_eq_rfoldSpec self g _ init self.iter._end rfl

/-! ## Totality from the equation + totality of f and g. -/

private theorem rfoldSpec_total (n : Nat) (init : u64) (_end : u64)
    (f : u64 → RustM u64) (g : u64 → u64 → RustM u64)
    (h_f : ∀ x : u64, ∃ y : u64, f x = RustM.ok y)
    (h_g : ∀ a b : u64, ∃ c : u64, g a b = RustM.ok c) :
    ∃ r : u64, rfoldSpec n init _end f g = RustM.ok r := by
  induction n generalizing init _end with
  | zero =>
      refine ⟨init, ?_⟩
      unfold rfoldSpec; rfl
  | succ n ih =>
      unfold rfoldSpec
      obtain ⟨v, hv⟩ := h_f (_end - 1)
      rw [hv]
      show ∃ r, (g init v >>= fun acc => rfoldSpec n acc (_end - 1) f g) = RustM.ok r
      obtain ⟨c, hc⟩ := h_g init v
      rw [hc]
      show ∃ r, rfoldSpec n c (_end - 1) f g = RustM.ok r
      exact ih c (_end - 1)

theorem rfold_total
    (self : Map) (init : u64) (g : u64 → u64 → RustM u64)
    (h_f : ∀ x : u64, ∃ y : u64, self.f x = RustM.ok y)
    (h_g : ∀ a b : u64, ∃ c : u64, g a b = RustM.ok c) :
    ∃ r : u64, Impl.rfold self init g = RustM.ok r := by
  rw [rfold_matches_spec]
  exact rfoldSpec_total _ init self.iter._end self.f g h_f h_g

end Map_rfold_u64Obligations
