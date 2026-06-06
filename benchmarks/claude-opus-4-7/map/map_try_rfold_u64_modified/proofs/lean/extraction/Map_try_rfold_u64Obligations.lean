-- Companion obligations file for the `map_try_rfold_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import map_try_rfold_u64

open Std.Do
open Std.Tactic
open map_try_rfold_u64
open core_models.ops.range
open core_models.option

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Map_try_rfold_u64Obligations

open rust_primitives.hax (Tuple2)

/-! ## Reference specification

`try_rfoldSpec n init _end f g` mirrors the Rust source's
`reference_back_fold`: the recursive right-to-left fold of the range
`[_end - n, _end)`, applying `f` to each index, threading the accumulator
through `g`, and short-circuiting on `None`. It returns a `(new_end, result)`
pair matching `try_rfold_at`'s output:

* on full consumption, `(_end - n, Some final_acc)` — i.e., the start of the
  range together with the final accumulator;
* on short-circuit, `(boundary, None)` — the position where `g` returned
  `None`.

`n` is the iteration count (intended to be
`n = self.iter._end.toNat - self.iter.start.toNat`). The partiality of `f`
and `g` is preserved: a failure in either propagates up. -/
def try_rfoldSpec (n : Nat) (init : u64) (_end : u64)
    (f : u64 → RustM u64)
    (g : u64 → u64 → RustM (core_models.option.Option u64)) :
    RustM (Tuple2 u64 (core_models.option.Option u64)) :=
  match n with
  | 0 => RustM.ok (Tuple2.mk _end (Option.Some init))
  | n + 1 =>
      f (_end - 1) >>= fun v =>
        g init v >>= fun ans =>
          match ans with
          | Option.None => RustM.ok (Tuple2.mk (_end - 1) Option.None)
          | Option.Some new_acc => try_rfoldSpec n new_acc (_end - 1) f g

/-! ## Worker (`try_rfold_at`) obligations -/

/-- Empty-range postcondition for the worker. When `_end ≤ start` (the
    `start >= _end` branch of the Rust source), `try_rfold_at` returns
    `(_end, Some acc)` and does not invoke `f` or `g`.

    Captures the empty-range half of
    `try_rfold_empty_range_returns_init_without_calls`: the worker does not
    consume any element, so `new_end = _end` and the result is `Some acc`. -/
theorem try_rfold_at_empty_range
    (start _end : u64) (f : u64 → RustM u64) (acc : u64)
    (g : u64 → u64 → RustM (core_models.option.Option u64))
    (h : _end ≤ start) :
    try_rfold_at start _end f acc g
      = RustM.ok (Tuple2.mk _end (Option.Some acc)) := by
  unfold try_rfold_at
  simp only [rust_primitives.cmp.ge]
  have hge : start ≥ _end := h
  simp [hge]
  rfl

/-! Helper lemmas used by `try_rfold_at_matches_spec`. -/

/-- Helper: when `_end > start`, `_end -? 1 = pure (_end - 1)` (no underflow). -/
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
      have h1 : (1 : UInt64).toNat = 1 := rfl
      have hs_pos : 0 < _end.toNat := by
        have : start.toNat < _end.toNat := UInt64.lt_iff_toNat_lt.mp h
        omega
      rw [h1] at h_uf
      omega
  rw [h_no_uf]; rfl

/-- Helper: `(_end - 1).toNat = _end.toNat - 1` when `0 < _end.toNat`. -/
private theorem end_sub_one_toNat (_end : u64) (h : 0 < _end.toNat) :
    (_end - 1).toNat = _end.toNat - 1 := by
  apply UInt64.toNat_sub_of_le'
  show (1 : UInt64).toNat ≤ _end.toNat
  have h1 : (1 : UInt64).toNat = 1 := rfl
  rw [h1]; omega

/-- Functional-correctness postcondition for the worker:
    `try_rfold_at` agrees with the recursive `try_rfoldSpec` at iteration
    count `_end.toNat - start.toNat`. The spec mirrors `reference_back_fold`
    from the Rust source step-for-step (descending index `_end - 1`,
    short-circuit on `None`, value carried in the accumulator).

    Captures `try_rfold_matches_reference_back_fold_and_iter_state`'s value
    claim as well as the iterator-end claim (the first component of the
    returned tuple is exactly the new `_end`). -/
theorem try_rfold_at_matches_spec
    (start _end : u64) (f : u64 → RustM u64) (acc : u64)
    (g : u64 → u64 → RustM (core_models.option.Option u64)) :
    try_rfold_at start _end f acc g
      = try_rfoldSpec (_end.toNat - start.toNat) acc _end f g := by
  induction hk : (_end.toNat - start.toNat) using Nat.strongRecOn
    generalizing _end acc with
  | _ k ih =>
    unfold try_rfold_at
    by_cases h_ge : _end ≤ start
    · -- Empty branch.
      have hk0 : k = 0 := by
        have : _end.toNat ≤ start.toNat := UInt64.le_iff_toNat_le.mp h_ge
        omega
      subst hk0
      simp only [rust_primitives.cmp.ge]
      have hge : start ≥ _end := h_ge
      simp [hge]
      unfold try_rfoldSpec
      rfl
    · -- Non-empty branch.
      have h_lt : start < _end := by
        have h_ngeN : ¬ _end.toNat ≤ start.toNat := fun h =>
          h_ge (UInt64.le_iff_toNat_le.mpr h)
        exact UInt64.lt_iff_toNat_lt.mpr (by omega)
      have h_ltN : start.toNat < _end.toNat := UInt64.lt_iff_toNat_lt.mp h_lt
      have h_end_pos : 0 < _end.toNat := by omega
      have h_k_pos : 0 < k := by omega
      simp only [rust_primitives.cmp.ge]
      have hnge : ¬ start ≥ _end := fun hge =>
        absurd (UInt64.le_iff_toNat_le.mp hge) (by omega)
      simp [hnge]
      rw [sub_one_succeeds start _end h_lt]
      simp only [pure_bind]
      -- Establish measure relationships.
      have h_end_sub : (_end - 1).toNat = _end.toNat - 1 :=
        end_sub_one_toNat _end h_end_pos
      have h_new_meas : (_end - 1).toNat - start.toNat = k - 1 := by
        rw [h_end_sub]; omega
      have h_lt_meas : (_end - 1).toNat - start.toNat < k := by
        rw [h_new_meas]; omega
      -- Reduce spec on the rhs.
      have hk_succ : k = (k - 1) + 1 := by omega
      rw [hk_succ]
      unfold try_rfoldSpec
      apply bind_congr
      intro v
      apply bind_congr
      intro ans
      cases ans with
      | None => dsimp only; rfl
      | Some new_acc =>
        dsimp only
        rw [ih ((_end - 1).toNat - start.toNat) h_lt_meas (_end - 1) new_acc rfl, h_new_meas]

/-! Spec-side totality, proved by structural induction on `n`.

    Used to discharge `try_rfold_at_total` once the worker has been
    rewritten to the spec form via `try_rfold_at_matches_spec`. -/

/-- `RustM.ok x >>= f = f x`. The library's `pure_bind` simp lemma only
    matches literal `Pure.pure`; this rewrite handles the `RustM.ok` form
    produced after reducing definitions. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem try_rfoldSpec_total
    (n : Nat) (acc : u64) (_end : u64)
    (f : u64 → RustM u64)
    (g : u64 → u64 → RustM (core_models.option.Option u64))
    (h_f : ∀ x : u64, ∃ y : u64, f x = RustM.ok y)
    (h_g : ∀ a b : u64,
      ∃ r : core_models.option.Option u64, g a b = RustM.ok r) :
    ∃ r : Tuple2 u64 (core_models.option.Option u64),
      try_rfoldSpec n acc _end f g = RustM.ok r := by
  induction n generalizing acc _end with
  | zero =>
    refine ⟨Tuple2.mk _end (Option.Some acc), ?_⟩
    unfold try_rfoldSpec; rfl
  | succ n ih =>
    unfold try_rfoldSpec
    obtain ⟨v, hv⟩ := h_f (_end - 1)
    rw [hv, RustM_ok_bind]
    obtain ⟨ans, hans⟩ := h_g acc v
    rw [hans, RustM_ok_bind]
    cases ans with
    | None => exact ⟨_, rfl⟩
    | Some new_acc =>
      dsimp only
      exact ih new_acc (_end - 1)

/-- Totality / no-panic for the worker. The only way `try_rfold_at` can
    fail (in the `RustM` sense) is if `f` or `g` themselves fail; the
    `_end -? 1` arithmetic never underflows because the recursive branch
    is only entered when `start < _end`, which forces `_end > 0`. A `g`
    that returns `Option.None` is NOT a failure — short-circuit is encoded
    in the `Option` return, not as a panic.

    The mapper/combinator totality hypotheses are necessary because both
    `f` and `g` are arbitrary higher-order callbacks; the property tests use
    only total ones but the model permits failing ones. -/
theorem try_rfold_at_total
    (start _end : u64) (f : u64 → RustM u64) (acc : u64)
    (g : u64 → u64 → RustM (core_models.option.Option u64))
    (h_f : ∀ x : u64, ∃ y : u64, f x = RustM.ok y)
    (h_g : ∀ a b : u64,
      ∃ r : core_models.option.Option u64, g a b = RustM.ok r) :
    ∃ r : Tuple2 u64 (core_models.option.Option u64),
      try_rfold_at start _end f acc g = RustM.ok r := by
  rw [try_rfold_at_matches_spec]
  exact try_rfoldSpec_total _ acc _end f g h_f h_g

/-! ## Wrapper (`Impl.try_rfold`) obligations -/

/-- Empty-range no-op postcondition for the wrapper. When the inner
    `iter._end ≤ iter.start`, `Impl.try_rfold` returns `(self, Some init)`:
    the `Map` is unchanged (since `new_end = self.iter._end`), and the
    result is `Some init`. Neither `f` nor `g` is invoked.

    Direct capture of `try_rfold_empty_range_returns_init_without_calls`. -/
theorem Impl_try_rfold_empty_range
    (self : Map) (init : u64)
    (g : u64 → u64 → RustM (core_models.option.Option u64))
    (h : self.iter._end ≤ self.iter.start) :
    Impl.try_rfold self init g
      = RustM.ok (Tuple2.mk self (Option.Some init)) := by
  unfold Impl.try_rfold
  rw [try_rfold_at_empty_range self.iter.start self.iter._end self.f init g h]
  rfl

/-- The wrapper preserves `iter.start` and the mapper `f`: the only field
    it may update is `iter._end`. Whenever `Impl.try_rfold` returns
    successfully with new self `r._0`, that new self has the same
    `iter.start` and same `f` as the original.

    Captures the `iter.start` half of
    `try_rfold_matches_reference_back_fold_and_iter_state` (the test
    `m.iter.start == start`). -/
theorem Impl_try_rfold_preserves_start_and_mapper
    (self : Map) (init : u64)
    (g : u64 → u64 → RustM (core_models.option.Option u64))
    (r : Tuple2 Map (core_models.option.Option u64))
    (h : Impl.try_rfold self init g = RustM.ok r) :
    r._0.iter.start = self.iter.start ∧ r._0.f = self.f := by
  unfold Impl.try_rfold at h
  -- Case on the worker's result; match already substitutes in `h`.
  match hwk : try_rfold_at self.iter.start self.iter._end self.f init g, h with
  | RustM.ok pair, h =>
    rw [RustM_ok_bind] at h
    -- h : pure ⟨{self with iter := {self.iter with _end := pair._0}}, pair._1⟩ = RustM.ok r
    have hr : Tuple2.mk { self with iter := { self.iter with _end := pair._0 } } pair._1 = r := by
      have := h
      injection this with hr1
      injection hr1
    rw [← hr]
    exact ⟨rfl, rfl⟩
  | RustM.fail e, h =>
    simp only [bind, ExceptT.bind, ExceptT.mk, Option.bind] at h
    cases h
  | RustM.div, h =>
    simp only [bind, ExceptT.bind, ExceptT.mk, Option.bind] at h
    cases h

/-- Wrapper functional-correctness: `Impl.try_rfold self init g` is exactly
    the worker's result fed into the record-update at `iter._end`. Combined
    with `try_rfold_at_matches_spec`, this pins down both the returned
    `Option u64` (the fold result, with short-circuit) and the resulting
    `iter._end` (the position where the worker stopped: `start` on full
    consumption, the short-circuit boundary on `None`).

    Captures the `iter.end` half of
    `try_rfold_matches_reference_back_fold_and_iter_state` as well as the
    returned-value half. -/
theorem Impl_try_rfold_matches_spec
    (self : Map) (init : u64)
    (g : u64 → u64 → RustM (core_models.option.Option u64)) :
    Impl.try_rfold self init g
      = try_rfoldSpec
          (self.iter._end.toNat - self.iter.start.toNat)
          init self.iter._end self.f g
        >>= fun r =>
          RustM.ok (Tuple2.mk
            { self with iter := { self.iter with _end := r._0 } }
            r._1) := by
  unfold Impl.try_rfold
  rw [try_rfold_at_matches_spec]
  apply bind_congr
  intro pair
  cases pair with
  | mk a b => rfl

/-- Wrapper totality: under totality of `self.f` and `g`, `Impl.try_rfold`
    returns successfully. Follows from the worker's totality plus the
    pure tail of the wrapper (`pure (Tuple2.mk ...)`).

    No additional preconditions on `self.iter.start` / `self.iter._end` are
    needed: the empty-range branch is total (returns `(_end, Some init)`
    directly), and the non-empty branch's `_end -? 1` cannot underflow
    because the branch is gated on `start < _end`, which forces `_end > 0`. -/
theorem Impl_try_rfold_total
    (self : Map) (init : u64)
    (g : u64 → u64 → RustM (core_models.option.Option u64))
    (h_f : ∀ x : u64, ∃ y : u64, self.f x = RustM.ok y)
    (h_g : ∀ a b : u64,
      ∃ r : core_models.option.Option u64, g a b = RustM.ok r) :
    ∃ r : Tuple2 Map (core_models.option.Option u64),
      Impl.try_rfold self init g = RustM.ok r := by
  rw [Impl_try_rfold_matches_spec]
  obtain ⟨pair, hpair⟩ :=
    try_rfoldSpec_total
      (self.iter._end.toNat - self.iter.start.toNat)
      init self.iter._end self.f g h_f h_g
  rw [hpair, RustM_ok_bind]
  exact ⟨_, rfl⟩

end Map_try_rfold_u64Obligations
