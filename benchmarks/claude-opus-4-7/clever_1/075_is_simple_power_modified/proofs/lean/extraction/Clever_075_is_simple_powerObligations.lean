-- Companion obligations file for the `clever_075_is_simple_power` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_075_is_simple_power

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_075_is_simple_powerObligations

/-! ## Numeric helper lemmas (u64 ⇄ Nat bridges) -/

private theorem u64_zero_toNat : ((0 : u64).toNat) = 0 := rfl
private theorem u64_one_toNat  : ((1 : u64).toNat) = 1 := rfl
private theorem u64_two_toNat  : ((2 : u64).toNat) = 2 := rfl

/-- `RustM.ok`-headed bind reduction.  The library's `pure_bind` simp lemma
    only matches literal `Pure.pure`; this rewrite handles the `RustM.ok`
    form that simp produces after reducing definitions. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

/-! ## Contract clauses derived from the Rust property tests.

The Rust source contains the following property-style tests; each becomes
one (or two) independent `theorem` below.

  * `matches_oracle`               — main bidirectional spec against a
    naive reference.  Captured by `is_simple_power_sound` together with
    `is_simple_power_actual_powers_recognized` (forward at the powers)
    and `is_simple_power_between_powers_not_recognized` (negative
    direction strictly between powers).
  * `one_is_always_simple_power`   — `x = 1`  → `true` for any `n`.
  * `zero_is_never_simple_power`   — `x = 0`  → `false` for any `n`.
  * `base_one_simple_power_iff_x_is_one`  — `n = 1` → `(x = 1)`.
  * `base_zero_simple_power_iff_x_is_one` — `n = 0` → `(x = 1)`.
  * `actual_powers_recognized`            — `n ≥ 2 ∧ n^k = x` → `true`.
  * `between_powers_not_recognized`       — `n ≥ 2 ∧ n^k < x < n^(k+1)`
    → `false` (with `n^(k+1) < 2^64` to rule out overflow).

### Feasibility notes

The body of `power_walks_to` repeatedly applies `cur ↦ cur *? n`, which
fails on `u64` overflow.  Three observations:

  1. The positive direction `actual_powers_recognized` is universally
     feasible: if `n.toNat ^ k = x.toNat`, then for every intermediate
     value `cur = n^i` with `i ≤ k` we have `n^i ≤ x < 2^64`, so the
     multiplicative chain never overflows.  No extra precondition
     beyond `n ≥ 2` is needed.
  2. The negative direction `between_powers_not_recognized` is *not*
     universal: when `n^(k+1) ≥ 2^64`, the recursion's last
     multiplication overflows and the function returns `.fail`, not
     `.ok false`.  We add the precondition `n^(k+1) < 2^64`, matching
     the proptest's `prop_assume!(hi ≤ u64::MAX as u128)`.
  3. Soundness (`ok true → ∃ k, n^k = x`) needs no precondition: if the
     function returns successfully with `true`, the chain of `cur`
     values witnesses the exponent. -/

/-- `x = 1` is a simple power of any `n` (via the `n^0 = 1` convention).
    Captures the proptest `one_is_always_simple_power`. -/
theorem is_simple_power_one (n : u64) :
    clever_075_is_simple_power.is_simple_power 1 n = RustM.ok true := by
  unfold clever_075_is_simple_power.is_simple_power
  simp only [show ((1 : u64) ==? (1 : u64)) =
                 (pure (decide ((1 : u64) = (1 : u64))) : RustM Bool) from rfl,
             pure_bind, decide_true, ↓reduceIte]
  rfl

/-- `0` is never a simple power of any `n`.  Captures the proptest
    `zero_is_never_simple_power`. -/
theorem is_simple_power_zero (n : u64) :
    clever_075_is_simple_power.is_simple_power 0 n = RustM.ok false := by
  unfold clever_075_is_simple_power.is_simple_power
  -- (0 ==? 1) = pure false
  simp only [show ((0 : u64) ==? (1 : u64)) =
                 (pure (decide ((0 : u64) = (1 : u64))) : RustM Bool) from rfl,
             pure_bind, show (decide ((0 : u64) = (1 : u64))) = false from rfl,
             Bool.false_eq_true, ↓reduceIte]
  -- (0 ==? 0) = pure true, then or with anything is true
  simp only [show ((0 : u64) ==? (0 : u64)) =
                 (pure (decide ((0 : u64) = (0 : u64))) : RustM Bool) from rfl,
             show (decide ((0 : u64) = (0 : u64))) = true from rfl,
             pure_bind]
  -- now have (true ||? _) >>= ...
  simp only [rust_primitives.hax.logical_op.or, Bool.true_or, pure_bind,
             ↓reduceIte]
  rfl

/-- Base `n = 1`: only `x = 1` qualifies (since `1^k = 1` for all `k`).
    Together with `is_simple_power_one` this captures the proptest
    `base_one_simple_power_iff_x_is_one`. -/
theorem is_simple_power_base_one_ne (x : u64) (h : x ≠ 1) :
    clever_075_is_simple_power.is_simple_power x 1 = RustM.ok false := by
  unfold clever_075_is_simple_power.is_simple_power
  have h_x1_false : decide (x = (1 : u64)) = false := decide_eq_false h
  simp only [show (x ==? (1 : u64)) =
                 (pure (decide (x = (1 : u64))) : RustM Bool) from rfl,
             pure_bind, h_x1_false, Bool.false_eq_true, ↓reduceIte]
  have h_10_false : decide ((1 : u64) = (0 : u64)) = false := by decide
  simp only [show ((1 : u64) ==? (0 : u64)) =
                 (pure (decide ((1 : u64) = (0 : u64))) : RustM Bool) from rfl,
             show (x ==? (0 : u64)) =
                 (pure (decide (x = (0 : u64))) : RustM Bool) from rfl,
             h_10_false, pure_bind,
             rust_primitives.hax.logical_op.or, Bool.or_false]
  by_cases hx : x = 0
  · have h_x0_true : decide (x = (0 : u64)) = true := decide_eq_true hx
    simp only [h_x0_true, ↓reduceIte]
    rfl
  · have h_x0_false : decide (x = (0 : u64)) = false := decide_eq_false hx
    simp only [h_x0_false, Bool.false_eq_true, ↓reduceIte]
    simp only [show ((1 : u64) ==? (1 : u64)) =
                   (pure (decide ((1 : u64) = (1 : u64))) : RustM Bool) from rfl,
               show (decide ((1 : u64) = (1 : u64))) = true from rfl,
               pure_bind, ↓reduceIte]
    rfl

/-- Base `n = 0`: only `x = 1` qualifies (via the `0^0 = 1` convention).
    Together with `is_simple_power_one` this captures the proptest
    `base_zero_simple_power_iff_x_is_one`. -/
theorem is_simple_power_base_zero_ne (x : u64) (h : x ≠ 1) :
    clever_075_is_simple_power.is_simple_power x 0 = RustM.ok false := by
  unfold clever_075_is_simple_power.is_simple_power
  have h_x1_false : decide (x = (1 : u64)) = false := decide_eq_false h
  simp only [show (x ==? (1 : u64)) =
                 (pure (decide (x = (1 : u64))) : RustM Bool) from rfl,
             pure_bind, h_x1_false, Bool.false_eq_true, ↓reduceIte]
  -- (0 ==? 0) is true, so OR is true regardless of x ==? 0
  simp only [show ((0 : u64) ==? (0 : u64)) =
                 (pure (decide ((0 : u64) = (0 : u64))) : RustM Bool) from rfl,
             show (x ==? (0 : u64)) =
                 (pure (decide (x = (0 : u64))) : RustM Bool) from rfl,
             show (decide ((0 : u64) = (0 : u64))) = true from rfl,
             pure_bind,
             rust_primitives.hax.logical_op.or, Bool.or_true,
             decide_true, ↓reduceIte]
  rfl

/-! ## Branch lemmas for `power_walks_to`.

Three reductions of the recursive definition: terminate on match,
return false on overshoot, recurse on undershoot (when the
multiplication doesn't overflow). -/

private theorem power_walks_to_terminate (x n cur : u64) (h : cur = x) :
    clever_075_is_simple_power.power_walks_to x n cur = RustM.ok true := by
  conv => lhs; unfold clever_075_is_simple_power.power_walks_to
  have h_eq : decide (cur = x) = true := decide_eq_true h
  simp only [show (cur ==? x) =
                 (pure (decide (cur = x)) : RustM Bool) from rfl,
             pure_bind, h_eq, ↓reduceIte]
  rfl

private theorem power_walks_to_overshoot (x n cur : u64)
    (h : x.toNat < cur.toNat) :
    clever_075_is_simple_power.power_walks_to x n cur = RustM.ok false := by
  conv => lhs; unfold clever_075_is_simple_power.power_walks_to
  have h_ne : ¬ cur = x := by
    intro he
    have : cur.toNat = x.toNat := by rw [he]
    omega
  have h_gt : cur > x := UInt64.lt_iff_toNat_lt.mpr h
  have h_dec_eq : decide (cur = x) = false := decide_eq_false h_ne
  have h_dec_gt : decide (cur > x) = true := decide_eq_true h_gt
  simp only [show (cur ==? x) =
                 (pure (decide (cur = x)) : RustM Bool) from rfl,
             show (cur >? x) =
                 (pure (decide (cur > x)) : RustM Bool) from rfl,
             pure_bind, h_dec_eq, h_dec_gt, Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem power_walks_to_step (x n cur : u64)
    (h_lt : cur.toNat < x.toNat)
    (h_no_ov : cur.toNat * n.toNat < 2 ^ 64) :
    clever_075_is_simple_power.power_walks_to x n cur =
      clever_075_is_simple_power.power_walks_to x n (cur * n) := by
  conv => lhs; unfold clever_075_is_simple_power.power_walks_to
  have h_ne : ¬ cur = x := by
    intro he
    have : cur.toNat = x.toNat := by rw [he]
    omega
  have h_not_gt : ¬ cur > x := by
    intro hgt
    have := UInt64.lt_iff_toNat_lt.mp hgt
    omega
  have h_dec_eq : decide (cur = x) = false := decide_eq_false h_ne
  have h_dec_gt : decide (cur > x) = false := decide_eq_false h_not_gt
  simp only [show (cur ==? x) =
                 (pure (decide (cur = x)) : RustM Bool) from rfl,
             show (cur >? x) =
                 (pure (decide (cur > x)) : RustM Bool) from rfl,
             pure_bind, h_dec_eq, h_dec_gt, Bool.false_eq_true, ↓reduceIte]
  -- Reduce cur *? n
  have h_no_ov_iff : ¬ UInt64.mulOverflow cur n := by
    rw [UInt64.mulOverflow_iff]; omega
  have h_bv : BitVec.umulOverflow cur.toBitVec n.toBitVec = false := by
    cases hb : BitVec.umulOverflow cur.toBitVec n.toBitVec with
    | false => rfl
    | true => exact absurd hb h_no_ov_iff
  have h_mul_pure : (cur *? n : RustM u64) = pure (cur * n) := by
    show (rust_primitives.ops.arith.Mul.mul cur n : RustM u64) = pure (cur * n)
    show (if BitVec.umulOverflow cur.toBitVec n.toBitVec then
            (.fail .integerOverflow : RustM u64)
          else pure (cur * n)) = pure (cur * n)
    rw [h_bv]; rfl
  rw [h_mul_pure]
  simp only [pure_bind]

/-- If `cur *? n` overflows and `cur < x`, then `power_walks_to` fails. -/
private theorem power_walks_to_step_fail (x n cur : u64)
    (h_lt : cur.toNat < x.toNat)
    (h_ov : 2 ^ 64 ≤ cur.toNat * n.toNat) :
    clever_075_is_simple_power.power_walks_to x n cur =
      .fail .integerOverflow := by
  conv => lhs; unfold clever_075_is_simple_power.power_walks_to
  have h_ne : ¬ cur = x := by
    intro he
    have : cur.toNat = x.toNat := by rw [he]
    omega
  have h_not_gt : ¬ cur > x := by
    intro hgt
    have := UInt64.lt_iff_toNat_lt.mp hgt
    omega
  have h_dec_eq : decide (cur = x) = false := decide_eq_false h_ne
  have h_dec_gt : decide (cur > x) = false := decide_eq_false h_not_gt
  simp only [show (cur ==? x) =
                 (pure (decide (cur = x)) : RustM Bool) from rfl,
             show (cur >? x) =
                 (pure (decide (cur > x)) : RustM Bool) from rfl,
             pure_bind, h_dec_eq, h_dec_gt, Bool.false_eq_true, ↓reduceIte]
  have h_ov_iff : UInt64.mulOverflow cur n := by
    rw [UInt64.mulOverflow_iff]; exact h_ov
  have h_bv : BitVec.umulOverflow cur.toBitVec n.toBitVec = true := h_ov_iff
  have h_mul_fail : (cur *? n : RustM u64) = .fail .integerOverflow := by
    show (rust_primitives.ops.arith.Mul.mul cur n : RustM u64) = .fail .integerOverflow
    show (if BitVec.umulOverflow cur.toBitVec n.toBitVec then
            (.fail .integerOverflow : RustM u64)
          else pure (cur * n)) = _
    rw [h_bv]; rfl
  rw [h_mul_fail]
  rfl

/-! ## Soundness workhorse.

If `power_walks_to x n cur` returns `ok true` with `n ≥ 2` and `cur ≥ 1`,
then there is some `m` with `cur.toNat * n.toNat^m = x.toNat`.
Strong induction on the measure `x.toNat - cur.toNat`. -/

private theorem power_walks_to_sound_aux (x n : u64) (h_n : 2 ≤ n.toNat) :
    ∀ (m : Nat) (cur : u64),
      x.toNat - cur.toNat ≤ m →
      1 ≤ cur.toNat →
      clever_075_is_simple_power.power_walks_to x n cur = RustM.ok true →
      ∃ k : Nat, cur.toNat * n.toNat ^ k = x.toNat := by
  intro m
  induction m with
  | zero =>
    intro cur h_le h_cur h_call
    -- m = 0 means x.toNat ≤ cur.toNat
    have h_le' : x.toNat ≤ cur.toNat := by omega
    rcases Nat.eq_or_lt_of_le h_le' with h_eq | h_lt
    · refine ⟨0, ?_⟩
      rw [Nat.pow_zero, Nat.mul_one]
      exact h_eq.symm
    · -- x < cur: overshoot, contradiction
      rw [power_walks_to_overshoot x n cur h_lt] at h_call
      cases h_call
  | succ m ih =>
    intro cur h_le h_cur h_call
    rcases Nat.lt_trichotomy cur.toNat x.toNat with h_lt | h_eq | h_gt
    · -- cur < x: must recurse
      by_cases h_ov : cur.toNat * n.toNat < 2 ^ 64
      · -- no overflow: function equals power_walks_to x n (cur * n)
        rw [power_walks_to_step x n cur h_lt h_ov] at h_call
        have h_cur_new_toNat : (cur * n).toNat = cur.toNat * n.toNat :=
          UInt64.toNat_mul_of_lt h_ov
        have h_n_pos : 1 ≤ n.toNat := by omega
        have h_cur_new_pos : 1 ≤ (cur * n).toNat := by
          rw [h_cur_new_toNat]
          have : 1 * 1 ≤ cur.toNat * n.toNat := Nat.mul_le_mul h_cur h_n_pos
          omega
        have h_strictly_more : cur.toNat < (cur * n).toNat := by
          rw [h_cur_new_toNat]
          have h_lt_mul : cur.toNat * 1 < cur.toNat * n.toNat :=
            Nat.mul_lt_mul_of_pos_left (by omega) h_cur
          omega
        have h_new_le : x.toNat - (cur * n).toNat ≤ m := by omega
        rcases ih (cur * n) h_new_le h_cur_new_pos h_call with ⟨k, hk⟩
        refine ⟨k + 1, ?_⟩
        rw [h_cur_new_toNat] at hk
        -- hk : cur.toNat * n.toNat * n.toNat^k = x.toNat
        -- Goal: cur.toNat * n.toNat^(k+1) = x.toNat
        rw [Nat.pow_succ,
            show n.toNat^k * n.toNat = n.toNat * n.toNat^k from Nat.mul_comm _ _,
            ← Nat.mul_assoc]
        exact hk
      · -- overflow: function fails, contradiction
        have h_ov_le : 2 ^ 64 ≤ cur.toNat * n.toNat := Nat.le_of_not_lt h_ov
        rw [power_walks_to_step_fail x n cur h_lt h_ov_le] at h_call
        cases h_call
    · -- cur = x: witness exponent 0
      refine ⟨0, ?_⟩
      rw [Nat.pow_zero, Nat.mul_one]
      exact h_eq
    · -- cur > x: function returns false, contradiction with ok true
      rw [power_walks_to_overshoot x n cur h_gt] at h_call
      cases h_call

/-- Soundness half of `matches_oracle`: if the function returns `true`,
    there is some `k : Nat` with `n^k = x` at the `Nat` level.  No
    precondition: a successful `ok true` already constrains the trace
    of `cur` values to expose the witness. -/
theorem is_simple_power_sound (x n : u64)
    (h : clever_075_is_simple_power.is_simple_power x n = RustM.ok true) :
    ∃ k : Nat, n.toNat ^ k = x.toNat := by
  unfold clever_075_is_simple_power.is_simple_power at h
  -- Case x = 1: witness k = 0
  by_cases hx1 : x = (1 : u64)
  · refine ⟨0, ?_⟩
    rw [Nat.pow_zero, hx1, u64_one_toNat]
  have h_x1_false : decide (x = (1 : u64)) = false := decide_eq_false hx1
  simp only [show (x ==? (1 : u64)) =
                 (pure (decide (x = (1 : u64))) : RustM Bool) from rfl,
             pure_bind, h_x1_false, Bool.false_eq_true, ↓reduceIte] at h
  -- Now we case-split on (x = 0 ∨ n = 0)
  simp only [show (x ==? (0 : u64)) =
                 (pure (decide (x = (0 : u64))) : RustM Bool) from rfl,
             show (n ==? (0 : u64)) =
                 (pure (decide (n = (0 : u64))) : RustM Bool) from rfl,
             pure_bind, rust_primitives.hax.logical_op.or] at h
  by_cases hx0 : x = (0 : u64)
  · have h_x0_true : decide (x = (0 : u64)) = true := decide_eq_true hx0
    simp only [h_x0_true, Bool.true_or, ↓reduceIte] at h
    cases h
  have h_x0_false : decide (x = (0 : u64)) = false := decide_eq_false hx0
  simp only [h_x0_false, Bool.false_or] at h
  by_cases hn0 : n = (0 : u64)
  · have h_n0_true : decide (n = (0 : u64)) = true := decide_eq_true hn0
    simp only [h_n0_true, ↓reduceIte] at h
    cases h
  have h_n0_false : decide (n = (0 : u64)) = false := decide_eq_false hn0
  simp only [h_n0_false, Bool.false_eq_true, ↓reduceIte] at h
  -- Now (n ==? 1)
  simp only [show (n ==? (1 : u64)) =
                 (pure (decide (n = (1 : u64))) : RustM Bool) from rfl,
             pure_bind] at h
  by_cases hn1 : n = (1 : u64)
  · have h_n1_true : decide (n = (1 : u64)) = true := decide_eq_true hn1
    simp only [h_n1_true, ↓reduceIte] at h
    cases h
  have h_n1_false : decide (n = (1 : u64)) = false := decide_eq_false hn1
  simp only [h_n1_false, Bool.false_eq_true, ↓reduceIte] at h
  -- Now h : power_walks_to x n n = ok true. We have n ≠ 0, n ≠ 1, so n.toNat ≥ 2.
  have h_n_ge_2 : 2 ≤ n.toNat := by
    have h_n_ne0 : n.toNat ≠ 0 := by
      intro hz
      apply hn0
      apply UInt64.toNat_inj.mp
      rw [hz, u64_zero_toNat]
    have h_n_ne1 : n.toNat ≠ 1 := by
      intro hz
      apply hn1
      apply UInt64.toNat_inj.mp
      rw [hz, u64_one_toNat]
    omega
  have h_n_pos : 1 ≤ n.toNat := by omega
  rcases power_walks_to_sound_aux x n h_n_ge_2 (x.toNat - n.toNat) n
      (Nat.le_refl _) h_n_pos h
    with ⟨k, hk⟩
  -- hk : n.toNat * n.toNat^k = x.toNat
  refine ⟨k + 1, ?_⟩
  -- Goal: n.toNat^(k+1) = x.toNat
  rw [Nat.pow_succ, Nat.mul_comm (n.toNat^k) n.toNat]
  exact hk

/-! ## Completeness workhorse for the actual-powers direction.

If `cur = n^i` for some `i ≤ k`, then `power_walks_to x n cur = ok true`
where `n^k = x`. Induction on the bound `k - i`. -/

private theorem power_walks_to_complete (x n : u64) (k : Nat)
    (h_n : 2 ≤ n.toNat) (h_eq : n.toNat ^ k = x.toNat) :
    ∀ (m : Nat) (i : Nat) (cur : u64),
      i ≤ k →
      k - i ≤ m →
      cur.toNat = n.toNat ^ i →
      clever_075_is_simple_power.power_walks_to x n cur = RustM.ok true := by
  intro m
  induction m with
  | zero =>
    intro i cur h_i_le_k h_m h_cur_eq
    -- m = 0: k ≤ i, so i = k
    have h_i_eq_k : i = k := by omega
    apply power_walks_to_terminate
    apply UInt64.toNat_inj.mp
    rw [h_cur_eq, h_i_eq_k, h_eq]
  | succ m ih =>
    intro i cur h_i_le_k h_m h_cur_eq
    by_cases h_i_eq_k : i = k
    · apply power_walks_to_terminate
      apply UInt64.toNat_inj.mp
      rw [h_cur_eq, h_i_eq_k, h_eq]
    · have h_i_lt_k : i < k := by omega
      have h_n_pos : 1 ≤ n.toNat := by omega
      have h_cur_lt : cur.toNat < x.toNat := by
        rw [h_cur_eq, ← h_eq]
        exact Nat.pow_lt_pow_right (by omega : 1 < n.toNat) h_i_lt_k
      have h_cur_n_eq : cur.toNat * n.toNat = n.toNat ^ (i + 1) := by
        rw [h_cur_eq, ← Nat.pow_succ]
      have h_cur_n_le : cur.toNat * n.toNat ≤ x.toNat := by
        rw [h_cur_n_eq, ← h_eq]
        exact Nat.pow_le_pow_right h_n_pos (by omega)
      have h_no_ov : cur.toNat * n.toNat < 2 ^ 64 := by
        have h_x_lt : x.toNat < 2 ^ 64 := x.toNat_lt
        omega
      rw [power_walks_to_step x n cur h_cur_lt h_no_ov]
      have h_cur_new_toNat : (cur * n).toNat = cur.toNat * n.toNat :=
        UInt64.toNat_mul_of_lt h_no_ov
      apply ih (i + 1) (cur * n) (by omega) (by omega)
      rw [h_cur_new_toNat, h_cur_n_eq]

/-- Positive direction: every actual power `n^k` is recognized for
    `n ≥ 2`.  Captures the proptest `actual_powers_recognized` and
    also serves as the completeness half of `matches_oracle` in the
    principal case (the `n = 0, 1` cases are covered by the dedicated
    edge clauses).  Universal: `n^i ≤ n^k = x < 2^64` rules out
    overflow during the chain. -/
theorem is_simple_power_actual_powers_recognized (x n : u64) (k : Nat)
    (h_n : 2 ≤ n.toNat) (h_eq : n.toNat ^ k = x.toNat) :
    clever_075_is_simple_power.is_simple_power x n = RustM.ok true := by
  by_cases hk : k = 0
  · -- x = 1
    have h_x_eq_1 : x.toNat = 1 := by rw [← h_eq, hk]; rfl
    have hx : x = 1 := by
      apply UInt64.toNat_inj.mp
      rw [h_x_eq_1, u64_one_toNat]
    rw [hx]
    exact is_simple_power_one n
  · -- k ≥ 1
    have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have h_n_pos : 1 ≤ n.toNat := by omega
    have h_x_ge_n : n.toNat ≤ x.toNat := by
      rw [← h_eq]
      have h_pow_le : n.toNat ^ 1 ≤ n.toNat ^ k :=
        Nat.pow_le_pow_right h_n_pos hk_pos
      simpa [Nat.pow_one] using h_pow_le
    have h_x_ge_2 : 2 ≤ x.toNat := Nat.le_trans h_n h_x_ge_n
    have hx1_ne : x ≠ (1 : u64) := by
      intro h
      have h_eq1 : x.toNat = (1 : u64).toNat := by rw [h]
      rw [u64_one_toNat] at h_eq1; omega
    have hx0_ne : x ≠ (0 : u64) := by
      intro h
      have h_eq0 : x.toNat = (0 : u64).toNat := by rw [h]
      rw [u64_zero_toNat] at h_eq0; omega
    have hn0_ne : n ≠ (0 : u64) := by
      intro h
      have h_eq0 : n.toNat = (0 : u64).toNat := by rw [h]
      rw [u64_zero_toNat] at h_eq0; omega
    have hn1_ne : n ≠ (1 : u64) := by
      intro h
      have h_eq1 : n.toNat = (1 : u64).toNat := by rw [h]
      rw [u64_one_toNat] at h_eq1; omega
    unfold clever_075_is_simple_power.is_simple_power
    have h_x1_false : decide (x = (1 : u64)) = false := decide_eq_false hx1_ne
    simp only [show (x ==? (1 : u64)) =
                   (pure (decide (x = (1 : u64))) : RustM Bool) from rfl,
               pure_bind, h_x1_false, Bool.false_eq_true, ↓reduceIte]
    have h_x0_false : decide (x = (0 : u64)) = false := decide_eq_false hx0_ne
    have h_n0_false : decide (n = (0 : u64)) = false := decide_eq_false hn0_ne
    simp only [show (x ==? (0 : u64)) =
                   (pure (decide (x = (0 : u64))) : RustM Bool) from rfl,
               show (n ==? (0 : u64)) =
                   (pure (decide (n = (0 : u64))) : RustM Bool) from rfl,
               pure_bind, h_x0_false, h_n0_false,
               rust_primitives.hax.logical_op.or, Bool.or_self,
               Bool.false_eq_true, ↓reduceIte]
    have h_n1_false : decide (n = (1 : u64)) = false := decide_eq_false hn1_ne
    simp only [show (n ==? (1 : u64)) =
                   (pure (decide (n = (1 : u64))) : RustM Bool) from rfl,
               pure_bind, h_n1_false, Bool.false_eq_true, ↓reduceIte]
    -- Apply power_walks_to_complete with cur = n, i = 1
    apply power_walks_to_complete x n k h_n h_eq (k - 1) 1 n hk_pos
      (Nat.le_refl _) (by rw [Nat.pow_one])

/-! ## Negative direction workhorse for the between-powers case.

If `cur = n^i` for some `i ≤ k + 1`, then `power_walks_to x n cur = ok false`
when `n^k < x < n^(k+1)` and `n^(k+1) < 2^64`.  Induction on the bound
`k + 1 - i`. -/

private theorem power_walks_to_between (x n : u64) (k : Nat)
    (h_n : 2 ≤ n.toNat)
    (h_lo : n.toNat ^ k < x.toNat)
    (h_hi : x.toNat < n.toNat ^ (k + 1))
    (h_fit : n.toNat ^ (k + 1) < 2 ^ 64) :
    ∀ (m : Nat) (i : Nat) (cur : u64),
      i ≤ k + 1 →
      (k + 1) - i ≤ m →
      cur.toNat = n.toNat ^ i →
      clever_075_is_simple_power.power_walks_to x n cur = RustM.ok false := by
  intro m
  induction m with
  | zero =>
    intro i cur h_i_le h_m h_cur_eq
    -- m = 0: k + 1 ≤ i ≤ k + 1, so i = k + 1
    have h_i_eq : i = k + 1 := by omega
    apply power_walks_to_overshoot
    rw [h_cur_eq, h_i_eq]
    exact h_hi
  | succ m ih =>
    intro i cur h_i_le h_m h_cur_eq
    by_cases h_i_eq : i = k + 1
    · apply power_walks_to_overshoot
      rw [h_cur_eq, h_i_eq]
      exact h_hi
    · have h_i_le_k : i ≤ k := by omega
      have h_n_pos : 1 ≤ n.toNat := by omega
      have h_cur_le_pow_k : cur.toNat ≤ n.toNat ^ k := by
        rw [h_cur_eq]
        exact Nat.pow_le_pow_right h_n_pos h_i_le_k
      have h_cur_lt : cur.toNat < x.toNat := by omega
      have h_cur_n_eq : cur.toNat * n.toNat = n.toNat ^ (i + 1) := by
        rw [h_cur_eq, ← Nat.pow_succ]
      have h_cur_n_le_pow : cur.toNat * n.toNat ≤ n.toNat ^ (k + 1) := by
        rw [h_cur_n_eq]
        exact Nat.pow_le_pow_right h_n_pos (by omega)
      have h_no_ov : cur.toNat * n.toNat < 2 ^ 64 := by omega
      rw [power_walks_to_step x n cur h_cur_lt h_no_ov]
      have h_cur_new_toNat : (cur * n).toNat = cur.toNat * n.toNat :=
        UInt64.toNat_mul_of_lt h_no_ov
      apply ih (i + 1) (cur * n) (by omega) (by omega)
      rw [h_cur_new_toNat, h_cur_n_eq]

/-- Negative direction: a value strictly between consecutive powers
    `n^k` and `n^(k+1)` is not a simple power of `n`.  The
    precondition `n^(k+1) < 2^64` mirrors the proptest's
    `prop_assume!(hi ≤ u64::MAX as u128)` and rules out the genuine
    overflow case the natural universal statement omits.  Captures the
    proptest `between_powers_not_recognized`. -/
theorem is_simple_power_between_powers_not_recognized (x n : u64) (k : Nat)
    (h_n : 2 ≤ n.toNat)
    (h_lo : n.toNat ^ k < x.toNat)
    (h_hi : x.toNat < n.toNat ^ (k + 1))
    (h_fit : n.toNat ^ (k + 1) < 2 ^ 64) :
    clever_075_is_simple_power.is_simple_power x n = RustM.ok false := by
  have h_n_pos : 1 ≤ n.toNat := by omega
  have h_pow_k_pos : 0 < n.toNat ^ k := Nat.pow_pos h_n_pos
  have h_x_ge_2 : 2 ≤ x.toNat := by omega
  have hx1_ne : x ≠ (1 : u64) := by
    intro h
    have h_eq1 : x.toNat = (1 : u64).toNat := by rw [h]
    rw [u64_one_toNat] at h_eq1; omega
  have hx0_ne : x ≠ (0 : u64) := by
    intro h
    have h_eq0 : x.toNat = (0 : u64).toNat := by rw [h]
    rw [u64_zero_toNat] at h_eq0; omega
  have hn0_ne : n ≠ (0 : u64) := by
    intro h
    have h_eq0 : n.toNat = (0 : u64).toNat := by rw [h]
    rw [u64_zero_toNat] at h_eq0; omega
  have hn1_ne : n ≠ (1 : u64) := by
    intro h
    have h_eq1 : n.toNat = (1 : u64).toNat := by rw [h]
    rw [u64_one_toNat] at h_eq1; omega
  unfold clever_075_is_simple_power.is_simple_power
  have h_x1_false : decide (x = (1 : u64)) = false := decide_eq_false hx1_ne
  simp only [show (x ==? (1 : u64)) =
                 (pure (decide (x = (1 : u64))) : RustM Bool) from rfl,
             pure_bind, h_x1_false, Bool.false_eq_true, ↓reduceIte]
  have h_x0_false : decide (x = (0 : u64)) = false := decide_eq_false hx0_ne
  have h_n0_false : decide (n = (0 : u64)) = false := decide_eq_false hn0_ne
  simp only [show (x ==? (0 : u64)) =
                 (pure (decide (x = (0 : u64))) : RustM Bool) from rfl,
             show (n ==? (0 : u64)) =
                 (pure (decide (n = (0 : u64))) : RustM Bool) from rfl,
             pure_bind, h_x0_false, h_n0_false,
             rust_primitives.hax.logical_op.or, Bool.or_self,
             Bool.false_eq_true, ↓reduceIte]
  have h_n1_false : decide (n = (1 : u64)) = false := decide_eq_false hn1_ne
  simp only [show (n ==? (1 : u64)) =
                 (pure (decide (n = (1 : u64))) : RustM Bool) from rfl,
             pure_bind, h_n1_false, Bool.false_eq_true, ↓reduceIte]
  -- Apply power_walks_to_between with cur = n, i = 1
  apply power_walks_to_between x n k h_n h_lo h_hi h_fit (k + 1 - 1) 1 n
    (by omega) (Nat.le_refl _) (by rw [Nat.pow_one])

/-! ## Unit pins from the `small_cases` test.

These are sanity pins on specific values.  They are derivable from the
universal clauses above, but pinning them as separate theorems guards
against regressions on the specific examples listed in the Rust
`small_cases` test. -/

/-- `is_simple_power(8, 2) = true` (since `2³ = 8`). -/
theorem is_simple_power_8_2 :
    clever_075_is_simple_power.is_simple_power 8 2 = RustM.ok true := by
  native_decide

/-- `is_simple_power(81, 3) = true` (since `3⁴ = 81`). -/
theorem is_simple_power_81_3 :
    clever_075_is_simple_power.is_simple_power 81 3 = RustM.ok true := by
  native_decide

/-- `is_simple_power(3, 2) = false`. -/
theorem is_simple_power_3_2 :
    clever_075_is_simple_power.is_simple_power 3 2 = RustM.ok false := by
  native_decide

/-- `is_simple_power(7, 4) = false`. -/
theorem is_simple_power_7_4 :
    clever_075_is_simple_power.is_simple_power 7 4 = RustM.ok false := by
  native_decide

end Clever_075_is_simple_powerObligations
