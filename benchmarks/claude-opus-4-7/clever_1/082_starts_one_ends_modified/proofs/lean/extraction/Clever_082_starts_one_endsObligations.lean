-- Companion obligations file for the `clever_082_starts_one_ends` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_082_starts_one_ends

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_082_starts_one_endsObligations

/-! ## Helpers reused below. -/

private theorem u64_zero_toNat : ((0 : u64).toNat) = 0 := rfl
private theorem u64_one_toNat  : ((1 : u64).toNat) = 1 := rfl
private theorem u64_two_toNat  : ((2 : u64).toNat) = 2 := rfl
private theorem u64_ten_toNat  : ((10 : u64).toNat) = 10 := rfl
private theorem u64_eighteen_toNat : ((18 : u64).toNat) = 18 := rfl

/-- `RustM.ok`-headed bind reduction.  The library's `pure_bind` simp lemma
    only matches literal `Pure.pure`; this rewrite handles the `RustM.ok`
    form that appears after the characterization rewrite. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

/-! ## Contract clauses

The Rust source contains the following contract-style tests:

  * `small_cases` — five unit pins: `starts_one_ends(0)=0`,
    `starts_one_ends(1)=1`, `starts_one_ends(2)=18`,
    `starts_one_ends(3)=180`, `starts_one_ends(4)=1800`.
  * `matches_brute_force (n in 0u64..=6)` — main postcondition: the
    closed form `18 · 10^(n-2)` agrees with an independent
    enumeration of "n-digit positives starting or ending with 1".
    For `n = 0` the convention is `0` and for `n = 1` only `1`
    qualifies, both of which are degenerate base cases.

Each becomes one independent `theorem`.

### Feasibility analysis

The body of `pow10_at` walks `acc ↦ acc *? 10` with `acc` starting
at `1`, so the intermediate values are `1, 10, 100, …, 10^(n-2)`.
The outer wrapper then multiplies by `18`.  The closed form
`18 · 10^(n-2)` fits in `u64` iff `n ≤ 20`:

  * `18 · 10^18 = 1.8·10^19 < 2^64 ≈ 1.84·10^19`  → succeeds at `n = 20`.
  * `18 · 10^19 = 1.8·10^20 > 2^64`               → overflows at `n = 21`.

For `n = 21` the inner `pow10_at(19, 1) = 10^19` still fits, but the
outer `18 *? 10^19` overflows; for `n ≥ 22` the inner walk itself
overflows when computing `10^20 = 10 · 10^19`.  Either way, the
function returns `.fail .integerOverflow` for every `n ≥ 21`.

We therefore state the closed-form postcondition with the explicit
range `2 ≤ n ≤ 20`, and a matching failure clause for `n ≥ 21`.
The proptest's range `0..=6` is a tiny slice of the true success
domain; the theorem we state is much stronger than the proptest. -/

/-! ## Unit pins from `small_cases`.

These literal values are independently asserted by the Rust test
suite.  Closing each with `native_decide` reduces the extracted
definition by kernel evaluation. -/

/-- Unit pin: `starts_one_ends(0) = 0`.  Base-case convention
    that `n = 0` yields no count. -/
theorem starts_one_ends_at_0 :
    clever_082_starts_one_ends.starts_one_ends 0 = RustM.ok 0 := by
  native_decide

/-- Unit pin: `starts_one_ends(1) = 1`.  Only `1` itself is a
    1-digit number that starts or ends with `1`. -/
theorem starts_one_ends_at_1 :
    clever_082_starts_one_ends.starts_one_ends 1 = RustM.ok 1 := by
  native_decide

/-- Unit pin: `starts_one_ends(2) = 18`.  Inclusion–exclusion at
    `n = 2` gives `18 · 10^0 = 18`. -/
theorem starts_one_ends_at_2 :
    clever_082_starts_one_ends.starts_one_ends 2 = RustM.ok 18 := by
  native_decide

/-- Unit pin: `starts_one_ends(3) = 180`.  Closed form at `n = 3`:
    `18 · 10^1 = 180`. -/
theorem starts_one_ends_at_3 :
    clever_082_starts_one_ends.starts_one_ends 3 = RustM.ok 180 := by
  native_decide

/-- Unit pin: `starts_one_ends(4) = 1800`.  Closed form at `n = 4`:
    `18 · 10^2 = 1800`. -/
theorem starts_one_ends_at_4 :
    clever_082_starts_one_ends.starts_one_ends 4 = RustM.ok 1800 := by
  native_decide

/-! ## Branch lemmas for `pow10_at` -/

/-- Base branch: when `k = 0`, the function returns `pure acc`. -/
private theorem pow10_at_base (acc : u64) :
    clever_082_starts_one_ends.pow10_at 0 acc = RustM.ok acc := by
  unfold clever_082_starts_one_ends.pow10_at
  simp only [show ((0 : u64) ==? (0 : u64)) =
                 (pure (decide ((0 : u64) = (0 : u64))) : RustM Bool) from rfl,
             pure_bind, decide_true, ↓reduceIte]
  rfl

/-- Recursive step: when `k ≠ 0` and `acc * 10` doesn't overflow,
    the function delegates to the recursive call with `acc * 10` and `k - 1`. -/
private theorem pow10_at_step (k acc : u64) (hk : k ≠ 0)
    (h_no_ov : acc.toNat * 10 < 2 ^ 64) :
    clever_082_starts_one_ends.pow10_at k acc =
      clever_082_starts_one_ends.pow10_at (k - 1) (acc * 10) := by
  conv => lhs; unfold clever_082_starts_one_ends.pow10_at
  have h_dec : decide (k = (0 : u64)) = false := decide_eq_false hk
  simp only [show (k ==? (0 : u64)) =
                 (pure (decide (k = (0 : u64))) : RustM Bool) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
  -- Reduce acc *? 10.
  have h_no_ov' : acc.toNat * (10 : u64).toNat < 2 ^ 64 := by
    rw [u64_ten_toNat]; exact h_no_ov
  have h_mul_no_overflow : ¬ UInt64.mulOverflow acc 10 := by
    rw [UInt64.mulOverflow_iff]; exact Nat.not_le.mpr h_no_ov'
  have h_bv_mul : BitVec.umulOverflow acc.toBitVec (10 : u64).toBitVec = false := by
    cases hb : BitVec.umulOverflow acc.toBitVec (10 : u64).toBitVec with
    | false => rfl
    | true => exact absurd hb h_mul_no_overflow
  have h_acc_mul : (acc *? (10 : u64) : RustM u64) = pure (acc * 10) := by
    show (rust_primitives.ops.arith.Mul.mul acc (10 : u64) : RustM u64) = pure (acc * 10)
    show (if BitVec.umulOverflow acc.toBitVec ((10 : u64).toBitVec) then
            (.fail .integerOverflow : RustM u64)
          else pure (acc * 10)) = pure (acc * 10)
    rw [h_bv_mul]; rfl
  rw [h_acc_mul]
  simp only [pure_bind]
  -- Reduce k -? 1.  k ≠ 0, so 1 ≤ k.toNat, so no underflow.
  have h_k_pos : 0 < k.toNat := by
    rcases Nat.eq_zero_or_pos k.toNat with h | h
    · exfalso; apply hk; apply UInt64.toNat_inj.mp; rw [h]; rfl
    · exact h
  have h_k_sub_no_underflow : ¬ UInt64.subOverflow k 1 := by
    rw [UInt64.subOverflow_iff, u64_one_toNat]
    omega
  have h_bv_sub : BitVec.usubOverflow k.toBitVec (1 : u64).toBitVec = false := by
    cases hb : BitVec.usubOverflow k.toBitVec (1 : u64).toBitVec with
    | false => rfl
    | true => exact absurd hb h_k_sub_no_underflow
  have h_k_sub : (k -? (1 : u64) : RustM u64) = pure (k - 1) := by
    show (rust_primitives.ops.arith.Sub.sub k (1 : u64) : RustM u64) = pure (k - 1)
    show (if BitVec.usubOverflow k.toBitVec ((1 : u64).toBitVec) then
            (.fail .integerOverflow : RustM u64)
          else pure (k - 1)) = pure (k - 1)
    rw [h_bv_sub]; rfl
  rw [h_k_sub]
  simp only [pure_bind]

/-- Step that fails: when `k ≠ 0` and `acc * 10` overflows, returns fail. -/
private theorem pow10_at_step_fail (k acc : u64) (hk : k ≠ 0)
    (h_ov : 2 ^ 64 ≤ acc.toNat * 10) :
    clever_082_starts_one_ends.pow10_at k acc = RustM.fail .integerOverflow := by
  conv => lhs; unfold clever_082_starts_one_ends.pow10_at
  have h_dec : decide (k = (0 : u64)) = false := decide_eq_false hk
  simp only [show (k ==? (0 : u64)) =
                 (pure (decide (k = (0 : u64))) : RustM Bool) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
  -- First reduce k -? 1.
  have h_k_pos : 0 < k.toNat := by
    rcases Nat.eq_zero_or_pos k.toNat with h | h
    · exfalso; apply hk; apply UInt64.toNat_inj.mp; rw [h]; rfl
    · exact h
  have h_k_sub_no_underflow : ¬ UInt64.subOverflow k 1 := by
    rw [UInt64.subOverflow_iff, u64_one_toNat]
    omega
  have h_bv_sub : BitVec.usubOverflow k.toBitVec (1 : u64).toBitVec = false := by
    cases hb : BitVec.usubOverflow k.toBitVec (1 : u64).toBitVec with
    | false => rfl
    | true => exact absurd hb h_k_sub_no_underflow
  have h_k_sub : (k -? (1 : u64) : RustM u64) = pure (k - 1) := by
    show (rust_primitives.ops.arith.Sub.sub k (1 : u64) : RustM u64) = pure (k - 1)
    show (if BitVec.usubOverflow k.toBitVec ((1 : u64).toBitVec) then
            (.fail .integerOverflow : RustM u64)
          else pure (k - 1)) = pure (k - 1)
    rw [h_bv_sub]; rfl
  rw [h_k_sub]
  simp only [pure_bind]
  -- Now reduce acc *? 10 = fail.
  have h_ov' : 2 ^ 64 ≤ acc.toNat * (10 : u64).toNat := by
    rw [u64_ten_toNat]; exact h_ov
  have h_mul_overflow : UInt64.mulOverflow acc 10 := by
    rw [UInt64.mulOverflow_iff]; exact h_ov'
  have h_bv_mul : BitVec.umulOverflow acc.toBitVec (10 : u64).toBitVec = true := h_mul_overflow
  have h_acc_mul : (acc *? (10 : u64) : RustM u64) = RustM.fail .integerOverflow := by
    show (rust_primitives.ops.arith.Mul.mul acc (10 : u64) : RustM u64) = RustM.fail .integerOverflow
    show (if BitVec.umulOverflow acc.toBitVec ((10 : u64).toBitVec) then
            (.fail .integerOverflow : RustM u64)
          else pure (acc * 10)) = _
    rw [h_bv_mul]; rfl
  rw [h_acc_mul]
  rfl

/-! ## Main characterization of `pow10_at`.

Strong induction on `k.toNat`.  The function returns `ok (acc * 10^k)`
when the closed-form product fits in `u64`, and `fail` otherwise. -/

private theorem pow10_at_compute (k acc : u64) :
    clever_082_starts_one_ends.pow10_at k acc =
      if acc.toNat * 10 ^ k.toNat < 2 ^ 64 then
        RustM.ok (UInt64.ofNat (acc.toNat * 10 ^ k.toNat))
      else
        RustM.fail .integerOverflow := by
  induction hkm : k.toNat using Nat.strongRecOn generalizing k acc with
  | _ m ih =>
    by_cases hk0 : k = 0
    · -- Base case: k = 0.
      subst hk0
      have hm0 : m = 0 := by
        have h := hkm; rw [u64_zero_toNat] at h; omega
      subst hm0
      have h_acc_lt : acc.toNat < 2 ^ 64 := acc.toNat_lt
      rw [pow10_at_base]
      simp only [Nat.pow_zero, Nat.mul_one]
      rw [if_pos h_acc_lt]
      congr 1
      apply UInt64.toNat_inj.mp
      show acc.toNat = (BitVec.ofNat 64 acc.toNat).toNat
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_acc_lt]
    · -- Step case: k ≠ 0.
      have h_k_pos : 0 < k.toNat := by
        rcases Nat.eq_zero_or_pos k.toNat with h | h
        · exfalso; apply hk0; apply UInt64.toNat_inj.mp; rw [h]; rfl
        · exact h
      -- Substitute m = k.toNat for clean rewriting.
      have h_m_eq : m = k.toNat := hkm.symm
      have h_pow_succ : 10 ^ k.toNat = 10 ^ (k.toNat - 1) * 10 := by
        obtain ⟨p, hp⟩ : ∃ p, k.toNat = p + 1 := ⟨k.toNat - 1, by omega⟩
        rw [hp]
        have hp' : p + 1 - 1 = p := by omega
        rw [hp', Nat.pow_succ]
      by_cases h_step_ov : acc.toNat * 10 < 2 ^ 64
      · -- Step succeeds: peel one call, apply IH.
        rw [pow10_at_step k acc hk0 h_step_ov]
        have h_acc_mul_toNat : (acc * 10).toNat = acc.toNat * 10 := by
          have h : acc.toNat * (10 : u64).toNat < 2 ^ 64 := by
            rw [u64_ten_toNat]; exact h_step_ov
          rw [UInt64.toNat_mul_of_lt h, u64_ten_toNat]
        have h_k_sub_toNat : (k - 1).toNat = k.toNat - 1 := by
          have h_one_le : (1 : u64).toNat ≤ k.toNat := by rw [u64_one_toNat]; omega
          rw [UInt64.toNat_sub_of_le' h_one_le, u64_one_toNat]
        have h_k_sub_lt : (k - 1).toNat < m := by
          rw [h_k_sub_toNat, ← hkm]; omega
        rw [ih (k - 1).toNat h_k_sub_lt (k - 1) (acc * 10) rfl]
        -- Now rewrite m to k.toNat on the RHS and show both sides equal.
        rw [h_m_eq]
        have h_pow_eq : (acc * 10).toNat * 10 ^ (k - 1).toNat =
            acc.toNat * 10 ^ k.toNat := by
          rw [h_acc_mul_toNat, h_k_sub_toNat, h_pow_succ]
          -- Goal: acc.toNat * 10 * 10^(k-1) = acc.toNat * (10^(k-1) * 10)
          rw [Nat.mul_assoc acc.toNat 10 _,
              Nat.mul_comm 10 (10 ^ (k.toNat - 1))]
        rw [h_pow_eq]
      · -- Step fails: acc * 10 overflows.
        have h_step_ov' : 2 ^ 64 ≤ acc.toNat * 10 := Nat.le_of_not_lt h_step_ov
        rw [pow10_at_step_fail k acc hk0 h_step_ov']
        rw [h_m_eq]
        -- Show the if condition is false: acc.toNat * 10^k.toNat ≥ 2^64.
        have h_pow_pos : 1 ≤ 10 ^ (k.toNat - 1) := Nat.one_le_pow _ _ (by decide)
        have h_pow_ge : 10 ≤ 10 ^ k.toNat := by
          rw [h_pow_succ]
          calc 10 = 1 * 10 := by rw [Nat.one_mul]
            _ ≤ 10 ^ (k.toNat - 1) * 10 := Nat.mul_le_mul_right 10 h_pow_pos
        have h_big : 2 ^ 64 ≤ acc.toNat * 10 ^ k.toNat := by
          have h : acc.toNat * 10 ≤ acc.toNat * 10 ^ k.toNat :=
            Nat.mul_le_mul_left acc.toNat h_pow_ge
          omega
        rw [if_neg (Nat.not_lt.mpr h_big)]

/-! ## Main postcondition (closed form).

Captures the `matches_brute_force` proptest at the `Nat` level: the
function returns `18 · 10^(n.toNat - 2)`.  The proptest only
samples `0 ≤ n ≤ 6` for cheap brute-force enumeration, but the
closed form holds across the entire success domain `2 ≤ n ≤ 20`
(beyond which the result no longer fits in `u64`). -/

/-- Postcondition (closed form): for `2 ≤ n.toNat ≤ 20`, the
    function succeeds and returns `18 · 10^(n.toNat - 2)`.  Combined
    with the two base-case unit pins (`_at_0`, `_at_1`), this pins
    down the exact mathematical value on the entire success domain. -/
theorem starts_one_ends_closed_form (n : u64)
    (hlo : 2 ≤ n.toNat) (hhi : n.toNat ≤ 20) :
    clever_082_starts_one_ends.starts_one_ends n
      = RustM.ok (UInt64.ofNat (18 * 10 ^ (n.toNat - 2))) := by
  unfold clever_082_starts_one_ends.starts_one_ends
  -- Branch out of `n == 0` and `n == 1`.
  have h_n_ne_0 : n ≠ 0 := by
    intro hh
    have : n.toNat = (0 : u64).toNat := by rw [hh]
    rw [u64_zero_toNat] at this; omega
  have h_n0_false : decide (n = (0 : u64)) = false := decide_eq_false h_n_ne_0
  simp only [show (n ==? (0 : u64)) =
                 (pure (decide (n = (0 : u64))) : RustM Bool) from rfl,
             h_n0_false, pure_bind, Bool.false_eq_true, ↓reduceIte]
  have h_n_ne_1 : n ≠ 1 := by
    intro hh
    have : n.toNat = (1 : u64).toNat := by rw [hh]
    rw [u64_one_toNat] at this; omega
  have h_n1_false : decide (n = (1 : u64)) = false := decide_eq_false h_n_ne_1
  simp only [show (n ==? (1 : u64)) =
                 (pure (decide (n = (1 : u64))) : RustM Bool) from rfl,
             h_n1_false, pure_bind, Bool.false_eq_true, ↓reduceIte]
  -- Reduce n -? 2 (no underflow since n.toNat ≥ 2).
  have h_two_le : (2 : u64).toNat ≤ n.toNat := by rw [u64_two_toNat]; exact hlo
  have h_n_sub_no_uo : ¬ UInt64.subOverflow n 2 := by
    rw [UInt64.subOverflow_iff, u64_two_toNat]; omega
  have h_bv_sub : BitVec.usubOverflow n.toBitVec (2 : u64).toBitVec = false := by
    cases hb : BitVec.usubOverflow n.toBitVec (2 : u64).toBitVec with
    | false => rfl
    | true => exact absurd hb h_n_sub_no_uo
  have h_n_sub : (n -? (2 : u64) : RustM u64) = pure (n - 2) := by
    show (rust_primitives.ops.arith.Sub.sub n (2 : u64) : RustM u64) = pure (n - 2)
    show (if BitVec.usubOverflow n.toBitVec ((2 : u64).toBitVec) then
            (.fail .integerOverflow : RustM u64)
          else pure (n - 2)) = pure (n - 2)
    rw [h_bv_sub]; rfl
  rw [h_n_sub]
  simp only [pure_bind]
  -- Apply characterization to pow10_at (n - 2) 1.
  rw [pow10_at_compute]
  have h_n_sub_toNat : (n - 2).toNat = n.toNat - 2 := by
    rw [UInt64.toNat_sub_of_le' h_two_le, u64_two_toNat]
  have h_acc_pow : (1 : u64).toNat * 10 ^ (n - 2).toNat = 10 ^ (n.toNat - 2) := by
    rw [u64_one_toNat, Nat.one_mul, h_n_sub_toNat]
  rw [h_acc_pow]
  -- 10^(n.toNat - 2) ≤ 10^18 < 2^64 in the success range.
  have h_pow_lt : 10 ^ (n.toNat - 2) < 2 ^ 64 := by
    have h_exp_le : n.toNat - 2 ≤ 18 := by omega
    have h_18 : (10 : Nat) ^ 18 < 2 ^ 64 := by decide
    have h_mono : (10 : Nat) ^ (n.toNat - 2) ≤ 10 ^ 18 :=
      Nat.pow_le_pow_right (by decide : 1 ≤ 10) h_exp_le
    omega
  rw [if_pos h_pow_lt]
  simp only [RustM_ok_bind]
  -- Now reduce 18 *? UInt64.ofNat (10^(n.toNat - 2)).
  have h_ofnat_toNat : (UInt64.ofNat (10 ^ (n.toNat - 2))).toNat = 10 ^ (n.toNat - 2) := by
    show (BitVec.ofNat 64 (10 ^ (n.toNat - 2))).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_pow_lt]
  have h_18_mul_fit : (18 : Nat) * 10 ^ (n.toNat - 2) < 2 ^ 64 := by
    have h_exp_le : n.toNat - 2 ≤ 18 := by omega
    have h_18_pow_le : 18 * 10 ^ (n.toNat - 2) ≤ 18 * 10 ^ 18 :=
      Nat.mul_le_mul_left 18 (Nat.pow_le_pow_right (by decide : 1 ≤ 10) h_exp_le)
    have h_18 : (18 : Nat) * 10 ^ 18 < 2 ^ 64 := by decide
    omega
  have h_18_no_ov : ¬ UInt64.mulOverflow 18 (UInt64.ofNat (10 ^ (n.toNat - 2))) := by
    rw [UInt64.mulOverflow_iff, u64_eighteen_toNat, h_ofnat_toNat]
    omega
  have h_bv_18 : BitVec.umulOverflow (18 : u64).toBitVec
                   (UInt64.ofNat (10 ^ (n.toNat - 2))).toBitVec = false := by
    cases hb : BitVec.umulOverflow (18 : u64).toBitVec
                 (UInt64.ofNat (10 ^ (n.toNat - 2))).toBitVec with
    | false => rfl
    | true => exact absurd hb h_18_no_ov
  have h_18_mul : ((18 : u64) *? UInt64.ofNat (10 ^ (n.toNat - 2)) : RustM u64) =
                    pure ((18 : u64) * UInt64.ofNat (10 ^ (n.toNat - 2))) := by
    show (rust_primitives.ops.arith.Mul.mul (18 : u64)
            (UInt64.ofNat (10 ^ (n.toNat - 2))) : RustM u64) =
            pure ((18 : u64) * UInt64.ofNat (10 ^ (n.toNat - 2)))
    show (if BitVec.umulOverflow (18 : u64).toBitVec
              (UInt64.ofNat (10 ^ (n.toNat - 2))).toBitVec then
            (.fail .integerOverflow : RustM u64)
          else pure ((18 : u64) * UInt64.ofNat (10 ^ (n.toNat - 2)))) =
          pure ((18 : u64) * UInt64.ofNat (10 ^ (n.toNat - 2)))
    rw [h_bv_18]; rfl
  rw [h_18_mul]
  -- Final: pure (18 * ofNat ...) = ok (ofNat (18 * 10^(n-2)))
  apply congrArg RustM.ok
  apply UInt64.toNat_inj.mp
  have h_mul_no_ov : (18 : u64).toNat * (UInt64.ofNat (10 ^ (n.toNat - 2))).toNat
                       < 2 ^ 64 := by
    rw [u64_eighteen_toNat, h_ofnat_toNat]; exact h_18_mul_fit
  rw [UInt64.toNat_mul_of_lt h_mul_no_ov, u64_eighteen_toNat, h_ofnat_toNat]
  show 18 * 10 ^ (n.toNat - 2) = (BitVec.ofNat 64 (18 * 10 ^ (n.toNat - 2))).toNat
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_18_mul_fit]

/-! ## Failure condition (integer overflow).

For `n ≥ 21` the closed-form value `18 · 10^(n-2)` exceeds
`u64::MAX`, so the function panics with `Error.integerOverflow`.
This pins down the precondition `n ≤ 20`.  The proptest does not
explicitly assert the failure mode (it's outside its sampled
range), but the contract clearly delineates it — the function
*must* return some `RustM` value, and outside the success domain
that value can only be `.fail .integerOverflow` (the only failure
mode any `*?` site can produce). -/

/-- Failure: for every `n ≥ 21`, `starts_one_ends n` panics with
    integer overflow.  The boundary value `n = 21` overflows in the
    outer `18 *? 10^19`; larger `n` overflow earlier in the
    `pow10_at` walk. -/
theorem starts_one_ends_overflow (n : u64) (h : 21 ≤ n.toNat) :
    clever_082_starts_one_ends.starts_one_ends n
      = RustM.fail .integerOverflow := by
  unfold clever_082_starts_one_ends.starts_one_ends
  have h_n_ne_0 : n ≠ 0 := by
    intro hh
    have : n.toNat = (0 : u64).toNat := by rw [hh]
    rw [u64_zero_toNat] at this; omega
  have h_n0_false : decide (n = (0 : u64)) = false := decide_eq_false h_n_ne_0
  simp only [show (n ==? (0 : u64)) =
                 (pure (decide (n = (0 : u64))) : RustM Bool) from rfl,
             h_n0_false, pure_bind, Bool.false_eq_true, ↓reduceIte]
  have h_n_ne_1 : n ≠ 1 := by
    intro hh
    have : n.toNat = (1 : u64).toNat := by rw [hh]
    rw [u64_one_toNat] at this; omega
  have h_n1_false : decide (n = (1 : u64)) = false := decide_eq_false h_n_ne_1
  simp only [show (n ==? (1 : u64)) =
                 (pure (decide (n = (1 : u64))) : RustM Bool) from rfl,
             h_n1_false, pure_bind, Bool.false_eq_true, ↓reduceIte]
  have h_two_le : (2 : u64).toNat ≤ n.toNat := by rw [u64_two_toNat]; omega
  have h_n_sub_no_uo : ¬ UInt64.subOverflow n 2 := by
    rw [UInt64.subOverflow_iff, u64_two_toNat]; omega
  have h_bv_sub : BitVec.usubOverflow n.toBitVec (2 : u64).toBitVec = false := by
    cases hb : BitVec.usubOverflow n.toBitVec (2 : u64).toBitVec with
    | false => rfl
    | true => exact absurd hb h_n_sub_no_uo
  have h_n_sub : (n -? (2 : u64) : RustM u64) = pure (n - 2) := by
    show (rust_primitives.ops.arith.Sub.sub n (2 : u64) : RustM u64) = pure (n - 2)
    show (if BitVec.usubOverflow n.toBitVec ((2 : u64).toBitVec) then
            (.fail .integerOverflow : RustM u64)
          else pure (n - 2)) = pure (n - 2)
    rw [h_bv_sub]; rfl
  rw [h_n_sub]
  simp only [pure_bind]
  rw [pow10_at_compute]
  have h_n_sub_toNat : (n - 2).toNat = n.toNat - 2 := by
    rw [UInt64.toNat_sub_of_le' h_two_le, u64_two_toNat]
  have h_acc_pow : (1 : u64).toNat * 10 ^ (n - 2).toNat = 10 ^ (n.toNat - 2) := by
    rw [u64_one_toNat, Nat.one_mul, h_n_sub_toNat]
  rw [h_acc_pow]
  by_cases h_pow_lt : 10 ^ (n.toNat - 2) < 2 ^ 64
  · -- pow10_at returns ok 10^(n-2); then 18 * 10^(n-2) overflows.
    rw [if_pos h_pow_lt]
    simp only [RustM_ok_bind]
    have h_ofnat_toNat : (UInt64.ofNat (10 ^ (n.toNat - 2))).toNat = 10 ^ (n.toNat - 2) := by
      show (BitVec.ofNat 64 (10 ^ (n.toNat - 2))).toNat = _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_pow_lt]
    -- For n.toNat ≥ 21, 18 * 10^(n.toNat - 2) ≥ 18 * 10^19 > 2^64.
    have h_18_mul_ov : 2 ^ 64 ≤ 18 * 10 ^ (n.toNat - 2) := by
      have h_exp_ge : 19 ≤ n.toNat - 2 := by omega
      have h_pow_19_le : (10 : Nat) ^ 19 ≤ 10 ^ (n.toNat - 2) :=
        Nat.pow_le_pow_right (by decide : 1 ≤ 10) h_exp_ge
      have h_18_pow_19_le : 18 * 10 ^ 19 ≤ 18 * 10 ^ (n.toNat - 2) :=
        Nat.mul_le_mul_left 18 h_pow_19_le
      have h_18_19 : (2 : Nat) ^ 64 ≤ 18 * 10 ^ 19 := by decide
      omega
    have h_18_ov : UInt64.mulOverflow 18 (UInt64.ofNat (10 ^ (n.toNat - 2))) := by
      rw [UInt64.mulOverflow_iff, u64_eighteen_toNat, h_ofnat_toNat]
      exact h_18_mul_ov
    have h_bv_18 : BitVec.umulOverflow (18 : u64).toBitVec
                     (UInt64.ofNat (10 ^ (n.toNat - 2))).toBitVec = true := h_18_ov
    have h_18_mul : ((18 : u64) *? UInt64.ofNat (10 ^ (n.toNat - 2)) : RustM u64) =
                      RustM.fail .integerOverflow := by
      show (rust_primitives.ops.arith.Mul.mul (18 : u64)
              (UInt64.ofNat (10 ^ (n.toNat - 2))) : RustM u64) = _
      show (if BitVec.umulOverflow (18 : u64).toBitVec
                (UInt64.ofNat (10 ^ (n.toNat - 2))).toBitVec then
              (.fail .integerOverflow : RustM u64)
            else pure ((18 : u64) * UInt64.ofNat (10 ^ (n.toNat - 2)))) = _
      rw [h_bv_18]; rfl
    rw [h_18_mul]
  · -- pow10_at returns fail; bind propagates.
    rw [if_neg h_pow_lt]
    rfl

end Clever_082_starts_one_endsObligations
