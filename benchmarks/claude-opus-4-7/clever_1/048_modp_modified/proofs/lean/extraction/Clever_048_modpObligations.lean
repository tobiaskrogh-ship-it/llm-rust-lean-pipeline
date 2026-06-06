-- Companion obligations file for the `clever_048_modp` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_048_modp

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_048_modpObligations

/-! ## Helpers reused below. -/

private theorem u64_zero_toNat : ((0 : u64).toNat) = 0 := rfl
private theorem u64_one_toNat  : ((1 : u64).toNat) = 1 := rfl
private theorem u64_two_toNat  : ((2 : u64).toNat) = 2 := rfl

/-- `(a % p) * b % p = a * b % p` on Nat. -/
private theorem nat_mod_mul_left (a b p : Nat) :
    (a % p) * b % p = a * b % p := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

/-- Bridge `UInt64.ofNat x` toNat for `x ≤ 2^63`. -/
private theorem u64_ofNat_toNat_of_le (x : Nat) (h : x ≤ 2 ^ 63) :
    (UInt64.ofNat x).toNat = x := by
  have h_lt : x < 2 ^ 64 := by
    have h63 : (2 ^ 63 : Nat) < 2 ^ 64 := by decide
    omega
  simp [UInt64.toNat, UInt64.ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lt]

/-! ## Contract clauses

The Rust source contains the following contract-style tests in `mod tests`:
  * `small_cases` — four unit pins: `modp(0,5)=1`, `modp(0,1)=0`,
    `modp(3,5)=3`, `modp(10,7)=2`.
  * `matches_oracle` — main postcondition: for `p > 0`, `modp(n, p)` equals
    `2^n mod p` (computed via the `u128` naive oracle, which agrees with
    `Nat`-level `2^n mod p` for any `p` fitting in `u64`).
  * `p_zero_yields_zero` — degenerate convention: `p = 0 → 0`.

Each becomes one independent `theorem`.  Equational form (`f x = RustM.ok …`)
is used everywhere because the function is total in the safe domain.

### Feasibility note on `matches_oracle`

The proptest bounds `p ≤ 2^30`, but the universal Nat statement holds across
the wider range `0 < p ≤ 2^63`.  The accumulator invariant `acc < p` plus
`p ≤ 2^63` gives `acc * 2 < 2^64`, ruling out the only overflow site
(`(acc *? 2) %? p`).  For `p > 2^63` the universal statement is *false*:
e.g. for `p = 2^63 + 1`, after enough steps `acc = 2^63 < p`, and then
`acc * 2 = 2^64` overflows.  So we take the strongest honest precondition
`p.toNat ≤ 2^63`, well beyond the proptest's range.

The `k +? 1` step never overflows: recursion only continues when `k < n ≤
u64::MAX`, so `k + 1 ≤ n ≤ u64::MAX`.  No `n`-side precondition needed. -/

/-- Degenerate boundary: `p = 0 → 0`, regardless of `n`.
    Captures the proptest `p_zero_yields_zero`. -/
theorem modp_p_zero (n : u64) :
    clever_048_modp.modp n 0 = RustM.ok 0 := by
  unfold clever_048_modp.modp
  simp only [show ((0 : u64) ==? (0 : u64)) =
                 (pure (decide ((0 : u64) = (0 : u64))) : RustM Bool) from rfl,
             pure_bind, decide_true, ↓reduceIte]
  rfl

/-! ## Branch lemmas for `pow2_mod_at` -/

/-- Base branch: when `n.toNat ≤ k.toNat`, the function returns `pure acc`. -/
private theorem pow2_mod_at_base (n p acc k : u64) (h : n.toNat ≤ k.toNat) :
    clever_048_modp.pow2_mod_at n p acc k = RustM.ok acc := by
  unfold clever_048_modp.pow2_mod_at
  have h_ge : k ≥ n := UInt64.le_iff_toNat_le.mpr h
  have h_dec : decide (k ≥ n) = true := decide_eq_true h_ge
  simp only [show (k >=? n : RustM Bool) = (pure (decide (k ≥ n)) : RustM Bool) from rfl,
             h_dec, pure_bind, ↓reduceIte]
  rfl

/-- Recursive step: when `k.toNat < n.toNat`, `acc.toNat < p.toNat ≤ 2^63`,
    delegates to the recursive call with `(acc*2) % p` and `k+1`. -/
private theorem pow2_mod_at_step (n p acc k : u64)
    (h_lt : k.toNat < n.toNat)
    (h_p_pos : 0 < p.toNat)
    (h_acc_lt_p : acc.toNat < p.toNat)
    (h_p_fit : p.toNat ≤ 2 ^ 63) :
    clever_048_modp.pow2_mod_at n p acc k =
      clever_048_modp.pow2_mod_at n p ((acc * 2) % p) (k + 1) := by
  conv => lhs; unfold clever_048_modp.pow2_mod_at
  have h_not_ge : ¬ k ≥ n := by
    intro hk
    have := UInt64.le_iff_toNat_le.mp hk
    omega
  have h_dec : decide (k ≥ n) = false := decide_eq_false h_not_ge
  simp only [show (k >=? n : RustM Bool) = (pure (decide (k ≥ n)) : RustM Bool) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
  -- Reduce acc *? 2.
  have h_acc_lt_pow : acc.toNat < 2 ^ 63 := Nat.lt_of_lt_of_le h_acc_lt_p h_p_fit
  have h_acc_mul_lt : acc.toNat * (2 : u64).toNat < 2 ^ 64 := by
    rw [u64_two_toNat]
    have h63x2 : (2 ^ 63 : Nat) * 2 = 2 ^ 64 := by decide
    have h : acc.toNat * 2 < 2 ^ 63 * 2 :=
      Nat.mul_lt_mul_of_lt_of_le h_acc_lt_pow (Nat.le_refl 2) (by decide)
    omega
  have h_mul_no_overflow : ¬ UInt64.mulOverflow acc 2 := by
    rw [UInt64.mulOverflow_iff]; omega
  have h_bv_mul : BitVec.umulOverflow acc.toBitVec (2 : u64).toBitVec = false := by
    cases hb : BitVec.umulOverflow acc.toBitVec (2 : u64).toBitVec with
    | false => rfl
    | true => exact absurd hb h_mul_no_overflow
  have h_acc_mul : (acc *? (2 : u64) : RustM u64) = pure (acc * 2) := by
    show (rust_primitives.ops.arith.Mul.mul acc (2 : u64) : RustM u64) = pure (acc * 2)
    show (if BitVec.umulOverflow acc.toBitVec ((2 : u64).toBitVec) then
            (.fail .integerOverflow : RustM u64)
          else pure (acc * 2)) = pure (acc * 2)
    rw [h_bv_mul]; rfl
  rw [h_acc_mul]
  simp only [pure_bind]
  -- Reduce (acc * 2) %? p
  have h_p_ne : p ≠ 0 := by
    intro h
    have h_zero : p.toNat = (0 : u64).toNat := by rw [h]
    rw [u64_zero_toNat] at h_zero; omega
  have h_mod : ((acc * 2) %? p : RustM u64) = pure ((acc * 2) % p) := by
    show (rust_primitives.ops.arith.Rem.rem (acc * 2) p : RustM u64) = pure ((acc * 2) % p)
    show (if p = 0 then (.fail .divisionByZero : RustM u64) else pure ((acc * 2) % p))
            = pure ((acc * 2) % p)
    rw [if_neg h_p_ne]
  rw [h_mod]
  simp only [pure_bind]
  -- Reduce k +? 1
  have h_n_lt : n.toNat < 2 ^ 64 := n.toNat_lt
  have h_k_add_no_overflow : ¬ UInt64.addOverflow k 1 := by
    rw [UInt64.addOverflow_iff, u64_one_toNat]
    omega
  have h_bv_add : BitVec.uaddOverflow k.toBitVec (1 : u64).toBitVec = false := by
    cases hb : BitVec.uaddOverflow k.toBitVec (1 : u64).toBitVec with
    | false => rfl
    | true => exact absurd hb h_k_add_no_overflow
  have h_k_add : (k +? (1 : u64) : RustM u64) = pure (k + 1) := by
    show (rust_primitives.ops.arith.Add.add k 1 : RustM u64) = pure (k + 1)
    show (if BitVec.uaddOverflow k.toBitVec ((1 : u64).toBitVec) then
            (.fail .integerOverflow : RustM u64)
          else pure (k + 1)) = pure (k + 1)
    rw [h_bv_add]; rfl
  rw [h_k_add]
  simp only [pure_bind]

/-! ## Main characterization (strong induction on `n.toNat - k.toNat`) -/

private theorem pow2_mod_at_correct
    (n p : u64) (h_p_pos : 0 < p.toNat) (h_p_fit : p.toNat ≤ 2 ^ 63) :
    ∀ (m : Nat) (acc k : u64),
      acc.toNat < p.toNat →
      k.toNat ≤ n.toNat →
      n.toNat - k.toNat = m →
      clever_048_modp.pow2_mod_at n p acc k =
        RustM.ok (UInt64.ofNat ((acc.toNat * 2 ^ m) % p.toNat)) := by
  intro m
  induction m with
  | zero =>
    intro acc k h_acc h_k_le h_m
    have h_k_ge_n : n.toNat ≤ k.toNat := by omega
    rw [pow2_mod_at_base n p acc k h_k_ge_n]
    congr 1
    -- Goal: acc = UInt64.ofNat ((acc.toNat * 2^0) % p.toNat)
    -- 2^0 = 1, acc < p, so acc % p = acc.
    have h_mod_eq : acc.toNat % p.toNat = acc.toNat := Nat.mod_eq_of_lt h_acc
    have h_simp : (acc.toNat * 2 ^ 0) % p.toNat = acc.toNat := by
      rw [Nat.pow_zero, Nat.mul_one, h_mod_eq]
    rw [h_simp]
    apply UInt64.toNat_inj.mp
    have h_acc_lt_pow : acc.toNat ≤ 2 ^ 63 :=
      Nat.le_of_lt (Nat.lt_of_lt_of_le h_acc h_p_fit)
    rw [u64_ofNat_toNat_of_le acc.toNat h_acc_lt_pow]
  | succ m ih =>
    intro acc k h_acc h_k_le h_m
    have h_k_lt_n : k.toNat < n.toNat := by omega
    rw [pow2_mod_at_step n p acc k h_k_lt_n h_p_pos h_acc h_p_fit]
    -- Apply IH with acc' = (acc * 2) % p, k' = k + 1
    have h_acc_lt_pow : acc.toNat < 2 ^ 63 := Nat.lt_of_lt_of_le h_acc h_p_fit
    have h_acc2_lt : acc.toNat * 2 < 2 ^ 64 := by
      have h63x2 : (2 ^ 63 : Nat) * 2 = 2 ^ 64 := by decide
      have : acc.toNat * 2 < 2 ^ 63 * 2 :=
        Nat.mul_lt_mul_of_lt_of_le h_acc_lt_pow (Nat.le_refl 2) (by decide)
      omega
    have h_acc2_toNat : (acc * 2).toNat = acc.toNat * 2 := by
      have := UInt64.toNat_mul_of_lt (x := acc) (y := 2) (by rw [u64_two_toNat]; exact h_acc2_lt)
      rw [this, u64_two_toNat]
    have h_new_acc_toNat : ((acc * 2) % p).toNat = (acc.toNat * 2) % p.toNat := by
      rw [UInt64.toNat_mod, h_acc2_toNat]
    have h_new_acc_lt : ((acc * 2) % p).toNat < p.toNat := by
      rw [h_new_acc_toNat]; exact Nat.mod_lt _ h_p_pos
    have h_n_lt : n.toNat < 2 ^ 64 := n.toNat_lt
    have h_k_add_no_ov : k.toNat + 1 < 2 ^ 64 := by omega
    have h_k_add_toNat : (k + 1).toNat = k.toNat + 1 := by
      have := UInt64.toNat_add_of_lt (x := k) (y := 1) (by rw [u64_one_toNat]; exact h_k_add_no_ov)
      rw [this, u64_one_toNat]
    have h_new_k_le : (k + 1).toNat ≤ n.toNat := by rw [h_k_add_toNat]; omega
    have h_new_m : n.toNat - (k + 1).toNat = m := by rw [h_k_add_toNat]; omega
    rw [ih ((acc * 2) % p) (k + 1) h_new_acc_lt h_new_k_le h_new_m]
    congr 2
    rw [h_new_acc_toNat]
    -- Goal: (acc.toNat * 2) % p.toNat * 2^m % p.toNat = acc.toNat * 2^(m+1) % p.toNat
    rw [nat_mod_mul_left]
    have h_pow : acc.toNat * 2 * 2 ^ m = acc.toNat * 2 ^ (m + 1) := by
      rw [Nat.pow_succ]
      rw [Nat.mul_assoc, Nat.mul_comm 2 (2^m)]
    rw [h_pow]

/-- Main postcondition (closed form): for `p > 0` in the feasibility
    range `p.toNat ≤ 2^63`, `modp n p = 2^n mod p`.  Captures the
    proptest `matches_oracle` (whose `u128` naive oracle is precisely
    `2^n mod p` at the `Nat` level).  Implies `result < p`. -/
theorem modp_matches_oracle (n p : u64)
    (h_pos : 0 < p.toNat)
    (h_fit : p.toNat ≤ 2 ^ 63) :
    clever_048_modp.modp n p
      = RustM.ok (UInt64.ofNat (2 ^ n.toNat % p.toNat)) := by
  unfold clever_048_modp.modp
  have h_p_ne : p ≠ 0 := by
    intro h
    have h_zero : p.toNat = (0 : u64).toNat := by rw [h]
    rw [u64_zero_toNat] at h_zero; omega
  have h_dec : decide (p = (0 : u64)) = false := decide_eq_false h_p_ne
  simp only [show (p ==? (0 : u64)) =
                 (pure (decide (p = (0 : u64))) : RustM Bool) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
  -- Reduce 1 %? p
  have h_one_mod : ((1 : u64) %? p : RustM u64) = pure ((1 : u64) % p) := by
    show (rust_primitives.ops.arith.Rem.rem (1 : u64) p : RustM u64) = pure ((1 : u64) % p)
    show (if p = 0 then (.fail .divisionByZero : RustM u64) else pure ((1 : u64) % p))
            = pure ((1 : u64) % p)
    rw [if_neg h_p_ne]
  rw [h_one_mod]
  simp only [pure_bind]
  -- Apply characterization
  have h_one_mod_p_lt : ((1 : u64) % p).toNat < p.toNat := by
    rw [UInt64.toNat_mod]
    exact Nat.mod_lt _ h_pos
  have h_zero_le : (0 : u64).toNat ≤ n.toNat := by rw [u64_zero_toNat]; exact Nat.zero_le _
  have h_m_eq : n.toNat - (0 : u64).toNat = n.toNat := by rw [u64_zero_toNat]
  rw [pow2_mod_at_correct n p h_pos h_fit n.toNat ((1 : u64) % p) (0 : u64)
        h_one_mod_p_lt h_zero_le h_m_eq]
  congr 1
  -- Goal: UInt64.ofNat (((1 % p).toNat * 2^n.toNat) % p.toNat) =
  --       UInt64.ofNat (2^n.toNat % p.toNat)
  congr 1
  rw [UInt64.toNat_mod, u64_one_toNat]
  -- Goal: (1 % p.toNat) * 2^n.toNat % p.toNat = 2^n.toNat % p.toNat
  rw [nat_mod_mul_left, Nat.one_mul]

/-! ## Unit pins from `small_cases` -/

/-- Unit pin: `modp 0 5 = 1`.  Reflects the convention `2^0 = 1`,
    and `1 % 5 = 1`. -/
theorem modp_at_0_5 :
    clever_048_modp.modp 0 5 = RustM.ok 1 := by
  native_decide

/-- Unit pin: `modp 0 1 = 0`.  Differentiates the boundary `p = 1`
    (where `1 % 1 = 0`) from the `p > 1` case. -/
theorem modp_at_0_1 :
    clever_048_modp.modp 0 1 = RustM.ok 0 := by
  native_decide

/-- Unit pin: `modp 3 5 = 3`.  Sanity-checks the first few iterations:
    `1 → 2 → 4 → (8 mod 5) = 3`. -/
theorem modp_at_3_5 :
    clever_048_modp.modp 3 5 = RustM.ok 3 := by
  native_decide

/-- Unit pin: `modp 10 7 = 2`.  `2^10 = 1024 = 7·146 + 2`. -/
theorem modp_at_10_7 :
    clever_048_modp.modp 10 7 = RustM.ok 2 := by
  native_decide

end Clever_048_modpObligations
