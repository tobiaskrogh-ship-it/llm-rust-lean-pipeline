-- Companion obligations file for the `clever_148_x_or_y` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_148_x_or_y

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_148_x_or_yObligations

/-! ## Spec-side primality oracle

Mathematical primality on `Int`. Mirrors `is_prime_int` from
`clever_024_factorize_modified`: the standard "≥ 2 ∧ no proper
divisor" definition. The codomain is `Int` because `Int64.toInt`
returns `Int`. -/

/-- Mathematical primality on `Int`. -/
private def is_prime_int (p : Int) : Prop :=
  2 ≤ p ∧ ∀ k : Int, 2 ≤ k → k < p → ¬ k ∣ p

/-! ## Numeric helper lemmas (i64 ⇄ Int bridges).

These mirror the helper toolkit from `clever_024_factorize_modified`. -/

/-- `RustM.ok x >>= f = f x`. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem i64_one_toInt : (1 : i64).toInt = 1 := by decide
private theorem i64_two_toInt : (2 : i64).toInt = 2 := by decide
private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide
private theorem i64_neg_one_toInt : (-1 : i64).toInt = -1 := by decide

private theorem i64_min_toInt : Int64.minValue.toInt = -(2^63 : Int) := by decide

private theorem i64_toInt_lt (x : i64) : x.toInt < 2 ^ 63 := by
  have h := Int64.toInt_lt x
  simpa using h

private theorem i64_toInt_ge (x : i64) : -(2^63 : Int) ≤ x.toInt := by
  have h := Int64.le_toInt x
  simpa using h

/-- `p *? p = pure (p * p)` when `p ≥ 0` and `p * p` fits in `i64`. -/
private theorem mul_self_pure (p : i64) (hnn : 0 ≤ p.toInt)
    (h : p.toInt * p.toInt < 2 ^ 63) :
    (p *? p : RustM i64) = pure (p * p) := by
  show (rust_primitives.ops.arith.Mul.mul p p : RustM i64) = pure (p * p)
  show (if BitVec.smulOverflow p.toBitVec p.toBitVec then
          (.fail .integerOverflow : RustM i64)
        else pure (p * p)) = _
  have h_pp_nn : 0 ≤ p.toInt * p.toInt := Int.mul_nonneg hnn hnn
  have h63 : (2 : Int) ^ (64 - 1) = 2 ^ 63 := by decide
  have h_no : ¬ Int64.mulOverflow p p := by
    intro hov
    rw [Int64.mulOverflow_iff] at hov
    rcases hov with hov | hov
    · rw [h63] at hov; omega
    · rw [h63] at hov; omega
  have h_bv : BitVec.smulOverflow p.toBitVec p.toBitVec = false := by
    cases hb : BitVec.smulOverflow p.toBitVec p.toBitVec with
    | false => rfl
    | true => exact absurd hb h_no
  rw [h_bv]; rfl

/-- `p +? 1 = pure (p + 1)` when `p + 1` fits in `i64`. -/
private theorem add_one_pure (p : i64) (h : p.toInt + 1 < 2 ^ 63) :
    (p +? (1 : i64) : RustM i64) = pure (p + 1) := by
  show (rust_primitives.ops.arith.Add.add p 1 : RustM i64) = pure (p + 1)
  show (if BitVec.saddOverflow p.toBitVec (1 : i64).toBitVec then
          (.fail .integerOverflow : RustM i64)
        else pure (p + 1)) = _
  have h_ge_min := i64_toInt_ge p
  have h63 : (2 : Int) ^ (64 - 1) = 2 ^ 63 := by decide
  have h_no : ¬ Int64.addOverflow p 1 := by
    intro hov
    rw [Int64.addOverflow_iff, i64_one_toInt] at hov
    rcases hov with hov | hov
    · rw [h63] at hov; omega
    · rw [h63] at hov; omega
  have h_bv : BitVec.saddOverflow p.toBitVec (1 : i64).toBitVec = false := by
    cases hb : BitVec.saddOverflow p.toBitVec (1 : i64).toBitVec with
    | false => rfl
    | true => exact absurd hb h_no
  rw [h_bv]; rfl

/-- `n %? p = pure (n % p)` when `0 < p.toInt`. -/
private theorem mod_pure (n p : i64) (hp_pos : 0 < p.toInt) :
    (n %? p : RustM i64) = pure (n % p) := by
  show (rust_primitives.ops.arith.Rem.rem n p : RustM i64) = pure (n % p)
  show (if n = Int64.minValue && p = -1 then
          (.fail .integerOverflow : RustM i64)
        else if p = 0 then .fail .divisionByZero
        else pure (n % p)) = pure (n % p)
  have hp_ne_neg_one : p ≠ (-1 : i64) := by
    intro h_eq
    have : p.toInt = -1 := by rw [h_eq, i64_neg_one_toInt]
    omega
  have hp_ne_zero : p ≠ (0 : i64) := by
    intro h_eq
    have : p.toInt = 0 := by rw [h_eq, i64_zero_toInt]
    omega
  have h_and : (n = Int64.minValue && p = -1) = false := by
    rcases Decidable.em (n = Int64.minValue) with hn | hn
    · simp [hn, hp_ne_neg_one]
    · simp [hn]
  rw [h_and, if_neg hp_ne_zero]
  rfl

/-- For nonneg `n` and positive `p`: `(n % p).toInt = n.toInt % p.toInt`. -/
private theorem toInt_mod_of_nonneg (n p : i64)
    (hn : 0 ≤ n.toInt) (hp : 0 < p.toInt) :
    (n % p).toInt = n.toInt % p.toInt := by
  have hp_ne_neg_one : p ≠ (-1 : i64) := by
    intro h_eq
    have : p.toInt = -1 := by rw [h_eq, i64_neg_one_toInt]
    omega
  have h_tmod : (n % p).toInt = n.toInt.tmod p.toInt :=
    Int64.toInt_mod n p
  rw [h_tmod, Int.tmod_eq_emod_of_nonneg hn]

/-! ## Primality from trial-division.

For `n ≥ 2`: if no `k ∈ [2, p)` divides `n` and `p² > n`, then `n` is prime
(in the sense of `is_prime_int`). Standard "smallest factor ≤ √n" argument.
Copied from `clever_024_factorize_modified`. -/

private theorem is_prime_of_no_small_divisor (n : Int) (p : Int)
    (hn : 2 ≤ n) (hp : 0 ≤ p)
    (h_no_small : ∀ d : Int, 2 ≤ d → d < p → ¬ d ∣ n)
    (h_pp_gt : p * p > n) :
    is_prime_int n := by
  refine ⟨hn, ?_⟩
  intro k hk_ge hk_lt h_dvd
  obtain ⟨d, hd⟩ := h_dvd
  have h_n_pos : 0 < n := by omega
  have h_k_pos : 0 < k := by omega
  have h_d_pos : 0 < d := by
    rcases Decidable.em (0 < d) with h | h
    · exact h
    · exfalso
      have h_d_le : d ≤ 0 := by omega
      have h_kd_nonpos : k * d ≤ 0 :=
        Int.mul_nonpos_of_nonneg_of_nonpos (by omega) h_d_le
      rw [← hd] at h_kd_nonpos
      omega
  have h_d_ge_2 : 2 ≤ d := by
    rcases Decidable.em (2 ≤ d) with h | h
    · exact h
    · exfalso
      have h_d_le_1 : d ≤ 1 := by omega
      have h_d_eq_1 : d = 1 := by omega
      rw [h_d_eq_1, Int.mul_one] at hd
      omega
  rcases Decidable.em (k ≤ d) with hkd | hkd
  · -- k ≤ d. k * k ≤ k * d = n, so k < p; also k ∣ n.
    have h_kk_le_kd : k * k ≤ k * d :=
      Int.mul_le_mul_of_nonneg_left hkd (by omega)
    have h_kk_le_n : k * k ≤ n := by rw [hd]; exact h_kk_le_kd
    have h_k_lt_p : k < p := by
      rcases Decidable.em (k < p) with h | h
      · exact h
      · exfalso
        have h_p_le_k : p ≤ k := by omega
        have : p * p ≤ k * k :=
          Int.mul_le_mul h_p_le_k h_p_le_k hp (by omega)
        omega
    exact h_no_small k hk_ge h_k_lt_p ⟨d, hd⟩
  · -- d < k. d * d ≤ d * k = k * d = n; d ∈ [2, p); d ∣ n.
    have h_d_lt_k : d < k := by omega
    have h_dd_le_kd : d * d ≤ k * d := by
      have : d * d ≤ k * d :=
        Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      exact this
    have h_dd_le_n : d * d ≤ n := by rw [hd]; exact h_dd_le_kd
    have h_d_lt_p : d < p := by
      rcases Decidable.em (d < p) with h | h
      · exact h
      · exfalso
        have h_p_le_d : p ≤ d := by omega
        have : p * p ≤ d * d :=
          Int.mul_le_mul h_p_le_d h_p_le_d hp (by omega)
        omega
    have h_d_dvd : d ∣ n := by
      refine ⟨k, ?_⟩
      rw [hd, Int.mul_comm]
    exact h_no_small d h_d_ge_2 h_d_lt_p h_d_dvd

/-! ## Branch reductions for `is_prime_at`.

`is_prime_at n p` unfolds into three branches:
  * `p² > n` ⟹ returns `ok true`  ("no divisor in [p, √n], so n is prime")
  * `p² ≤ n` ∧ `n % p = 0` ⟹ returns `ok false`  ("p divides n, so n is composite")
  * `p² ≤ n` ∧ `n % p ≠ 0` ⟹ recurses on `(n, p + 1)`.

Each lemma rewrites the call according to its branch hypotheses. -/

/-- `p*p > n` branch: returns `ok true`. -/
private theorem is_prime_at_dd_gt_n
    (n p : i64)
    (h_p_nn : 0 ≤ p.toInt) (h_pp_fits : p.toInt * p.toInt < 2 ^ 63)
    (h_pp_gt : p.toInt * p.toInt > n.toInt) :
    clever_148_x_or_y.is_prime_at n p = RustM.ok true := by
  conv => lhs; unfold clever_148_x_or_y.is_prime_at
  rw [mul_self_pure p h_p_nn h_pp_fits]
  simp only [pure_bind]
  have h_pp_nn : 0 ≤ p.toInt * p.toInt := Int.mul_nonneg h_p_nn h_p_nn
  have h63 : (2 : Int) ^ (64 - 1) = 2 ^ 63 := by decide
  have h_no_mul : ¬ Int64.mulOverflow p p := by
    intro hov
    rw [Int64.mulOverflow_iff] at hov
    rcases hov with hov | hov
    · rw [h63] at hov; omega
    · rw [h63] at hov; omega
  have h_pp_toInt : (p * p).toInt = p.toInt * p.toInt :=
    Int64.toInt_mul_of_not_mulOverflow h_no_mul
  have h_gt_u : (p * p) > n := by
    apply Int64.lt_iff_toInt_lt.mpr
    rw [h_pp_toInt]; exact h_pp_gt
  have h_dec_gt : decide ((p * p) > n) = true := decide_eq_true h_gt_u
  simp only [show ((p * p) >? n : RustM Bool) =
               (pure (decide ((p * p) > n)) : RustM Bool) from rfl,
             h_dec_gt, pure_bind, ↓reduceIte]
  rfl

/-- `p*p ≤ n` ∧ `p ∣ n` branch: returns `ok false`. -/
private theorem is_prime_at_mod_zero_step
    (n p : i64)
    (h_n_nn : 0 ≤ n.toInt)
    (h_p_pos : 0 < p.toInt) (h_pp_fits : p.toInt * p.toInt < 2 ^ 63)
    (h_pp_le_n : p.toInt * p.toInt ≤ n.toInt)
    (h_dvd : p.toInt ∣ n.toInt) :
    clever_148_x_or_y.is_prime_at n p = RustM.ok false := by
  conv => lhs; unfold clever_148_x_or_y.is_prime_at
  have h_p_nn : 0 ≤ p.toInt := by omega
  rw [mul_self_pure p h_p_nn h_pp_fits]
  simp only [pure_bind]
  have h_pp_nn : 0 ≤ p.toInt * p.toInt := Int.mul_nonneg h_p_nn h_p_nn
  have h63 : (2 : Int) ^ (64 - 1) = 2 ^ 63 := by decide
  have h_no_mul : ¬ Int64.mulOverflow p p := by
    intro hov
    rw [Int64.mulOverflow_iff] at hov
    rcases hov with hov | hov
    · rw [h63] at hov; omega
    · rw [h63] at hov; omega
  have h_pp_toInt : (p * p).toInt = p.toInt * p.toInt :=
    Int64.toInt_mul_of_not_mulOverflow h_no_mul
  have h_not_gt : ¬ (p * p) > n := by
    intro hgt
    have : (p * p).toInt > n.toInt := Int64.lt_iff_toInt_lt.mp hgt
    rw [h_pp_toInt] at this; omega
  have h_dec_gt : decide ((p * p) > n) = false := decide_eq_false h_not_gt
  simp only [show ((p * p) >? n : RustM Bool) =
               (pure (decide ((p * p) > n)) : RustM Bool) from rfl,
             h_dec_gt, pure_bind, Bool.false_eq_true, ↓reduceIte]
  rw [mod_pure n p h_p_pos]
  simp only [pure_bind]
  have h_mod_toInt : (n % p).toInt = 0 := by
    rw [toInt_mod_of_nonneg n p h_n_nn h_p_pos]
    exact Int.emod_eq_zero_of_dvd h_dvd
  have h_mod_zero : (n % p) = (0 : i64) := by
    apply Int64.toInt_inj.mp
    rw [h_mod_toInt, i64_zero_toInt]
  have h_dec_eq : decide ((n % p) = (0 : i64)) = true := decide_eq_true h_mod_zero
  simp only [show ((n % p) ==? (0 : i64) : RustM Bool) =
               (pure (decide ((n % p) = (0 : i64))) : RustM Bool) from rfl,
             h_dec_eq, pure_bind, ↓reduceIte]
  rfl

/-- `p*p ≤ n` ∧ `¬ p ∣ n` branch: recurses on `(n, p + 1)`. -/
private theorem is_prime_at_recurse_step
    (n p : i64)
    (h_n_nn : 0 ≤ n.toInt)
    (h_p_pos : 0 < p.toInt) (h_pp_fits : p.toInt * p.toInt < 2 ^ 63)
    (h_pp_le_n : p.toInt * p.toInt ≤ n.toInt)
    (h_not_dvd : ¬ p.toInt ∣ n.toInt)
    (h_p_plus_one_fits : p.toInt + 1 < 2 ^ 63) :
    clever_148_x_or_y.is_prime_at n p =
      clever_148_x_or_y.is_prime_at n (p + 1) := by
  conv => lhs; unfold clever_148_x_or_y.is_prime_at
  have h_p_nn : 0 ≤ p.toInt := by omega
  rw [mul_self_pure p h_p_nn h_pp_fits]
  simp only [pure_bind]
  have h_pp_nn : 0 ≤ p.toInt * p.toInt := Int.mul_nonneg h_p_nn h_p_nn
  have h63 : (2 : Int) ^ (64 - 1) = 2 ^ 63 := by decide
  have h_no_mul : ¬ Int64.mulOverflow p p := by
    intro hov
    rw [Int64.mulOverflow_iff] at hov
    rcases hov with hov | hov
    · rw [h63] at hov; omega
    · rw [h63] at hov; omega
  have h_pp_toInt : (p * p).toInt = p.toInt * p.toInt :=
    Int64.toInt_mul_of_not_mulOverflow h_no_mul
  have h_not_gt : ¬ (p * p) > n := by
    intro hgt
    have : (p * p).toInt > n.toInt := Int64.lt_iff_toInt_lt.mp hgt
    rw [h_pp_toInt] at this; omega
  have h_dec_gt : decide ((p * p) > n) = false := decide_eq_false h_not_gt
  simp only [show ((p * p) >? n : RustM Bool) =
               (pure (decide ((p * p) > n)) : RustM Bool) from rfl,
             h_dec_gt, pure_bind, Bool.false_eq_true, ↓reduceIte]
  rw [mod_pure n p h_p_pos]
  simp only [pure_bind]
  have h_mod_toInt : (n % p).toInt = n.toInt % p.toInt :=
    toInt_mod_of_nonneg n p h_n_nn h_p_pos
  have h_mod_not_zero : (n % p) ≠ (0 : i64) := by
    intro h_eq
    have h_mod_i : (n % p).toInt = ((0 : i64).toInt) := by rw [h_eq]
    rw [h_mod_toInt, i64_zero_toInt] at h_mod_i
    exact h_not_dvd (Int.dvd_of_emod_eq_zero h_mod_i)
  have h_dec_eq : decide ((n % p) = (0 : i64)) = false := decide_eq_false h_mod_not_zero
  simp only [show ((n % p) ==? (0 : i64) : RustM Bool) =
               (pure (decide ((n % p) = (0 : i64))) : RustM Bool) from rfl,
             h_dec_eq, pure_bind, Bool.false_eq_true, ↓reduceIte]
  rw [add_one_pure p h_p_plus_one_fits]
  simp only [pure_bind]

/-! ## Main spec for `is_prime_at`.

By strong induction on the measure `2^33 - p.toInt.toNat`.

The bound `p ≤ 2^31 + 1` is preserved: we only ever recurse when `p² ≤ n`,
which (combined with `n < 2^62`) forces `p ≤ 2^31`, so `p + 1 ≤ 2^31 + 1`.

The `h_no_small` precondition is the inductive invariant: no integer in
`[2, p)` divides `n`. Trivially satisfied at `p = 2`, and preserved across
the recursive step (we recurse only when `¬ p ∣ n`, so the new gap
`[2, p+1)` adds the now-excluded value `p`). -/

private theorem is_prime_at_spec
    (n : i64) (h_n_lo : 2 ≤ n.toInt) (h_n_hi : n.toInt < 2 ^ 62) :
    ∀ (p : i64),
      2 ≤ p.toInt → p.toInt ≤ 2 ^ 31 + 1 →
      (∀ k : Int, 2 ≤ k → k < p.toInt → ¬ k ∣ n.toInt) →
      (clever_148_x_or_y.is_prime_at n p = RustM.ok true ∧ is_prime_int n.toInt)
      ∨ (clever_148_x_or_y.is_prime_at n p = RustM.ok false ∧ ¬ is_prime_int n.toInt) := by
  intro p
  induction h_meas : (2 ^ 33 - p.toInt.toNat)
    using Nat.strongRecOn generalizing p with
  | _ m ih =>
    intro h_p_lo h_p_hi h_no_small
    have h_n_nn : 0 ≤ n.toInt := by omega
    have h_p_nn : 0 ≤ p.toInt := by omega
    have h_p_pos : 0 < p.toInt := by omega
    -- p² ≤ (2^31 + 1)² = 2^62 + 2^32 + 1 < 2^63
    have h_pp_fits : p.toInt * p.toInt < 2 ^ 63 := by
      have h1 : p.toInt * p.toInt ≤ (2^31 + 1) * p.toInt :=
        Int.mul_le_mul_of_nonneg_right h_p_hi h_p_nn
      have h2 : ((2 : Int)^31 + 1) * p.toInt ≤ (2^31 + 1) * (2^31 + 1) :=
        Int.mul_le_mul_of_nonneg_left h_p_hi (by decide)
      have h_bound : ((2 : Int)^31 + 1) * (2^31 + 1) < 2^63 := by decide
      omega
    by_cases hpp : p.toInt * p.toInt > n.toInt
    · -- p² > n: returns true, n is prime by is_prime_of_no_small_divisor.
      left
      refine ⟨is_prime_at_dd_gt_n n p h_p_nn h_pp_fits hpp, ?_⟩
      exact is_prime_of_no_small_divisor n.toInt p.toInt h_n_lo h_p_nn h_no_small hpp
    · -- p² ≤ n.
      have h_pp_le_n : p.toInt * p.toInt ≤ n.toInt := by omega
      by_cases hdvd : p.toInt ∣ n.toInt
      · -- p ∣ n: returns false; p ∈ [2, n) is a witness divisor, so n is not prime.
        right
        refine ⟨is_prime_at_mod_zero_step n p h_n_nn h_p_pos h_pp_fits h_pp_le_n hdvd, ?_⟩
        intro h_prime
        -- p < n: p ≤ p² ≤ n; if p = n then p² ≤ n becomes n² ≤ n, impossible since n ≥ 2.
        have h_p_lt_n : p.toInt < n.toInt := by
          rcases Decidable.em (p.toInt < n.toInt) with h | h
          · exact h
          · exfalso
            have h_n_le_p : n.toInt ≤ p.toInt := by omega
            -- p² ≤ n ≤ p so p² ≤ p, but 2*p ≤ p*p (since p ≥ 2),
            -- chaining: 2p ≤ p, so p ≤ 0, contradicting p ≥ 2.
            have h_pp_le_p : p.toInt * p.toInt ≤ p.toInt :=
              Int.le_trans h_pp_le_n h_n_le_p
            have h_2p_le_pp : 2 * p.toInt ≤ p.toInt * p.toInt :=
              Int.mul_le_mul_of_nonneg_right h_p_lo h_p_nn
            omega
        obtain ⟨_, h_no⟩ := h_prime
        exact h_no p.toInt h_p_lo h_p_lt_n hdvd
      · -- ¬ p ∣ n: recurse on p + 1.
        -- p ≤ 2^31 (since p² ≤ n < 2^62)
        have h_p_le_2_31 : p.toInt ≤ 2 ^ 31 := by
          rcases Decidable.em (p.toInt ≤ 2^31) with h | h
          · exact h
          · exfalso
            have h_p_ge : (2 : Int)^31 + 1 ≤ p.toInt := by omega
            have h_pp_ge : ((2 : Int)^31 + 1) * (2^31 + 1) ≤ p.toInt * p.toInt :=
              Int.mul_le_mul h_p_ge h_p_ge (by decide) h_p_nn
            have h_bound : ((2 : Int)^31 + 1) * (2^31 + 1) > 2^62 := by decide
            omega
        have h_p_plus_one_fits : p.toInt + 1 < 2 ^ 63 := by omega
        have h_p1_no_ov : ¬ Int64.addOverflow p 1 := by
          intro hov
          rw [Int64.addOverflow_iff, i64_one_toInt] at hov
          have h63 : (2 : Int) ^ (64 - 1) = 2 ^ 63 := by decide
          rcases hov with hov | hov
          · rw [h63] at hov
            have h_ge_min := i64_toInt_ge p
            omega
          · rw [h63] at hov
            have h_ge_min := i64_toInt_ge p
            omega
        have h_p1_toInt : (p + 1).toInt = p.toInt + 1 := by
          rw [Int64.toInt_add_of_not_addOverflow h_p1_no_ov, i64_one_toInt]
        have h_p1_lo : 2 ≤ (p + 1).toInt := by rw [h_p1_toInt]; omega
        have h_p1_hi : (p + 1).toInt ≤ 2^31 + 1 := by rw [h_p1_toInt]; omega
        have h_no_small_new :
            ∀ k : Int, 2 ≤ k → k < (p + 1).toInt → ¬ k ∣ n.toInt := by
          intro k hk_lo hk_hi h_k_dvd
          rw [h_p1_toInt] at hk_hi
          rcases Decidable.em (k < p.toInt) with h | h
          · exact h_no_small k hk_lo h h_k_dvd
          · have h_k_eq_p : k = p.toInt := by omega
            rw [h_k_eq_p] at h_k_dvd
            exact hdvd h_k_dvd
        -- measure decreases: (p+1).toNat = p.toNat + 1
        have h_meas_dec : (2 ^ 33 - (p + 1).toInt.toNat) < m := by
          rw [← h_meas, h_p1_toInt]
          have h_p_eq : (p.toInt.toNat : Int) = p.toInt := Int.toNat_of_nonneg h_p_nn
          have h_p1_nn : 0 ≤ p.toInt + 1 := by omega
          have h_p1_eq : ((p.toInt + 1).toNat : Int) = p.toInt + 1 :=
            Int.toNat_of_nonneg h_p1_nn
          have h_p1_succ : (p.toInt + 1).toNat = p.toInt.toNat + 1 := by
            have h_lift : ((p.toInt + 1).toNat : Int) = (p.toInt.toNat + 1 : Nat) := by
              push_cast; rw [h_p1_eq, h_p_eq]
            exact_mod_cast h_lift
          rw [h_p1_succ]
          have h_p_lt_233 : p.toInt.toNat + 1 ≤ 2 ^ 33 := by
            have h_p_lift : (p.toInt.toNat : Int) ≤ 2^31 + 1 := by
              rw [h_p_eq]; exact h_p_hi
            have h_p_nat_le : p.toInt.toNat ≤ 2 ^ 31 + 1 := by exact_mod_cast h_p_lift
            have h_pow : (2 : Nat) ^ 31 + 1 + 1 ≤ 2 ^ 33 := by decide
            omega
          omega
        have h_rec :
            clever_148_x_or_y.is_prime_at n p
              = clever_148_x_or_y.is_prime_at n (p + 1) :=
          is_prime_at_recurse_step n p h_n_nn h_p_pos h_pp_fits h_pp_le_n hdvd h_p_plus_one_fits
        rcases ih _ h_meas_dec (p + 1) rfl h_p1_lo h_p1_hi h_no_small_new with
          ⟨h_true, h_prime⟩ | ⟨h_false, h_not_prime⟩
        · left; refine ⟨?_, h_prime⟩
          rw [h_rec]; exact h_true
        · right; refine ⟨?_, h_not_prime⟩
          rw [h_rec]; exact h_false

/-! ## `is_prime` wrapper lemmas. -/

/-- For `n < 2`, `is_prime n` short-circuits to `ok false`. -/
private theorem is_prime_below_two_lemma (n : i64) (h : n.toInt < 2) :
    clever_148_x_or_y.is_prime n = RustM.ok false := by
  unfold clever_148_x_or_y.is_prime
  have h_lt : n < (2 : i64) := by
    apply Int64.lt_iff_toInt_lt.mpr
    rw [i64_two_toInt]; exact h
  have h_dec : decide (n < (2 : i64)) = true := decide_eq_true h_lt
  simp only [show (n <? (2 : i64) : RustM Bool) =
               (pure (decide (n < (2 : i64))) : RustM Bool) from rfl,
             h_dec, pure_bind, ↓reduceIte]
  rfl

/-- For `n ≥ 2`, `is_prime n` reduces to `is_prime_at n 2`. -/
private theorem is_prime_eq_at_2 (n : i64) (h_lo : 2 ≤ n.toInt) :
    clever_148_x_or_y.is_prime n = clever_148_x_or_y.is_prime_at n (2 : i64) := by
  unfold clever_148_x_or_y.is_prime
  have h_not_lt : ¬ n < (2 : i64) := by
    intro hlt
    have := Int64.lt_iff_toInt_lt.mp hlt
    rw [i64_two_toInt] at this; omega
  have h_dec : decide (n < (2 : i64)) = false := decide_eq_false h_not_lt
  simp only [show (n <? (2 : i64) : RustM Bool) =
               (pure (decide (n < (2 : i64))) : RustM Bool) from rfl,
             h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]

/-- Bundled spec for `is_prime` in the safe regime `n ∈ [2, 2^62)`. -/
private theorem is_prime_spec (n : i64)
    (h_lo : 2 ≤ n.toInt) (h_hi : n.toInt < 2 ^ 62) :
    (clever_148_x_or_y.is_prime n = RustM.ok true ∧ is_prime_int n.toInt)
    ∨ (clever_148_x_or_y.is_prime n = RustM.ok false ∧ ¬ is_prime_int n.toInt) := by
  rw [is_prime_eq_at_2 n h_lo]
  have h_p_lo : 2 ≤ ((2 : i64).toInt) := by rw [i64_two_toInt]; exact Int.le_refl _
  have h_p_hi : ((2 : i64).toInt) ≤ 2 ^ 31 + 1 := by rw [i64_two_toInt]; decide
  have h_no_small : ∀ k : Int, 2 ≤ k → k < ((2 : i64).toInt) → ¬ k ∣ n.toInt := by
    intro k hk_lo hk_hi
    rw [i64_two_toInt] at hk_hi; omega
  exact is_prime_at_spec n h_lo h_hi (2 : i64) h_p_lo h_p_hi h_no_small

/-! ## Main contract clauses. -/

/-- Edge clause: for any `n < 2` (including all negative inputs), `x_or_y`
    returns `y`. Captures the unit test `n_below_two_returns_y` and the
    `n < 2` slice of the `returns_y_when_n_is_not_prime` proptest. -/
theorem x_or_y_below_two
    (n x y : i64) (h : n.toInt < 2) :
    clever_148_x_or_y.x_or_y n x y = RustM.ok y := by
  unfold clever_148_x_or_y.x_or_y
  rw [is_prime_below_two_lemma n h]
  simp only [RustM_ok_bind, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- Postcondition 1 (prime case): when `n` is mathematically prime (and the
    overflow-safety bound `n.toInt < 2 ^ 62` holds), `x_or_y n x y` returns
    `x`. Captures the proptest `returns_x_when_n_is_prime`. -/
theorem x_or_y_returns_x_when_prime
    (n x y : i64)
    (h_lo : 2 ≤ n.toInt) (h_hi : n.toInt < 2 ^ 62)
    (h_prime : is_prime_int n.toInt) :
    clever_148_x_or_y.x_or_y n x y = RustM.ok x := by
  unfold clever_148_x_or_y.x_or_y
  rcases is_prime_spec n h_lo h_hi with ⟨h_true, _⟩ | ⟨_, h_not_prime⟩
  · rw [h_true]
    simp only [RustM_ok_bind, ↓reduceIte]
    rfl
  · exact absurd h_prime h_not_prime

/-- Postcondition 2 (non-prime case, `n ≥ 2`): when `n ≥ 2` is not
    mathematically prime (and the overflow-safety bound `n.toInt < 2 ^ 62`
    holds), `x_or_y n x y` returns `y`. Together with `x_or_y_below_two`,
    this captures the full `returns_y_when_n_is_not_prime` proptest. -/
theorem x_or_y_returns_y_when_not_prime
    (n x y : i64)
    (h_lo : 2 ≤ n.toInt) (h_hi : n.toInt < 2 ^ 62)
    (h_not_prime : ¬ is_prime_int n.toInt) :
    clever_148_x_or_y.x_or_y n x y = RustM.ok y := by
  unfold clever_148_x_or_y.x_or_y
  rcases is_prime_spec n h_lo h_hi with ⟨_, h_prime⟩ | ⟨h_false, _⟩
  · exact absurd h_prime h_not_prime
  · rw [h_false]
    simp only [RustM_ok_bind, Bool.false_eq_true, ↓reduceIte]
    rfl

end Clever_148_x_or_yObligations
