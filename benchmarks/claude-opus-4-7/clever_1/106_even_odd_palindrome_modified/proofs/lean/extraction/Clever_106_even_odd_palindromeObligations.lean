-- Companion obligations file for the `clever_106_even_odd_palindrome` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_106_even_odd_palindrome

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_106_even_odd_palindromeObligations

/-! ## Nat-level oracle for the contract -/

/-- Reverse the base-10 digits of `n` into accumulator `acc`, on `Nat`. -/
private def rev_at_nat (n acc : Nat) : Nat :=
  if h : 0 < n then rev_at_nat (n / 10) (acc * 10 + n % 10)
  else acc
termination_by n
decreasing_by exact Nat.div_lt_self h (by decide)

/-- Boolean palindrome test on `Nat` via digit reversal. -/
private def is_palindrome_nat (n : Nat) : Bool := rev_at_nat n 0 == n

/-- Count of palindromes in `[1, n]` whose remainder modulo 2 equals
    `parity`. -/
private def count_pal : Nat → Nat → Nat
  | 0,     _      => 0
  | k + 1, parity =>
      count_pal k parity
        + (if is_palindrome_nat (k + 1) && (k + 1) % 2 == parity then 1 else 0)

/-! ## Helpers. -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem u64_zero_toNat : (0 : u64).toNat = 0 := rfl
private theorem u64_one_toNat : (1 : u64).toNat = 1 := rfl
private theorem u64_two_toNat : (2 : u64).toNat = 2 := rfl
private theorem u64_ten_toNat : (10 : u64).toNat = 10 := rfl

private theorem u64_ofNat_toNat_of_lt (x : Nat) (h : x < 2 ^ 64) :
    (UInt64.ofNat x).toNat = x :=
  UInt64.toNat_ofNat_of_lt' h

private theorem mod_pure (a b : u64) (h : b ≠ 0) :
    (a %? b : RustM u64) = pure (a % b) := by
  show (rust_primitives.ops.arith.Rem.rem a b : RustM u64) = pure (a % b)
  show (if b = 0 then (.fail .divisionByZero : RustM u64) else pure (a % b)) = _
  rw [if_neg h]

private theorem div_pure (a b : u64) (h : b ≠ 0) :
    (a /? b : RustM u64) = pure (a / b) := by
  show (rust_primitives.ops.arith.Div.div a b : RustM u64) = pure (a / b)
  show (if b = 0 then (.fail .divisionByZero : RustM u64) else pure (a / b)) = _
  rw [if_neg h]

private theorem mul_pure (a b : u64) (h : a.toNat * b.toNat < 2 ^ 64) :
    (a *? b : RustM u64) = pure (a * b) := by
  show (rust_primitives.ops.arith.Mul.mul a b : RustM u64) = pure (a * b)
  show (if BitVec.umulOverflow a.toBitVec b.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (a * b)) = _
  have h_no : ¬ UInt64.mulOverflow a b := by rw [UInt64.mulOverflow_iff]; omega
  have h_bv : BitVec.umulOverflow a.toBitVec b.toBitVec = false := by
    simpa [UInt64.mulOverflow] using h_no
  rw [h_bv]; rfl

private theorem add_pure (a b : u64) (h : a.toNat + b.toNat < 2 ^ 64) :
    (a +? b : RustM u64) = pure (a + b) := by
  show (rust_primitives.ops.arith.Add.add a b : RustM u64) = pure (a + b)
  show (if BitVec.uaddOverflow a.toBitVec b.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (a + b)) = _
  have h_no : ¬ UInt64.addOverflow a b := by rw [UInt64.addOverflow_iff]; omega
  have h_bv : BitVec.uaddOverflow a.toBitVec b.toBitVec = false := by
    simpa [UInt64.addOverflow] using h_no
  rw [h_bv]; rfl

/-! ## Equations for `rev_at_nat`. -/

private theorem rev_at_nat_zero (acc : Nat) : rev_at_nat 0 acc = acc := by
  unfold rev_at_nat
  rw [dif_neg (by decide : ¬ 0 < 0)]

private theorem rev_at_nat_succ (n acc : Nat) (h : 0 < n) :
    rev_at_nat n acc = rev_at_nat (n / 10) (acc * 10 + n % 10) := by
  conv => lhs; unfold rev_at_nat
  rw [dif_pos h]

/-! ## Monotonicity. -/

private theorem rev_at_nat_mono : ∀ (n acc : Nat), acc ≤ rev_at_nat n acc := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro acc
    by_cases h : 0 < n
    · rw [rev_at_nat_succ n acc h]
      have h_lt : n / 10 < n := Nat.div_lt_self h (by decide)
      have ih' := ih (n / 10) h_lt (acc * 10 + n % 10)
      have h_le : acc ≤ acc * 10 + n % 10 := by omega
      omega
    · have h_zero : n = 0 := by omega
      rw [h_zero, rev_at_nat_zero]
      exact Nat.le_refl acc

/-! ## Linear bound: `rev_at_nat n acc ≤ (acc + 1) * 10^j` for `n < 10^j`. -/

private theorem rev_at_nat_bound :
    ∀ (j : Nat) (n acc : Nat), n < 10 ^ j →
      rev_at_nat n acc ≤ (acc + 1) * 10 ^ j := by
  intro j
  induction j with
  | zero =>
    intro n acc h_lt
    have h_n : n = 0 := by simpa using h_lt
    rw [h_n, rev_at_nat_zero, Nat.pow_zero, Nat.mul_one]
    omega
  | succ j ih =>
    intro n acc h_lt
    have h_pow_succ : (10 : Nat) ^ (j + 1) = 10 * 10 ^ j := by
      rw [Nat.pow_succ, Nat.mul_comm]
    by_cases h : 0 < n
    · rw [rev_at_nat_succ n acc h]
      have h_div_lt : n / 10 < 10 ^ j := by
        rw [h_pow_succ] at h_lt
        exact Nat.div_lt_of_lt_mul h_lt
      have ih' := ih (n / 10) (acc * 10 + n % 10) h_div_lt
      have h_mod10 : n % 10 ≤ 9 := by
        have := Nat.mod_lt n (by decide : 0 < 10); omega
      have h_le1 : acc * 10 + n % 10 + 1 ≤ (acc + 1) * 10 := by
        have h_expand : (acc + 1) * 10 = acc * 10 + 10 := by
          rw [Nat.add_mul, Nat.one_mul]
        omega
      have h_chain : (acc * 10 + n % 10 + 1) * 10 ^ j ≤ (acc + 1) * 10 ^ (j + 1) := by
        calc (acc * 10 + n % 10 + 1) * 10 ^ j
            ≤ ((acc + 1) * 10) * 10 ^ j := Nat.mul_le_mul_right _ h_le1
          _ = (acc + 1) * (10 * 10 ^ j) := by rw [Nat.mul_assoc]
          _ = (acc + 1) * 10 ^ (j + 1) := by rw [← h_pow_succ]
      exact Nat.le_trans ih' h_chain
    · have h_n_zero : n = 0 := by omega
      rw [h_n_zero, rev_at_nat_zero]
      have h_pow_pos : 0 < (10 : Nat) ^ (j + 1) :=
        Nat.pow_pos (by decide : (0:Nat) < 10)
      have h1 : (acc + 1) * 10 ^ (j + 1) ≥ (acc + 1) * 1 :=
        Nat.mul_le_mul_left _ h_pow_pos
      rw [Nat.mul_one] at h1
      omega

private theorem rev_at_nat_fits_of_lt_1e19 (n : Nat) (h : n < 10 ^ 19) :
    rev_at_nat n 0 < 2 ^ 64 := by
  have h_bound := rev_at_nat_bound 19 n 0 h
  have h_pow_le : (10 : Nat) ^ 19 < 2 ^ 64 := by decide
  simp at h_bound
  omega

/-! ## Pointwise correctness of `rev_at`. -/

private theorem rev_at_correct :
    ∀ (m : Nat) (n acc : u64),
      n.toNat ≤ m →
      rev_at_nat n.toNat acc.toNat < 2 ^ 64 →
      clever_106_even_odd_palindrome.rev_at n acc
        = RustM.ok (UInt64.ofNat (rev_at_nat n.toNat acc.toNat)) := by
  intro m
  induction m with
  | zero =>
    intro n acc h_le h_fit
    have h_n_zero : n.toNat = 0 := by omega
    have h_n_eq : n = 0 := by
      apply UInt64.toNat_inj.mp; rw [h_n_zero, u64_zero_toNat]
    subst h_n_eq
    unfold clever_106_even_odd_palindrome.rev_at
    simp only [show ((0 : u64) ==? (0 : u64)) =
                 (pure (decide ((0 : u64) = (0 : u64))) : RustM Bool) from rfl,
               pure_bind, decide_true, ↓reduceIte]
    apply congrArg
    apply UInt64.toNat_inj.mp
    rw [u64_zero_toNat, rev_at_nat_zero,
        u64_ofNat_toNat_of_lt acc.toNat acc.toNat_lt]
  | succ m ih =>
    intro n acc h_le h_fit
    by_cases hn : n = 0
    · subst hn
      unfold clever_106_even_odd_palindrome.rev_at
      simp only [show ((0 : u64) ==? (0 : u64)) =
                   (pure (decide ((0 : u64) = (0 : u64))) : RustM Bool) from rfl,
                 pure_bind, decide_true, ↓reduceIte]
      apply congrArg
      apply UInt64.toNat_inj.mp
      rw [u64_zero_toNat, rev_at_nat_zero,
          u64_ofNat_toNat_of_lt acc.toNat acc.toNat_lt]
    · have hn_toNat : 0 < n.toNat := by
        rcases Nat.eq_zero_or_pos n.toNat with hz | hp
        · exfalso
          apply hn
          apply UInt64.toNat_inj.mp
          rw [hz, u64_zero_toNat]
        · exact hp
      unfold clever_106_even_odd_palindrome.rev_at
      have h_dec : (decide (n = (0 : u64))) = false := decide_eq_false hn
      simp only [show (n ==? (0 : u64)) =
                   (pure (decide (n = (0 : u64))) : RustM Bool) from rfl,
                 h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
      have h_fit_succ := h_fit
      rw [rev_at_nat_succ n.toNat acc.toNat hn_toNat] at h_fit_succ
      have h_inner_le :
          acc.toNat * 10 + n.toNat % 10
          ≤ rev_at_nat (n.toNat / 10) (acc.toNat * 10 + n.toNat % 10) :=
        rev_at_nat_mono (n.toNat / 10) (acc.toNat * 10 + n.toNat % 10)
      have h_acc_10_bound : acc.toNat * (10 : u64).toNat < 2 ^ 64 := by
        rw [u64_ten_toNat]; omega
      rw [div_pure n 10 (by decide : (10 : u64) ≠ 0), pure_bind]
      rw [mul_pure acc 10 h_acc_10_bound, pure_bind]
      rw [mod_pure n 10 (by decide : (10 : u64) ≠ 0), pure_bind]
      have h_mul_toNat : (acc * 10).toNat = acc.toNat * 10 := by
        rw [UInt64.toNat_mul_of_lt h_acc_10_bound, u64_ten_toNat]
      have h_mod_toNat : (n % 10).toNat = n.toNat % 10 := by
        rw [UInt64.toNat_mod, u64_ten_toNat]
      have h_add_bound : (acc * 10).toNat + (n % 10).toNat < 2 ^ 64 := by
        rw [h_mul_toNat, h_mod_toNat]; omega
      rw [add_pure (acc * 10) (n % 10) h_add_bound, pure_bind]
      have h_div_toNat : (n / 10).toNat = n.toNat / 10 := by
        rw [UInt64.toNat_div, u64_ten_toNat]
      have h_div_le_m : (n / 10).toNat ≤ m := by
        rw [h_div_toNat]
        have h_div_lt_n : n.toNat / 10 < n.toNat := Nat.div_lt_self hn_toNat (by decide)
        omega
      have h_new_acc_toNat :
          ((acc * 10) + (n % 10)).toNat = acc.toNat * 10 + n.toNat % 10 := by
        rw [UInt64.toNat_add_of_lt h_add_bound, h_mul_toNat, h_mod_toNat]
      have h_new_fit :
          rev_at_nat (n / 10).toNat ((acc * 10) + (n % 10)).toNat < 2 ^ 64 := by
        rw [h_new_acc_toNat, h_div_toNat]; exact h_fit_succ
      rw [ih (n / 10) ((acc * 10) + (n % 10)) h_div_le_m h_new_fit]
      apply congrArg
      apply UInt64.toNat_inj.mp
      rw [u64_ofNat_toNat_of_lt _ h_new_fit, u64_ofNat_toNat_of_lt _ h_fit,
          h_new_acc_toNat, h_div_toNat,
          rev_at_nat_succ n.toNat acc.toNat hn_toNat]

/-! ## Pointwise correctness of `is_palindrome`. -/

private theorem is_palindrome_correct (n : u64) (h_fit : n.toNat < 10 ^ 19) :
    clever_106_even_odd_palindrome.is_palindrome n
      = RustM.ok (is_palindrome_nat n.toNat) := by
  unfold clever_106_even_odd_palindrome.is_palindrome
  have h_rev_fit : rev_at_nat n.toNat (0 : u64).toNat < 2 ^ 64 := by
    rw [u64_zero_toNat]; exact rev_at_nat_fits_of_lt_1e19 n.toNat h_fit
  have h_rev_fit' : rev_at_nat n.toNat 0 < 2 ^ 64 := by
    rw [u64_zero_toNat] at h_rev_fit; exact h_rev_fit
  rw [rev_at_correct n.toNat n 0 (Nat.le_refl _) h_rev_fit]
  simp only [RustM_ok_bind]
  show ((UInt64.ofNat (rev_at_nat n.toNat (0 : u64).toNat)) ==? n : RustM Bool)
        = RustM.ok (is_palindrome_nat n.toNat)
  rw [show (∀ (a b : u64), (a ==? b : RustM Bool) = pure (decide (a = b)))
        from fun _ _ => rfl]
  rw [u64_zero_toNat]
  apply congrArg
  unfold is_palindrome_nat
  by_cases h_eq : rev_at_nat n.toNat 0 = n.toNat
  · have h_u_eq : UInt64.ofNat (rev_at_nat n.toNat 0) = n := by
      apply UInt64.toNat_inj.mp
      rw [u64_ofNat_toNat_of_lt _ h_rev_fit']
      exact h_eq
    rw [decide_eq_true h_u_eq]
    have h_beq : (rev_at_nat n.toNat 0 == n.toNat) = true := beq_iff_eq.mpr h_eq
    rw [h_beq]
  · have h_u_ne : UInt64.ofNat (rev_at_nat n.toNat 0) ≠ n := by
      intro h_eq'
      apply h_eq
      have h := congrArg UInt64.toNat h_eq'
      rw [u64_ofNat_toNat_of_lt _ h_rev_fit'] at h
      exact h
    rw [decide_eq_false h_u_ne]
    have h_bne : (rev_at_nat n.toNat 0 == n.toNat) = false := by
      simp [beq_iff_eq, h_eq]
    rw [h_bne]

/-! ## Bound on `count_pal`. -/

private theorem count_pal_le (n parity : Nat) : count_pal n parity ≤ n := by
  induction n with
  | zero => simp [count_pal]
  | succ n ih =>
    show count_pal n parity + (if is_palindrome_nat (n + 1) && (n + 1) % 2 == parity then 1 else 0) ≤ n + 1
    by_cases h : is_palindrome_nat (n + 1) && (n + 1) % 2 == parity
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega

/-! ## Step lemmas for `count_pal`. -/

private theorem count_pal_succ_pal_match
    (n parity : Nat)
    (h_pal : is_palindrome_nat (n + 1) = true)
    (h_par : (n + 1) % 2 = parity) :
    count_pal (n + 1) parity = count_pal n parity + 1 := by
  show count_pal n parity
        + (if is_palindrome_nat (n + 1) && (n + 1) % 2 == parity then 1 else 0)
       = count_pal n parity + 1
  rw [h_pal]
  have h_cond : ((n + 1) % 2 == parity) = true := by simp [h_par]
  rw [h_cond]
  rfl

private theorem count_pal_succ_pal_mismatch
    (n parity : Nat)
    (h_pal : is_palindrome_nat (n + 1) = true)
    (h_par : (n + 1) % 2 ≠ parity) :
    count_pal (n + 1) parity = count_pal n parity := by
  show count_pal n parity
        + (if is_palindrome_nat (n + 1) && (n + 1) % 2 == parity then 1 else 0)
       = count_pal n parity
  rw [h_pal]
  have h_cond : ((n + 1) % 2 == parity) = false := by simp [h_par]
  rw [h_cond]
  simp

private theorem count_pal_succ_not_pal
    (n parity : Nat)
    (h_pal : is_palindrome_nat (n + 1) = false) :
    count_pal (n + 1) parity = count_pal n parity := by
  show count_pal n parity
        + (if is_palindrome_nat (n + 1) && (n + 1) % 2 == parity then 1 else 0)
       = count_pal n parity
  rw [h_pal]
  simp

/-! ## Contract clauses -/

/-- Boundary clause: `even_odd_palindrome 0 = (0, 0)`. -/
theorem empty_range_is_zero_zero :
    clever_106_even_odd_palindrome.even_odd_palindrome 0
      = RustM.ok (rust_primitives.hax.Tuple2.mk (0 : u64) (0 : u64)) := by
  native_decide

/-- Unit pin from `known`: `even_odd_palindrome 3 = (1, 2)`. -/
theorem even_odd_palindrome_at_3 :
    clever_106_even_odd_palindrome.even_odd_palindrome 3
      = RustM.ok (rust_primitives.hax.Tuple2.mk (1 : u64) (2 : u64)) := by
  native_decide

/-- Unit pin from `known`: `even_odd_palindrome 12 = (4, 6)`. -/
theorem even_odd_palindrome_at_12 :
    clever_106_even_odd_palindrome.even_odd_palindrome 12
      = RustM.ok (rust_primitives.hax.Tuple2.mk (4 : u64) (6 : u64)) := by
  native_decide

/-! ## Strong-induction lemma for `count_at`. -/

private theorem count_at_correct (n : u64) (h_n_fit : n.toNat < 10 ^ 19) :
    ∀ (m : Nat) (k e o : u64),
      n.toNat + 1 - k.toNat ≤ m →
      1 ≤ k.toNat →
      k.toNat ≤ n.toNat + 1 →
      e.toNat = count_pal (k.toNat - 1) 0 →
      o.toNat = count_pal (k.toNat - 1) 1 →
      ∃ e' o' : u64,
        clever_106_even_odd_palindrome.count_at n k e o =
          RustM.ok (rust_primitives.hax.Tuple2.mk e' o') ∧
        e'.toNat = count_pal n.toNat 0 ∧
        o'.toNat = count_pal n.toNat 1 := by
  intro m
  induction m with
  | zero =>
    intro k e o hm h_k_pos h_k_le h_e_inv h_o_inv
    have h_k_eq : k.toNat = n.toNat + 1 := by omega
    refine ⟨e, o, ?_, ?_, ?_⟩
    · unfold clever_106_even_odd_palindrome.count_at
      have h_k_gt_n : k.toNat > n.toNat := by omega
      have h_k_gt_n_u : k > n := UInt64.lt_iff_toNat_lt.mpr h_k_gt_n
      have h_dec : decide (k > n) = true := decide_eq_true h_k_gt_n_u
      simp only [show (k >? n : RustM Bool) =
                   (pure (decide (k > n)) : RustM Bool) from rfl,
                 h_dec, pure_bind, ↓reduceIte]
      rfl
    · rw [h_e_inv]
      have h_arg : k.toNat - 1 = n.toNat := by omega
      rw [h_arg]
    · rw [h_o_inv]
      have h_arg : k.toNat - 1 = n.toNat := by omega
      rw [h_arg]
  | succ m ih =>
    intro k e o hm h_k_pos h_k_le h_e_inv h_o_inv
    by_cases h_k_gt_n : k.toNat > n.toNat
    · have h_k_eq : k.toNat = n.toNat + 1 := by omega
      refine ⟨e, o, ?_, ?_, ?_⟩
      · unfold clever_106_even_odd_palindrome.count_at
        have h_k_gt_n_u : k > n := UInt64.lt_iff_toNat_lt.mpr h_k_gt_n
        have h_dec : decide (k > n) = true := decide_eq_true h_k_gt_n_u
        simp only [show (k >? n : RustM Bool) =
                     (pure (decide (k > n)) : RustM Bool) from rfl,
                   h_dec, pure_bind, ↓reduceIte]
        rfl
      · rw [h_e_inv]
        have h_arg : k.toNat - 1 = n.toNat := by omega
        rw [h_arg]
      · rw [h_o_inv]
        have h_arg : k.toNat - 1 = n.toNat := by omega
        rw [h_arg]
    · have h_k_le_n : k.toNat ≤ n.toNat := by omega
      have h_k_fit_19 : k.toNat < 10 ^ 19 := by
        have : n.toNat < 10 ^ 19 := h_n_fit; omega
      unfold clever_106_even_odd_palindrome.count_at
      have h_not_gt : ¬ k > n := by
        intro h; have := UInt64.lt_iff_toNat_lt.mp h; omega
      have h_dec : decide (k > n) = false := decide_eq_false h_not_gt
      simp only [show (k >? n : RustM Bool) =
                   (pure (decide (k > n)) : RustM Bool) from rfl,
                 h_dec, pure_bind, Bool.false_eq_true, ↓reduceIte]
      rw [is_palindrome_correct k h_k_fit_19]
      simp only [RustM_ok_bind]
      have h_k1_bound : k.toNat + (1 : u64).toNat < 2 ^ 64 := by
        rw [u64_one_toNat]
        have h_pow_lt : (10 : Nat) ^ 19 < 2 ^ 64 := by decide
        omega
      have h_k1_eq : (k +? (1 : u64) : RustM u64) = pure (k + 1) :=
        add_pure k 1 h_k1_bound
      have h_k1_toNat : (k + 1).toNat = k.toNat + 1 := by
        rw [UInt64.toNat_add_of_lt h_k1_bound, u64_one_toNat]
      have h_k1_minus1 : (k + 1).toNat - 1 = k.toNat := by
        rw [h_k1_toNat]; omega
      have h_e_le_km1 : e.toNat ≤ k.toNat - 1 := by
        rw [h_e_inv]; exact count_pal_le (k.toNat - 1) 0
      have h_o_le_km1 : o.toNat ≤ k.toNat - 1 := by
        rw [h_o_inv]; exact count_pal_le (k.toNat - 1) 1
      have h_meas : n.toNat + 1 - (k + 1).toNat ≤ m := by
        rw [h_k1_toNat]; omega
      have h_k1_pos : 1 ≤ (k + 1).toNat := by rw [h_k1_toNat]; omega
      have h_k1_le : (k + 1).toNat ≤ n.toNat + 1 := by rw [h_k1_toNat]; omega
      have h_k_pos' : 0 < k.toNat := by omega
      have h_km1_succ : (k.toNat - 1) + 1 = k.toNat := by omega
      by_cases h_pal : is_palindrome_nat k.toNat = true
      · rw [if_pos h_pal]
        rw [mod_pure k 2 (by decide : (2 : u64) ≠ 0), pure_bind]
        have h_mod2_toNat : (k % 2).toNat = k.toNat % 2 := by
          rw [UInt64.toNat_mod, u64_two_toNat]
        rw [show ((k % 2) ==? (0 : u64) : RustM Bool) =
                pure (decide ((k % 2) = (0 : u64))) from rfl, pure_bind]
        have h_eq_iff_zero : ((k % 2) = (0 : u64)) ↔ (k.toNat % 2 = 0) := by
          constructor
          · intro h
            have := congrArg UInt64.toNat h
            rw [h_mod2_toNat, u64_zero_toNat] at this
            exact this
          · intro h
            apply UInt64.toNat_inj.mp
            rw [h_mod2_toNat, u64_zero_toNat]; exact h
        have h_pal_at_k : is_palindrome_nat ((k.toNat - 1) + 1) = true := by
          rw [h_km1_succ]; exact h_pal
        by_cases h_even : k.toNat % 2 = 0
        · have h_even_u : (k % 2) = (0 : u64) := h_eq_iff_zero.mpr h_even
          have h_dec_true : decide ((k % 2) = (0 : u64)) = true := decide_eq_true h_even_u
          rw [if_pos h_dec_true]
          have h_e1_bound : e.toNat + (1 : u64).toNat < 2 ^ 64 := by
            rw [u64_one_toNat]
            have h_pow_lt : (10 : Nat) ^ 19 < 2 ^ 64 := by decide
            omega
          have h_e1_eq : (e +? (1 : u64) : RustM u64) = pure (e + 1) :=
            add_pure e 1 h_e1_bound
          have h_e1_toNat : (e + 1).toNat = e.toNat + 1 := by
            rw [UInt64.toNat_add_of_lt h_e1_bound, u64_one_toNat]
          rw [h_k1_eq, pure_bind, h_e1_eq, pure_bind]
          have h_par_at_k : ((k.toNat - 1) + 1) % 2 = 0 := by rw [h_km1_succ]; exact h_even
          have h_par_at_k_ne_1 : ((k.toNat - 1) + 1) % 2 ≠ 1 := by rw [h_par_at_k]; decide
          have h_step_e : count_pal k.toNat 0 = count_pal (k.toNat - 1) 0 + 1 := by
            have h := count_pal_succ_pal_match (k.toNat - 1) 0 h_pal_at_k h_par_at_k
            rwa [h_km1_succ] at h
          have h_step_o : count_pal k.toNat 1 = count_pal (k.toNat - 1) 1 := by
            have h := count_pal_succ_pal_mismatch (k.toNat - 1) 1 h_pal_at_k h_par_at_k_ne_1
            rwa [h_km1_succ] at h
          have h_new_e_inv : (e + 1).toNat = count_pal ((k + 1).toNat - 1) 0 := by
            rw [h_e1_toNat, h_e_inv, h_k1_minus1, h_step_e]
          have h_new_o_inv : o.toNat = count_pal ((k + 1).toNat - 1) 1 := by
            rw [h_o_inv, h_k1_minus1, h_step_o]
          exact ih (k + 1) (e + 1) o h_meas h_k1_pos h_k1_le h_new_e_inv h_new_o_inv
        · have h_odd_u : (k % 2) ≠ (0 : u64) := fun h => h_even (h_eq_iff_zero.mp h)
          have h_dec_false : decide ((k % 2) = (0 : u64)) = false := decide_eq_false h_odd_u
          have h_dec_ne_true : ¬ (decide ((k % 2) = (0 : u64)) = true) := by
            rw [h_dec_false]; decide
          rw [if_neg h_dec_ne_true]
          have h_o1_bound : o.toNat + (1 : u64).toNat < 2 ^ 64 := by
            rw [u64_one_toNat]
            have h_pow_lt : (10 : Nat) ^ 19 < 2 ^ 64 := by decide
            omega
          have h_o1_eq : (o +? (1 : u64) : RustM u64) = pure (o + 1) :=
            add_pure o 1 h_o1_bound
          have h_o1_toNat : (o + 1).toNat = o.toNat + 1 := by
            rw [UInt64.toNat_add_of_lt h_o1_bound, u64_one_toNat]
          rw [h_k1_eq, pure_bind, h_o1_eq, pure_bind]
          have h_k_mod_2_odd : k.toNat % 2 = 1 := by
            have h_lt : k.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
            omega
          have h_par_at_k : ((k.toNat - 1) + 1) % 2 = 1 := by
            rw [h_km1_succ]; exact h_k_mod_2_odd
          have h_par_at_k_ne_0 : ((k.toNat - 1) + 1) % 2 ≠ 0 := by
            rw [h_par_at_k]; decide
          have h_step_e : count_pal k.toNat 0 = count_pal (k.toNat - 1) 0 := by
            have h := count_pal_succ_pal_mismatch (k.toNat - 1) 0 h_pal_at_k h_par_at_k_ne_0
            rwa [h_km1_succ] at h
          have h_step_o : count_pal k.toNat 1 = count_pal (k.toNat - 1) 1 + 1 := by
            have h := count_pal_succ_pal_match (k.toNat - 1) 1 h_pal_at_k h_par_at_k
            rwa [h_km1_succ] at h
          have h_new_e_inv : e.toNat = count_pal ((k + 1).toNat - 1) 0 := by
            rw [h_e_inv, h_k1_minus1, h_step_e]
          have h_new_o_inv : (o + 1).toNat = count_pal ((k + 1).toNat - 1) 1 := by
            rw [h_o1_toNat, h_o_inv, h_k1_minus1, h_step_o]
          exact ih (k + 1) e (o + 1) h_meas h_k1_pos h_k1_le h_new_e_inv h_new_o_inv
      · rw [if_neg h_pal]
        have h_pal_false : is_palindrome_nat k.toNat = false := by
          cases h : is_palindrome_nat k.toNat
          · rfl
          · exact absurd h h_pal
        rw [h_k1_eq, pure_bind]
        have h_pal_at_k_false : is_palindrome_nat ((k.toNat - 1) + 1) = false := by
          rw [h_km1_succ]; exact h_pal_false
        have h_step_e : count_pal k.toNat 0 = count_pal (k.toNat - 1) 0 := by
          have h := count_pal_succ_not_pal (k.toNat - 1) 0 h_pal_at_k_false
          rwa [h_km1_succ] at h
        have h_step_o : count_pal k.toNat 1 = count_pal (k.toNat - 1) 1 := by
          have h := count_pal_succ_not_pal (k.toNat - 1) 1 h_pal_at_k_false
          rwa [h_km1_succ] at h
        have h_new_e_inv : e.toNat = count_pal ((k + 1).toNat - 1) 0 := by
          rw [h_e_inv, h_k1_minus1, h_step_e]
        have h_new_o_inv : o.toNat = count_pal ((k + 1).toNat - 1) 1 := by
          rw [h_o_inv, h_k1_minus1, h_step_o]
        exact ih (k + 1) e o h_meas h_k1_pos h_k1_le h_new_e_inv h_new_o_inv

/-! ## Main postconditions. -/

/-- Postcondition (component 0, even count). -/
theorem even_count_matches_spec
    (n : u64) (h_fit : n.toNat < 10 ^ 19) :
    ∃ e o : u64,
      clever_106_even_odd_palindrome.even_odd_palindrome n
        = RustM.ok (rust_primitives.hax.Tuple2.mk e o)
      ∧ e.toNat = count_pal n.toNat 0 := by
  unfold clever_106_even_odd_palindrome.even_odd_palindrome
  have h_init_e : (0 : u64).toNat = count_pal ((1 : u64).toNat - 1) 0 := by
    rw [u64_zero_toNat, u64_one_toNat]
    rfl
  have h_init_o : (0 : u64).toNat = count_pal ((1 : u64).toNat - 1) 1 := by
    rw [u64_zero_toNat, u64_one_toNat]
    rfl
  have h_k_pos : 1 ≤ (1 : u64).toNat := by rw [u64_one_toNat]; omega
  have h_k_le : (1 : u64).toNat ≤ n.toNat + 1 := by
    rw [u64_one_toNat]; omega
  obtain ⟨e, o, h_eq, h_e, h_o⟩ :=
    count_at_correct n h_fit (n.toNat + 1) (1 : u64) (0 : u64) (0 : u64)
      (by rw [u64_one_toNat]; omega) h_k_pos h_k_le h_init_e h_init_o
  exact ⟨e, o, h_eq, h_e⟩

/-- Postcondition (component 1, odd count). -/
theorem odd_count_matches_spec
    (n : u64) (h_fit : n.toNat < 10 ^ 19) :
    ∃ e o : u64,
      clever_106_even_odd_palindrome.even_odd_palindrome n
        = RustM.ok (rust_primitives.hax.Tuple2.mk e o)
      ∧ o.toNat = count_pal n.toNat 1 := by
  unfold clever_106_even_odd_palindrome.even_odd_palindrome
  have h_init_e : (0 : u64).toNat = count_pal ((1 : u64).toNat - 1) 0 := by
    rw [u64_zero_toNat, u64_one_toNat]
    rfl
  have h_init_o : (0 : u64).toNat = count_pal ((1 : u64).toNat - 1) 1 := by
    rw [u64_zero_toNat, u64_one_toNat]
    rfl
  have h_k_pos : 1 ≤ (1 : u64).toNat := by rw [u64_one_toNat]; omega
  have h_k_le : (1 : u64).toNat ≤ n.toNat + 1 := by
    rw [u64_one_toNat]; omega
  obtain ⟨e, o, h_eq, h_e, h_o⟩ :=
    count_at_correct n h_fit (n.toNat + 1) (1 : u64) (0 : u64) (0 : u64)
      (by rw [u64_one_toNat]; omega) h_k_pos h_k_le h_init_e h_init_o
  exact ⟨e, o, h_eq, h_o⟩

end Clever_106_even_odd_palindromeObligations
