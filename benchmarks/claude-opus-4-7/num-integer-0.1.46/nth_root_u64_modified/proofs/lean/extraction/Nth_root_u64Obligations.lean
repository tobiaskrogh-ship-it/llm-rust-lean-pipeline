-- Companion obligations file for the `nth_root_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import nth_root_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Nth_root_u64Obligations

/-! ## Common helper lemmas (shared by sqrt, cbrt, nth_root proofs) -/

@[simp] private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

/-- `Nat.log2 n ≤ 63` whenever `1 ≤ n < 2^64`. -/
private theorem nat_log2_le_63 (n : Nat) (h_pos : 0 < n) (h_lt : n < 2 ^ 64) :
    Nat.log2 n ≤ 63 := by
  have h_lt' : Nat.log2 n < 64 :=
    (Nat.log2_lt (Nat.pos_iff_ne_zero.mp h_pos)).mpr h_lt
  omega

/-- `2 ^ Nat.log2 n ≤ n` for `n ≥ 1`. -/
private theorem nat_pow_log2_le (n : Nat) (h_pos : 0 < n) : 2 ^ Nat.log2 n ≤ n := by
  rcases Nat.lt_or_ge n (2 ^ Nat.log2 n) with h | h
  · exfalso
    have := (Nat.log2_lt (Nat.pos_iff_ne_zero.mp h_pos)).mpr h
    omega
  · exact h

/-- `n < 2 ^ (Nat.log2 n + 1)` for `n ≥ 1`. -/
private theorem nat_lt_pow_succ_log2 (n : Nat) (h_pos : 0 < n) :
    n < 2 ^ (Nat.log2 n + 1) := by
  have h_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp h_pos
  exact (Nat.log2_lt h_ne).mp (Nat.lt_succ_self _)

/-- Polynomial-expansion lemma for `(q + x) * (q + x)`. -/
private theorem nat_sum_sq_expand (q x : Nat) :
    (q + x) * (q + x) = q * q + q * x + q * x + x * x := by
  have h1 : (q + x) * (q + x) = q * (q + x) + x * (q + x) := Nat.add_mul q x (q + x)
  have h2 : q * (q + x) = q * q + q * x := Nat.mul_add q q x
  have h3 : x * (q + x) = x * q + x * x := Nat.mul_add x q x
  have h4 : x * q = q * x := Nat.mul_comm x q
  omega

/-- Refined polynomial identity used by the Babylonian step. -/
private theorem nat_sum_sq_qd (q d : Nat) :
    (q + (q + d)) * (q + (q + d)) = 4 * (q * (q + d)) + d * d := by
  have h_lhs : (q + (q + d)) * (q + (q + d)) =
      q*q + q*(q+d) + q*(q+d) + (q+d)*(q+d) := by
    have := nat_sum_sq_expand q (q + d)
    omega
  have h_expand_q_qd : q * (q + d) = q * q + q * d := Nat.mul_add q q d
  have h_expand_qd_sq : (q + d) * (q + d) = q*q + q*d + q*d + d*d := nat_sum_sq_expand q d
  have h_rhs : 4 * (q * (q + d)) = 4 * (q * q) + 4 * (q * d) := by
    rw [h_expand_q_qd]; omega
  omega

/-- AM-GM: `4qx ≤ (q + x)²`. -/
private theorem nat_amgm (q x : Nat) :
    4 * (q * x) ≤ (q + x) * (q + x) := by
  have h_expand := nat_sum_sq_expand q x
  by_cases hqx : q ≤ x
  · obtain ⟨d, hd⟩ : ∃ d, x = q + d := ⟨x - q, by omega⟩
    have h_sum_sq : (q + (q + d)) * (q + (q + d)) = 4 * (q * (q + d)) + d * d :=
      nat_sum_sq_qd q d
    rw [← hd] at h_sum_sq
    have h_d_sq : d * d ≥ 0 := Nat.zero_le _
    omega
  · have hqx' : x < q := Nat.lt_of_not_le hqx
    obtain ⟨d, hd⟩ : ∃ d, q = x + d := ⟨q - x, by omega⟩
    have h_sum_sq : (x + (x + d)) * (x + (x + d)) = 4 * (x * (x + d)) + d * d :=
      nat_sum_sq_qd x d
    have h_eq : q + x = x + (x + d) := by omega
    rw [h_eq]
    have h_xq : x * (x + d) = x * q := by rw [← hd]
    rw [h_sum_sq, h_xq]
    have h_qx_comm : x * q = q * x := Nat.mul_comm x q
    have h_d_sq : d * d ≥ 0 := Nat.zero_le _
    omega

/-- Sharper AM-GM with surplus: `(q+x)² = 4qx + d²` where `d = |q - x|`. -/
private theorem nat_amgm_eq (q x : Nat) :
    (q + x) * (q + x) = 4 * (q * x) +
      (if q ≤ x then (x - q) * (x - q) else (q - x) * (q - x)) := by
  by_cases hqx : q ≤ x
  · rw [if_pos hqx]
    obtain ⟨d, hd⟩ : ∃ d, x = q + d := ⟨x - q, by omega⟩
    have h_d_eq : x - q = d := by omega
    rw [h_d_eq]
    have h_sum_sq : (q + (q + d)) * (q + (q + d)) = 4 * (q * (q + d)) + d * d :=
      nat_sum_sq_qd q d
    rw [← hd] at h_sum_sq
    exact h_sum_sq
  · rw [if_neg hqx]
    have hqx' : x < q := Nat.lt_of_not_le hqx
    obtain ⟨d, hd⟩ : ∃ d, q = x + d := ⟨q - x, by omega⟩
    have h_d_eq : q - x = d := by omega
    rw [h_d_eq]
    have h_sum_sq : (x + (x + d)) * (x + (x + d)) = 4 * (x * (x + d)) + d * d :=
      nat_sum_sq_qd x d
    have h_qx_eq : q + x = x + (x + d) := by omega
    rw [h_qx_eq, h_sum_sq]
    have h_xq : x * (x + d) = x * q := by rw [← hd]
    rw [h_xq]
    have h_comm : x * q = q * x := Nat.mul_comm x q
    omega

/-- Polynomial identity: `(k + 1) * (k + 1) = k * k + 2 * k + 1`. -/
private theorem nat_succ_sq (k : Nat) : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by
  have h := nat_sum_sq_expand k 1
  have h1 : k * 1 = k := Nat.mul_one k
  have h2 : (1 : Nat) * 1 = 1 := rfl
  omega

/-- `4 * ((f+1)² ) = (2*f + 2) * (2*f + 2)`. -/
private theorem nat_4_mul_succ_sq (f : Nat) :
    4 * ((f + 1) * (f + 1)) = (2 * f + 2) * (2 * f + 2) := by
  have h_lhs : (f + 1) * (f + 1) = f * f + 2 * f + 1 := nat_succ_sq f
  have h_rhs : (2 * f + 2) * (2 * f + 2) = (2 * f) * (2 * f) + 2 * (2 * f) + 2 * (2 * f) + 4 := by
    have h := nat_sum_sq_expand (2 * f) 2
    have h22 : (2 : Nat) * 2 = 4 := rfl
    omega
  have h_2fsq : (2 * f) * (2 * f) = 4 * (f * f) := by
    have : (2 * f) * (2 * f) = 2 * (f * (2 * f)) := Nat.mul_assoc 2 f (2 * f)
    rw [this]
    rw [show f * (2 * f) = 2 * (f * f) from by
      rw [show f * (2 * f) = (f * 2) * f from (Nat.mul_assoc f 2 f).symm,
          Nat.mul_comm f 2, Nat.mul_assoc]]
    rw [show (2 : Nat) * (2 * (f * f)) = 4 * (f * f) from by
      rw [← Nat.mul_assoc]]
  have h_2_2f : 2 * (2 * f) = 4 * f := by
    rw [← Nat.mul_assoc]
  omega

/-- Cauchy-Schwarz: `(p+q)² ≤ 2 (p² + q²)`. -/
private theorem nat_cauchy (p q : Nat) :
    (p + q) * (p + q) ≤ 2 * (p * p + q * q) := by
  have h_expand : (p + q) * (p + q) = p * p + p * q + p * q + q * q :=
    nat_sum_sq_expand p q
  by_cases hpq : p ≤ q
  · obtain ⟨d, hd⟩ : ∃ d, q = p + d := ⟨q - p, by omega⟩
    subst hd
    have h_pq : p * (p + d) = p * p + p * d := Nat.mul_add p p d
    have h_qq := nat_sum_sq_expand p d
    omega
  · obtain ⟨d, hd⟩ : ∃ d, p = q + d := ⟨p - q, by omega⟩
    subst hd
    have h_pq : (q + d) * q = q * q + d * q := Nat.add_mul q d q
    have h_pp := nat_sum_sq_expand q d
    have h_comm : d * q = q * d := Nat.mul_comm d q
    omega

/-- Babylonian step lower bound. Mathematical core of the sqrt proof. -/
private theorem nat_babylonian_lb (a x : Nat) (hx : 0 < x) :
    a < ((a / x + x) / 2 + 1) * ((a / x + x) / 2 + 1) := by
  have h_div : x * (a / x) + a % x = a := Nat.div_add_mod a x
  have h_mod : a % x < x := Nat.mod_lt a hx
  have h_qx_plus_x : (a / x) * x + x ≥ a + 1 := by
    have h_comm : x * (a / x) = (a / x) * x := Nat.mul_comm x _
    omega
  have h_2f_lb : 2 * ((a / x + x) / 2) + 1 ≥ a / x + x := by
    have h_div := Nat.div_add_mod (a / x + x) 2
    have h_m : (a / x + x) % 2 < 2 := Nat.mod_lt _ (by decide)
    omega
  have h_amgm_eq := nat_amgm_eq (a / x) x
  have h_sq_le : (2 * ((a / x + x) / 2) + 1) * (2 * ((a / x + x) / 2) + 1)
      ≥ (a / x + x) * (a / x + x) := Nat.mul_le_mul h_2f_lb h_2f_lb
  have h_2f1_sq_lb : (2 * ((a / x + x) / 2) + 1) * (2 * ((a / x + x) / 2) + 1)
      ≥ 4 * ((a / x) * x) + (if a / x ≤ x then (x - a / x) * (x - a / x)
                              else (a / x - x) * (a / x - x)) := by
    have h := h_sq_le
    omega
  have h_4_f1_sq := nat_4_mul_succ_sq ((a / x + x) / 2)
  have h_2f2 : (2 * ((a / x + x) / 2) + 2) * (2 * ((a / x + x) / 2) + 2)
      = (2 * ((a / x + x) / 2) + 1) * (2 * ((a / x + x) / 2) + 1)
        + 4 * ((a / x + x) / 2) + 3 := by
    have h_eq : 2 * ((a / x + x) / 2) + 2 = (2 * ((a / x + x) / 2) + 1) + 1 := by omega
    rw [h_eq]
    have := nat_succ_sq (2 * ((a / x + x) / 2) + 1)
    have h_2k : 2 * (2 * ((a / x + x) / 2) + 1) = 4 * ((a / x + x) / 2) + 2 := by
      rw [Nat.mul_add, Nat.mul_one]
      rw [show 2 * (2 * ((a / x + x) / 2)) = 4 * ((a / x + x) / 2) from by
        rw [← Nat.mul_assoc]]
    omega
  have h_4qx_lb : 4 * ((a / x) * x) + 4 * x ≥ 4 * a + 4 := by
    have h := h_qx_plus_x; omega
  have h_4f_lb : 4 * ((a / x + x) / 2) ≥ 2 * (a / x) + 2 * x - 2 := by
    have h := h_2f_lb; omega
  have h_lhs_ge : (2 * ((a / x + x) / 2) + 2) * (2 * ((a / x + x) / 2) + 2)
      ≥ 4 * ((a / x) * x) + (if a / x ≤ x then (x - a / x) * (x - a / x)
                              else (a / x - x) * (a / x - x))
        + 4 * ((a / x + x) / 2) + 3 := by
    have h1 := h_2f1_sq_lb
    have h2 := h_2f2
    omega
  have h_gt : (2 * ((a / x + x) / 2) + 2) * (2 * ((a / x + x) / 2) + 2) > 4 * a := by
    by_cases hqx : a / x ≤ x
    · have h_d_val : (if a / x ≤ x then (x - a / x) * (x - a / x)
                     else (a / x - x) * (a / x - x)) = (x - a / x) * (x - a / x) := by
        rw [if_pos hqx]
      rw [h_d_val] at h_lhs_ge
      let d := x - a / x
      have hd_eq : d = x - a / x := rfl
      have hd_plus : d + a / x = x := by simp [hd_eq]; omega
      have h_d_sq_lb : d * d + 1 ≥ 2 * d := by
        rcases Nat.eq_zero_or_pos d with hd0 | hdp
        · rw [hd0]; simp
        · have h_dpred : (d - 1) * (d - 1) + 2 * d = d * d + 1 := by
            have h_d_pred : d - 1 + 1 = d := by omega
            have h_pred_sq := nat_succ_sq (d - 1)
            rw [h_d_pred] at h_pred_sq
            have h_2dm1 : 2 * (d - 1) = 2 * d - 2 := by omega
            rw [h_2dm1] at h_pred_sq
            omega
          have h_sq_nn : (d - 1) * (d - 1) ≥ 0 := Nat.zero_le _
          omega
      have h_d_sq_ge_zero : d * d ≥ 0 := Nat.zero_le _
      have h_d_sq_eq : (x - a / x) * (x - a / x) = d * d := by simp [hd_eq]
      rw [h_d_sq_eq] at h_lhs_ge
      omega
    · have hqx' : a / x > x := Nat.lt_of_not_le hqx
      have h_d_val : (if a / x ≤ x then (x - a / x) * (x - a / x)
                     else (a / x - x) * (a / x - x)) = (a / x - x) * (a / x - x) := by
        rw [if_neg hqx]
      rw [h_d_val] at h_lhs_ge
      have h_d_sq_ge : (a / x - x) * (a / x - x) ≥ 0 := Nat.zero_le _
      omega
  have h_final : 4 * (((a / x + x) / 2 + 1) * ((a / x + x) / 2 + 1)) > 4 * a := by
    have h := h_4_f1_sq
    omega
  exact Nat.lt_of_mul_lt_mul_left h_final

/-- Iter ≤ x ⟹ a < (x+1)². -/
private theorem nat_iter_le_self_implies (a x : Nat) (hx : 0 < x)
    (h_le : (a / x + x) / 2 ≤ x) :
    a < (x + 1) * (x + 1) := by
  have h_lb := nat_babylonian_lb a x hx
  have h_sq_le : ((a / x + x) / 2 + 1) * ((a / x + x) / 2 + 1)
      ≤ (x + 1) * (x + 1) :=
    Nat.mul_le_mul (Nat.add_le_add_right h_le 1) (Nat.add_le_add_right h_le 1)
  omega

/-- Iter ≥ x ⟺ x² ≤ a. -/
private theorem nat_iter_ge_self_iff (a x : Nat) (hx : 0 < x) :
    x ≤ (a / x + x) / 2 ↔ x * x ≤ a := by
  constructor
  · intro h
    have h_sum_ge : a / x + x ≥ 2 * x := by
      have : 2 * x ≤ 2 * ((a/x + x)/2) := by omega
      have h_div2 : 2 * ((a/x + x)/2) ≤ a/x + x := by
        have := Nat.div_add_mod (a/x + x) 2
        omega
      omega
    have h_q_ge : a / x ≥ x := by omega
    have h_div_mul : x * (a / x) ≤ a := Nat.mul_div_le a x
    have h_step : x * x ≤ x * (a / x) := Nat.mul_le_mul_left x h_q_ge
    omega
  · intro h_xx_le
    have h_q_ge : a / x ≥ x := by
      have h_div_ge : (x * x) / x ≤ a / x := Nat.div_le_div_right h_xx_le
      have h_self : (x * x) / x = x := by
        rw [Nat.mul_comm]; exact Nat.mul_div_cancel x hx
      omega
    have h_sum_ge : a / x + x ≥ 2 * x := by omega
    have h_div_ge : (a / x + x) / 2 ≥ (2 * x) / 2 := Nat.div_le_div_right h_sum_ge
    have h_simp : (2 * x) / 2 = x := by
      rw [Nat.mul_comm]; exact Nat.mul_div_cancel x (by decide)
    omega

/-! ## `log2_rec` correctness -/

/-- `log2_rec y count = RustM.ok (count + Nat.log2 y.toNat)` provided no overflow. -/
private theorem log2_rec_correct (y : u64) (count : u32)
    (h_no_ovf : count.toNat + Nat.log2 y.toNat < 2 ^ 32) :
    nth_root_u64.log2_rec y count
      = RustM.ok (UInt32.ofNat (count.toNat + Nat.log2 y.toNat)) := by
  induction hk : y.toNat using Nat.strongRecOn generalizing y count with
  | _ k ih =>
    unfold nth_root_u64.log2_rec
    show ((y <=? (1 : u64)) >>= _) = _
    have h_le_eqq : (y <=? (1 : u64) : RustM Bool) = pure (decide (y ≤ 1)) := rfl
    rw [h_le_eqq]
    simp only [pure_bind]
    subst hk
    by_cases hle : y ≤ 1
    · simp only [decide_eq_true hle, if_true]
      have hyN_le : y.toNat ≤ 1 := UInt64.le_iff_toNat_le.mp hle
      have h_log_zero : Nat.log2 y.toNat = 0 := by
        rcases Nat.lt_or_ge y.toNat 2 with h | h
        · rw [show y.toNat.log2 = if 2 ≤ y.toNat then (y.toNat / 2).log2 + 1 else 0
              from Nat.log2_def y.toNat, if_neg (Nat.not_le.mpr h)]
        · omega
      show RustM.ok count = RustM.ok _
      congr 1
      apply UInt32.toNat_inj.mp
      rw [h_log_zero, Nat.add_zero,
          UInt32.toNat_ofNat_of_lt' (by omega : count.toNat < 2 ^ 32)]
    · simp only [decide_eq_false hle, Bool.false_eq_true, if_false]
      have h_y_ge_2 : 2 ≤ y.toNat := by
        have h_not_le : ¬ y.toNat ≤ 1 := fun h => hle (UInt64.le_iff_toNat_le.mpr h)
        omega
      have h_shr : (y >>>? (1 : i32) : RustM u64) = pure (y >>> (1 : UInt64)) := by
        show (rust_primitives.ops.bit.Shr.shr y (1 : i32) : RustM u64) =
             pure (y >>> (1 : UInt64))
        show (if ((0 : Int32) ≤ (1 : Int32) && (1 : Int32) < 64) then
                pure (y >>> ((1 : Int32).toNatClampNeg.toUInt64))
              else .fail .integerOverflow) = pure (y >>> (1 : UInt64))
        rw [show ((0 : Int32) ≤ (1 : Int32) && (1 : Int32) < 64) = true from rfl]
        simp only [if_true]
        have : (1 : Int32).toNatClampNeg.toUInt64 = (1 : UInt64) := rfl
        rw [this]
      rw [h_shr]
      simp only [pure_bind]
      have h_log_ge_one : 1 ≤ Nat.log2 y.toNat := by
        rw [show y.toNat.log2 = if 2 ≤ y.toNat then (y.toNat / 2).log2 + 1 else 0
            from Nat.log2_def y.toNat, if_pos h_y_ge_2]
        omega
      have h_count_lt : count.toNat + 1 < 2 ^ 32 := by omega
      have h_add : (count +? (1 : u32) : RustM u32) = pure (count + 1) := by
        show (rust_primitives.ops.arith.Add.add count (1 : u32) : RustM u32) =
             pure (count + 1)
        show (if BitVec.uaddOverflow count.toBitVec (1 : u32).toBitVec then
                (.fail .integerOverflow : RustM u32)
              else pure (count + 1)) = pure (count + 1)
        have h_no_ovf' : BitVec.uaddOverflow count.toBitVec ((1 : u32).toBitVec) = false := by
          cases h_eq : BitVec.uaddOverflow count.toBitVec ((1 : u32).toBitVec) with
          | false => rfl
          | true =>
            exfalso
            have : UInt32.addOverflow count (1 : u32) = true := h_eq
            rw [UInt32.addOverflow_iff] at this
            have h1 : (1 : UInt32).toNat = 1 := rfl
            rw [h1] at this
            omega
        rw [h_no_ovf']
        rfl
      rw [h_add]
      simp only [pure_bind]
      have h_yshr : (y >>> (1 : UInt64)).toNat = y.toNat / 2 := by
        rw [UInt64.toNat_shiftRight, UInt64.toNat_one]
        show y.toNat >>> (1 % 64) = _
        rw [show (1 % 64 : Nat) = 1 from rfl, Nat.shiftRight_eq_div_pow,
            show (2 ^ 1 : Nat) = 2 from rfl]
      have h_yshr_lt : (y >>> (1 : UInt64)).toNat < y.toNat := by
        rw [h_yshr]
        exact Nat.div_lt_self (by omega) (by decide)
      have h_cplus : (count + (1 : u32)).toNat = count.toNat + 1 := by
        apply UInt32.toNat_add_of_lt
        have h1 : (1 : UInt32).toNat = 1 := rfl
        rw [h1]; omega
      have h_log_split : Nat.log2 y.toNat = Nat.log2 (y.toNat / 2) + 1 := by
        rw [show y.toNat.log2 = if 2 ≤ y.toNat then (y.toNat / 2).log2 + 1 else 0
            from Nat.log2_def y.toNat, if_pos h_y_ge_2]
      have h_ih_no_ovf : (count + 1).toNat + Nat.log2 (y >>> (1 : UInt64)).toNat < 2 ^ 32 := by
        rw [h_cplus, h_yshr]
        have : Nat.log2 y.toNat = Nat.log2 (y.toNat / 2) + 1 := h_log_split
        omega
      rw [ih _ h_yshr_lt _ (count + 1) h_ih_no_ovf rfl]
      apply congrArg RustM.ok
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_ofNat_of_lt' (by omega : (count + 1).toNat + Nat.log2 (y >>> (1 : UInt64)).toNat < 2 ^ 32)]
      rw [UInt32.toNat_ofNat_of_lt' (by omega : count.toNat + Nat.log2 y.toNat < 2 ^ 32)]
      rw [h_cplus, h_yshr, h_log_split]
      omega

/-! ## `pow2_loop` correctness (used by both sqrt_guess_u64 and cbrt_guess_u64) -/

/-- Reduction of `(g : u64) <<<? (1 : i32)` to `pure (g <<< 1)`. -/
private theorem u64_shl_i32_one (g : UInt64) :
    ((g <<<? (1 : i32)) : RustM u64) = pure (g <<< (1 : UInt64)) := by
  show (rust_primitives.ops.bit.Shl.shl g (1 : i32) : RustM u64) =
       pure (g <<< (1 : UInt64))
  show (if ((0 : Int32) ≤ (1 : Int32) && (1 : Int32) < 64) then
          pure (g <<< ((1 : Int32).toNatClampNeg.toUInt64))
        else .fail .integerOverflow) = pure (g <<< (1 : UInt64))
  rw [show ((0 : Int32) ≤ (1 : Int32) && (1 : Int32) < 64) = true from rfl]
  simp only [if_true]
  have : (1 : Int32).toNatClampNeg.toUInt64 = (1 : UInt64) := rfl
  rw [this]

/-- `pow2_loop k i g = RustM.ok (g * 2^(k - i))` provided no overflow. -/
private theorem pow2_loop_correct (k i : u32) (g : u64)
    (h_i_le : i.toNat ≤ k.toNat)
    (h_k_le : k.toNat ≤ 63)
    (h_no_ovf : g.toNat * 2 ^ (k.toNat - i.toNat) < 2 ^ 64) :
    ∃ g' : u64, nth_root_u64.pow2_loop k i g = RustM.ok g' ∧
      g'.toNat = g.toNat * 2 ^ (k.toNat - i.toNat) := by
  induction hd : k.toNat - i.toNat using Nat.strongRecOn generalizing i g with
  | _ d ih =>
    subst hd
    unfold nth_root_u64.pow2_loop
    have h_ge_eqq : (i >=? k : RustM Bool) = pure (decide (i ≥ k)) := rfl
    rw [h_ge_eqq]
    simp only [pure_bind]
    by_cases h_ge : i ≥ k
    · simp only [decide_eq_true h_ge, if_true]
      have h_i_ge_N : i.toNat ≥ k.toNat := UInt32.le_iff_toNat_le.mp h_ge
      have h_diff_zero : k.toNat - i.toNat = 0 := by omega
      refine ⟨g, rfl, ?_⟩
      rw [h_diff_zero]
      simp
    · simp only [decide_eq_false h_ge, Bool.false_eq_true, if_false]
      have h_i_lt : i.toNat < k.toNat := by
        have h_not : ¬ k.toNat ≤ i.toNat := fun hh => h_ge (UInt32.le_iff_toNat_le.mpr hh)
        omega
      have h_diff_pos : 0 < k.toNat - i.toNat := by omega
      have h_i_lt_63 : i.toNat < 63 := by omega
      have h_add : (i +? (1 : u32) : RustM u32) = pure (i + 1) := by
        show (rust_primitives.ops.arith.Add.add i (1 : u32) : RustM u32) = pure (i + 1)
        show (if BitVec.uaddOverflow i.toBitVec (1 : u32).toBitVec then
                (.fail .integerOverflow : RustM u32)
              else pure (i + 1)) = pure (i + 1)
        have h_no_ovf' : BitVec.uaddOverflow i.toBitVec ((1 : u32).toBitVec) = false := by
          cases h_eq : BitVec.uaddOverflow i.toBitVec ((1 : u32).toBitVec) with
          | false => rfl
          | true =>
            exfalso
            have : UInt32.addOverflow i (1 : u32) = true := h_eq
            rw [UInt32.addOverflow_iff] at this
            have h1 : (1 : UInt32).toNat = 1 := rfl
            rw [h1] at this
            omega
        rw [h_no_ovf']; rfl
      rw [h_add]
      simp only [pure_bind]
      rw [u64_shl_i32_one g]
      simp only [pure_bind]
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := by
        apply UInt32.toNat_add_of_lt
        have h1 : (1 : UInt32).toNat = 1 := rfl
        rw [h1]; omega
      have h_g_mul_2 : g.toNat * 2 < 2 ^ 64 := by
        have h_pow_ge : (2 : Nat) ^ (k.toNat - i.toNat) ≥ 2 := by
          have h_pow_le : 2 ^ 1 ≤ 2 ^ (k.toNat - i.toNat) := by
            apply Nat.pow_le_pow_right
            · decide
            · omega
          have h_p1 : (2 : Nat) ^ 1 = 2 := by decide
          omega
        have h_mul_le : g.toNat * 2 ≤ g.toNat * 2 ^ (k.toNat - i.toNat) :=
          Nat.mul_le_mul_left _ h_pow_ge
        omega
      have h_shl_toNat : (g <<< (1 : UInt64)).toNat = g.toNat * 2 := by
        rw [UInt64.toNat_shiftLeft]
        show g.toNat <<< (1 % 64) % 2 ^ 64 = g.toNat * 2
        rw [show (1 % 64 : Nat) = 1 from rfl, Nat.shiftLeft_eq, show (2 ^ 1 : Nat) = 2 from rfl]
        exact Nat.mod_eq_of_lt h_g_mul_2
      have h_new_diff : k.toNat - (i + 1).toNat = (k.toNat - i.toNat) - 1 := by
        rw [h_i1_toNat]; omega
      have h_new_lt : k.toNat - (i + 1).toNat < k.toNat - i.toNat := by
        rw [h_new_diff]; omega
      have h_pow_identity : g.toNat * 2 * 2 ^ ((k.toNat - i.toNat) - 1)
          = g.toNat * 2 ^ (k.toNat - i.toNat) := by
        have h_pow_split : 2 * 2 ^ ((k.toNat - i.toNat) - 1) = 2 ^ (k.toNat - i.toNat) := by
          have h_eq : 2 ^ ((k.toNat - i.toNat) - 1 + 1) = 2 * 2 ^ ((k.toNat - i.toNat) - 1) := by
            rw [Nat.pow_succ, Nat.mul_comm]
          have h_simp : (k.toNat - i.toNat) - 1 + 1 = k.toNat - i.toNat := by omega
          rw [h_simp] at h_eq
          exact h_eq.symm
        rw [Nat.mul_assoc, h_pow_split]
      have h_new_no_ovf : (g <<< (1 : UInt64)).toNat * 2 ^ (k.toNat - (i + 1).toNat) < 2 ^ 64 := by
        rw [h_shl_toNat, h_new_diff, h_pow_identity]
        exact h_no_ovf
      have h_new_i_le : (i + 1).toNat ≤ k.toNat := by rw [h_i1_toNat]; omega
      obtain ⟨g', hg'_eq, hg'_toNat⟩ :=
        ih (k.toNat - (i + 1).toNat) h_new_lt (i + 1) (g <<< (1 : UInt64))
          h_new_i_le h_new_no_ovf rfl
      refine ⟨g', hg'_eq, ?_⟩
      rw [hg'_toNat, h_shl_toNat, h_new_diff, h_pow_identity]

/-! ## `sqrt_loop_up_spec` and `sqrt_loop_down_spec` -/

/-- `sqrt_loop_up` postcondition. Adapted from `proof_patterns/sqrt_u64_modified`. -/
private theorem sqrt_loop_up_spec (a x xn : u64)
    (h_x_pos : 0 < x.toNat)
    (h_a_pos : 1 ≤ a.toNat)
    (h_x_le : x.toNat ≤ a.toNat)
    (h_xn_eq : xn.toNat = (a.toNat / x.toNat + x.toNat) / 2)
    (h_no_ovf : a.toNat / x.toNat + x.toNat < 2 ^ 64)
    (h_x_sq_lb : 4 * (x.toNat * x.toNat) ≥ a.toNat)
    (h_x_sq_ub : x.toNat * x.toNat ≤ 4 * a.toNat) :
    ∃ x' xn' : u64, nth_root_u64.sqrt_loop_up a x xn = RustM.ok ⟨x', xn'⟩ ∧
      xn'.toNat ≤ x'.toNat ∧
      0 < x'.toNat ∧
      xn'.toNat = (a.toNat / x'.toNat + x'.toNat) / 2 ∧
      a.toNat < (x'.toNat + 1) * (x'.toNat + 1) ∧
      x'.toNat * x'.toNat ≤ 4 * a.toNat := by
  induction hk : (a.toNat + 1 - x.toNat) using Nat.strongRecOn
    generalizing x xn with
  | _ k ih =>
    subst hk
    unfold nth_root_u64.sqrt_loop_up
    have h_lt_eqq : (x <? xn : RustM Bool) = pure (decide (x < xn)) := rfl
    rw [h_lt_eqq]
    simp only [pure_bind]
    by_cases hlt : x < xn
    · simp only [decide_eq_true hlt, if_true]
      have h_x_lt_xn : x.toNat < xn.toNat := UInt64.lt_iff_toNat_lt.mp hlt
      have h_xn_pos : 0 < xn.toNat := by omega
      have h_xn_ne : xn ≠ 0 := by
        intro hcon
        have : xn.toNat = 0 := by rw [hcon]; rfl
        omega
      have h_div : (a /? xn : RustM u64) = pure (a / xn) := by
        show (rust_primitives.ops.arith.Div.div a xn : RustM u64) = pure (a / xn)
        show (if xn = 0 then (.fail .divisionByZero : RustM u64) else pure (a / xn)) = pure (a / xn)
        rw [if_neg h_xn_ne]
      rw [h_div]
      simp only [pure_bind]
      have h_axn_toNat : (a / xn).toNat = a.toNat / xn.toNat := UInt64.toNat_div a xn
      have h_iter_lb : a.toNat < (xn.toNat + 1) * (xn.toNat + 1) := by
        have h_lb := nat_babylonian_lb a.toNat x.toNat h_x_pos
        rw [← h_xn_eq] at h_lb
        exact h_lb
      have h_a_div_xn_le : a.toNat / xn.toNat ≤ xn.toNat + 2 := by
        have h_le : a.toNat ≤ xn.toNat * xn.toNat + 2 * xn.toNat := by
          have h_expand := nat_succ_sq xn.toNat
          omega
        have h_div_le : a.toNat / xn.toNat ≤ (xn.toNat * xn.toNat + 2 * xn.toNat) / xn.toNat :=
          Nat.div_le_div_right h_le
        have h_factor : xn.toNat * xn.toNat + 2 * xn.toNat = (xn.toNat + 2) * xn.toNat := by
          rw [Nat.add_mul]
        rw [h_factor] at h_div_le
        rw [Nat.mul_div_cancel (xn.toNat + 2) h_xn_pos] at h_div_le
        exact h_div_le
      have h_xn_le_a : xn.toNat ≤ a.toNat := by
        rw [h_xn_eq]
        have h_div_le_a : a.toNat / x.toNat ≤ a.toNat := Nat.div_le_self a.toNat x.toNat
        have h_sum_le_2a : a.toNat / x.toNat + x.toNat ≤ 2 * a.toNat := by omega
        have h_half_le : (a.toNat / x.toNat + x.toNat) / 2 ≤ (2 * a.toNat) / 2 :=
          Nat.div_le_div_right h_sum_le_2a
        have h_simp : (2 * a.toNat) / 2 = a.toNat := by
          rw [Nat.mul_comm]; exact Nat.mul_div_cancel a.toNat (by decide)
        omega
      have h_xn_lt_2_63 : xn.toNat < 2 ^ 63 := by
        rw [h_xn_eq]
        have h_le : a.toNat / x.toNat + x.toNat ≤ 2 ^ 64 - 1 := by omega
        have h_div_le : (a.toNat / x.toNat + x.toNat) / 2 ≤ (2 ^ 64 - 1) / 2 :=
          Nat.div_le_div_right h_le
        have h_compute : (2 ^ 64 - 1) / 2 = 2 ^ 63 - 1 := by decide
        omega
      have h_xn_ge_2 : 2 ≤ xn.toNat := by omega
      have h_axn_mul_xn_le : (a.toNat / xn.toNat) * xn.toNat ≤ a.toNat := by
        have : xn.toNat * (a.toNat / xn.toNat) ≤ a.toNat := Nat.mul_div_le a.toNat xn.toNat
        have h_comm : (a.toNat / xn.toNat) * xn.toNat = xn.toNat * (a.toNat / xn.toNat) :=
          Nat.mul_comm _ _
        omega
      have h_a_lt : a.toNat < 2 ^ 64 := a.toNat_lt
      have h_axn_mul_2_le : (a.toNat / xn.toNat) * 2 ≤ a.toNat := by
        have h1 : (a.toNat / xn.toNat) * 2 ≤ (a.toNat / xn.toNat) * xn.toNat :=
          Nat.mul_le_mul_left _ h_xn_ge_2
        omega
      have h_axn_le_2_63 : a.toNat / xn.toNat ≤ 2 ^ 63 - 1 := by
        omega
      have h_no_ovf_rec : a.toNat / xn.toNat + xn.toNat < 2 ^ 64 := by omega
      have h_add : ((a / xn) +? xn : RustM u64) = pure ((a / xn) + xn) := by
        show (rust_primitives.ops.arith.Add.add (a / xn) xn : RustM u64) = pure ((a / xn) + xn)
        show (if BitVec.uaddOverflow (a / xn).toBitVec xn.toBitVec then
                (.fail .integerOverflow : RustM u64)
              else pure ((a / xn) + xn)) = pure ((a / xn) + xn)
        have h_no_ovf' : BitVec.uaddOverflow (a / xn).toBitVec xn.toBitVec = false := by
          cases h_eq : BitVec.uaddOverflow (a / xn).toBitVec xn.toBitVec with
          | false => rfl
          | true =>
            exfalso
            have : UInt64.addOverflow (a / xn) xn = true := h_eq
            rw [UInt64.addOverflow_iff] at this
            rw [h_axn_toNat] at this
            omega
        rw [h_no_ovf']; rfl
      rw [h_add]
      simp only [pure_bind]
      have h_shr : ((a / xn + xn) >>>? (1 : i32) : RustM u64)
          = pure ((a / xn + xn) >>> (1 : UInt64)) := by
        show (rust_primitives.ops.bit.Shr.shr (a / xn + xn) (1 : i32) : RustM u64)
             = pure ((a / xn + xn) >>> (1 : UInt64))
        show (if ((0 : Int32) ≤ (1 : Int32) && (1 : Int32) < 64) then
                pure ((a / xn + xn) >>> ((1 : Int32).toNatClampNeg.toUInt64))
              else .fail .integerOverflow) = pure ((a / xn + xn) >>> (1 : UInt64))
        rw [show ((0 : Int32) ≤ (1 : Int32) && (1 : Int32) < 64) = true from rfl]
        simp only [if_true]
        have : (1 : Int32).toNatClampNeg.toUInt64 = (1 : UInt64) := rfl
        rw [this]
      rw [h_shr]
      simp only [pure_bind]
      have h_new_xn_toNat : ((a / xn + xn) >>> (1 : UInt64)).toNat
          = (a.toNat / xn.toNat + xn.toNat) / 2 := by
        rw [UInt64.toNat_shiftRight, UInt64.toNat_one]
        show (a / xn + xn).toNat >>> (1 % 64) = _
        rw [show (1 % 64 : Nat) = 1 from rfl, Nat.shiftRight_eq_div_pow,
            show (2 ^ 1 : Nat) = 2 from rfl]
        have h_add_toNat : (a / xn + xn).toNat = (a / xn).toNat + xn.toNat := by
          apply UInt64.toNat_add_of_lt
          rw [h_axn_toNat]
          exact h_no_ovf_rec
        rw [h_add_toNat, h_axn_toNat]
      have h_xn_sq_lb_new : 4 * (xn.toNat * xn.toNat) ≥ a.toNat := by
        have h_succ : (xn.toNat + 1) * (xn.toNat + 1) = xn.toNat * xn.toNat + 2 * xn.toNat + 1 :=
          nat_succ_sq xn.toNat
        have h_a_le : a.toNat ≤ xn.toNat * xn.toNat + 2 * xn.toNat := by
          have := h_iter_lb; omega
        have h_xn_sq_ge_xn : xn.toNat * xn.toNat ≥ xn.toNat * 1 :=
          Nat.mul_le_mul_left xn.toNat h_xn_pos
        omega
      have h_xn_sq_ub_new : xn.toNat * xn.toNat ≤ 4 * a.toNat := by
        have h_2xn_le : 2 * xn.toNat ≤ a.toNat / x.toNat + x.toNat := by
          rw [h_xn_eq]
          have h := Nat.div_mul_le_self (a.toNat / x.toNat + x.toNat) 2
          omega
        have h_ax_sq_le : (a.toNat / x.toNat) * (a.toNat / x.toNat) ≤ 4 * a.toNat := by
          have h_div_mul : (a.toNat / x.toNat) * x.toNat ≤ a.toNat := Nat.div_mul_le_self _ _
          have h_sq : ((a.toNat / x.toNat) * x.toNat) * ((a.toNat / x.toNat) * x.toNat)
              ≤ a.toNat * a.toNat := Nat.mul_le_mul h_div_mul h_div_mul
          have h_rearr : ((a.toNat / x.toNat) * x.toNat) * ((a.toNat / x.toNat) * x.toNat)
              = ((a.toNat / x.toNat) * (a.toNat / x.toNat)) * (x.toNat * x.toNat) := by
            have h_assoc1 : ((a.toNat / x.toNat) * x.toNat) * ((a.toNat / x.toNat) * x.toNat)
                = (a.toNat / x.toNat) * (x.toNat * ((a.toNat / x.toNat) * x.toNat)) :=
              Nat.mul_assoc _ _ _
            rw [h_assoc1]
            have h_swap : x.toNat * ((a.toNat / x.toNat) * x.toNat)
                = (a.toNat / x.toNat) * (x.toNat * x.toNat) := by
              rw [← Nat.mul_assoc, Nat.mul_comm x.toNat (a.toNat / x.toNat), Nat.mul_assoc]
            rw [h_swap, ← Nat.mul_assoc]
          rw [h_rearr] at h_sq
          have h_4 : 4 * (((a.toNat / x.toNat) * (a.toNat / x.toNat)) * (x.toNat * x.toNat))
              ≤ 4 * (a.toNat * a.toNat) := Nat.mul_le_mul_left 4 h_sq
          have h_4_rearr : 4 * (((a.toNat / x.toNat) * (a.toNat / x.toNat)) * (x.toNat * x.toNat))
              = ((a.toNat / x.toNat) * (a.toNat / x.toNat)) * (4 * (x.toNat * x.toNat)) := by
            rw [← Nat.mul_assoc, Nat.mul_comm 4 _, Nat.mul_assoc]
          rw [h_4_rearr] at h_4
          have h_mid : ((a.toNat / x.toNat) * (a.toNat / x.toNat)) * a.toNat
              ≤ ((a.toNat / x.toNat) * (a.toNat / x.toNat)) * (4 * (x.toNat * x.toNat)) :=
            Nat.mul_le_mul_left _ h_x_sq_lb
          have h_chain : ((a.toNat / x.toNat) * (a.toNat / x.toNat)) * a.toNat
              ≤ 4 * (a.toNat * a.toNat) := Nat.le_trans h_mid h_4
          have h_eq : 4 * (a.toNat * a.toNat) = (4 * a.toNat) * a.toNat := by
            rw [← Nat.mul_assoc]
          rw [h_eq] at h_chain
          exact Nat.le_of_mul_le_mul_right h_chain h_a_pos
        have h_cauchy_step := nat_cauchy (a.toNat / x.toNat) x.toNat
        have h_4xn_sq_le : (2 * xn.toNat) * (2 * xn.toNat)
            ≤ (a.toNat / x.toNat + x.toNat) * (a.toNat / x.toNat + x.toNat) :=
          Nat.mul_le_mul h_2xn_le h_2xn_le
        have h_2xn_sq : (2 * xn.toNat) * (2 * xn.toNat) = 4 * (xn.toNat * xn.toNat) := by
          have h1 : (2 * xn.toNat) * (2 * xn.toNat) = 2 * (xn.toNat * (2 * xn.toNat)) :=
            Nat.mul_assoc 2 xn.toNat (2 * xn.toNat)
          rw [h1, show xn.toNat * (2 * xn.toNat) = 2 * (xn.toNat * xn.toNat) from by
            rw [← Nat.mul_assoc, Nat.mul_comm xn.toNat 2, Nat.mul_assoc],
              ← Nat.mul_assoc]
        have h_2_sum_le : 2 * ((a.toNat / x.toNat) * (a.toNat / x.toNat) + x.toNat * x.toNat)
            ≤ 2 * (4 * a.toNat + 4 * a.toNat) := by
          have h_add : (a.toNat / x.toNat) * (a.toNat / x.toNat) + x.toNat * x.toNat
              ≤ 4 * a.toNat + 4 * a.toNat := Nat.add_le_add h_ax_sq_le h_x_sq_ub
          exact Nat.mul_le_mul_left 2 h_add
        have h_combined : 4 * (xn.toNat * xn.toNat) ≤ 2 * (4 * a.toNat + 4 * a.toNat) := by
          rw [← h_2xn_sq]
          exact Nat.le_trans h_4xn_sq_le (Nat.le_trans h_cauchy_step h_2_sum_le)
        have h_16a : 2 * (4 * a.toNat + 4 * a.toNat) = 16 * a.toNat := by omega
        rw [h_16a] at h_combined
        have : xn.toNat * xn.toNat ≤ 4 * a.toNat := by omega
        exact this
      have h_measure_lt : a.toNat + 1 - xn.toNat < a.toNat + 1 - x.toNat := by
        omega
      obtain ⟨x', xn', h_eq', h_xn'_le, h_x'_pos, h_xn'_eq, h_x'_ub, h_x'_sq_ub⟩ :=
        ih (a.toNat + 1 - xn.toNat) h_measure_lt xn ((a / xn + xn) >>> (1 : UInt64))
          h_xn_pos h_xn_le_a h_new_xn_toNat h_no_ovf_rec h_xn_sq_lb_new h_xn_sq_ub_new rfl
      exact ⟨x', xn', h_eq', h_xn'_le, h_x'_pos, h_xn'_eq, h_x'_ub, h_x'_sq_ub⟩
    · simp only [decide_eq_false hlt, Bool.false_eq_true, if_false]
      refine ⟨x, xn, rfl, ?_, h_x_pos, h_xn_eq, ?_, h_x_sq_ub⟩
      · have h_not : ¬ x.toNat < xn.toNat := fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h)
        omega
      · have h_x_ge_xn : x.toNat ≥ xn.toNat := by
          have h_not : ¬ x.toNat < xn.toNat := fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h)
          omega
        have h_iter_le : (a.toNat / x.toNat + x.toNat) / 2 ≤ x.toNat := by
          rw [← h_xn_eq]; exact h_x_ge_xn
        exact nat_iter_le_self_implies a.toNat x.toNat h_x_pos h_iter_le

/-- `sqrt_loop_down` postcondition. -/
private theorem sqrt_loop_down_spec (a x xn : u64)
    (h_x_pos : 0 < x.toNat)
    (h_x_ub : a.toNat < (x.toNat + 1) * (x.toNat + 1))
    (h_xn_eq : xn.toNat = (a.toNat / x.toNat + x.toNat) / 2)
    (h_a_pos : 1 ≤ a.toNat)
    (h_x_small : 2 * x.toNat + 2 < 2 ^ 64) :
    ∃ r : u64, nth_root_u64.sqrt_loop_down a x xn = RustM.ok r ∧
      r.toNat * r.toNat ≤ a.toNat ∧
      a.toNat < (r.toNat + 1) * (r.toNat + 1) := by
  induction hk : x.toNat using Nat.strongRecOn generalizing x xn with
  | _ k ih =>
    subst hk
    unfold nth_root_u64.sqrt_loop_down
    have h_gt_eqq : (x >? xn : RustM Bool) = pure (decide (x > xn)) := rfl
    rw [h_gt_eqq]
    simp only [pure_bind]
    by_cases hgt : x > xn
    · simp only [decide_eq_true hgt, if_true]
      have h_xn_lt_x : xn.toNat < x.toNat := UInt64.lt_iff_toNat_lt.mp hgt
      have h_xn_pos : 0 < xn.toNat := by
        rw [h_xn_eq]
        have h_sum_ge_2 : a.toNat / x.toNat + x.toNat ≥ 2 := by
          rcases Nat.lt_or_ge x.toNat 2 with hx_lt | hx_ge
          · have hx1 : x.toNat = 1 := by omega
            rw [hx1, Nat.div_one]
            omega
          · have h_div_nn : 0 ≤ a.toNat / x.toNat := Nat.zero_le _
            omega
        exact Nat.div_pos h_sum_ge_2 (by decide)
      have h_xn_ne : xn ≠ 0 := by
        intro hcon
        have : xn.toNat = 0 := by rw [hcon]; rfl
        omega
      have h_div : (a /? xn : RustM u64) = pure (a / xn) := by
        show (rust_primitives.ops.arith.Div.div a xn : RustM u64) = pure (a / xn)
        show (if xn = 0 then (.fail .divisionByZero : RustM u64) else pure (a / xn)) = pure (a / xn)
        rw [if_neg h_xn_ne]
      rw [h_div]
      simp only [pure_bind]
      have h_axn_toNat : (a / xn).toNat = a.toNat / xn.toNat := UInt64.toNat_div a xn
      have h_iter_lb : a.toNat < (xn.toNat + 1) * (xn.toNat + 1) := by
        have h_lb := nat_babylonian_lb a.toNat x.toNat h_x_pos
        rw [← h_xn_eq] at h_lb
        exact h_lb
      have h_a_div_xn_le : a.toNat / xn.toNat ≤ xn.toNat + 2 := by
        have h_le : a.toNat ≤ xn.toNat * xn.toNat + 2 * xn.toNat := by
          have h_expand := nat_succ_sq xn.toNat
          omega
        have h_div_le : a.toNat / xn.toNat ≤ (xn.toNat * xn.toNat + 2 * xn.toNat) / xn.toNat :=
          Nat.div_le_div_right h_le
        have h_factor : xn.toNat * xn.toNat + 2 * xn.toNat = (xn.toNat + 2) * xn.toNat := by
          rw [Nat.add_mul]
        rw [h_factor] at h_div_le
        rw [Nat.mul_div_cancel (xn.toNat + 2) h_xn_pos] at h_div_le
        exact h_div_le
      have h_new_x_small : 2 * xn.toNat + 2 < 2 ^ 64 := by omega
      have h_no_ovf : a.toNat / xn.toNat + xn.toNat < 2 ^ 64 := by omega
      have h_add : ((a / xn) +? xn : RustM u64) = pure ((a / xn) + xn) := by
        show (rust_primitives.ops.arith.Add.add (a / xn) xn : RustM u64) = pure ((a / xn) + xn)
        show (if BitVec.uaddOverflow (a / xn).toBitVec xn.toBitVec then
                (.fail .integerOverflow : RustM u64)
              else pure ((a / xn) + xn)) = pure ((a / xn) + xn)
        have h_no_ovf' : BitVec.uaddOverflow (a / xn).toBitVec xn.toBitVec = false := by
          cases h_eq : BitVec.uaddOverflow (a / xn).toBitVec xn.toBitVec with
          | false => rfl
          | true =>
            exfalso
            have : UInt64.addOverflow (a / xn) xn = true := h_eq
            rw [UInt64.addOverflow_iff] at this
            rw [h_axn_toNat] at this
            omega
        rw [h_no_ovf']; rfl
      rw [h_add]
      simp only [pure_bind]
      have h_shr : ((a / xn + xn) >>>? (1 : i32) : RustM u64)
          = pure ((a / xn + xn) >>> (1 : UInt64)) := by
        show (rust_primitives.ops.bit.Shr.shr (a / xn + xn) (1 : i32) : RustM u64)
             = pure ((a / xn + xn) >>> (1 : UInt64))
        show (if ((0 : Int32) ≤ (1 : Int32) && (1 : Int32) < 64) then
                pure ((a / xn + xn) >>> ((1 : Int32).toNatClampNeg.toUInt64))
              else .fail .integerOverflow) = pure ((a / xn + xn) >>> (1 : UInt64))
        rw [show ((0 : Int32) ≤ (1 : Int32) && (1 : Int32) < 64) = true from rfl]
        simp only [if_true]
        have : (1 : Int32).toNatClampNeg.toUInt64 = (1 : UInt64) := rfl
        rw [this]
      rw [h_shr]
      simp only [pure_bind]
      have h_new_xn_toNat : ((a / xn + xn) >>> (1 : UInt64)).toNat
          = (a.toNat / xn.toNat + xn.toNat) / 2 := by
        rw [UInt64.toNat_shiftRight, UInt64.toNat_one]
        show (a / xn + xn).toNat >>> (1 % 64) = _
        rw [show (1 % 64 : Nat) = 1 from rfl, Nat.shiftRight_eq_div_pow,
            show (2 ^ 1 : Nat) = 2 from rfl]
        have h_add_toNat : (a / xn + xn).toNat = (a / xn).toNat + xn.toNat := by
          apply UInt64.toNat_add_of_lt
          rw [h_axn_toNat]
          exact h_no_ovf
        rw [h_add_toNat, h_axn_toNat]
      obtain ⟨r, hr_eq, hr_lb, hr_ub⟩ := ih xn.toNat h_xn_lt_x xn ((a / xn + xn) >>> (1 : UInt64))
        h_xn_pos h_iter_lb h_new_xn_toNat h_new_x_small rfl
      exact ⟨r, hr_eq, hr_lb, hr_ub⟩
    · simp only [decide_eq_false hgt, Bool.false_eq_true, if_false]
      refine ⟨x, rfl, ?_, h_x_ub⟩
      have h_x_le_xn : x.toNat ≤ xn.toNat := by
        have h_not : ¬ x.toNat > xn.toNat := fun h => hgt (UInt64.lt_iff_toNat_lt.mpr h)
        omega
      have h_x_le_iter : x.toNat ≤ (a.toNat / x.toNat + x.toNat) / 2 := by
        rw [← h_xn_eq]; exact h_x_le_xn
      exact (nat_iter_ge_self_iff a.toNat x.toNat h_x_pos).mp h_x_le_iter

/-! ## `sqrt_u64` contract clauses

`sqrt_u64 : u64 → RustM u64` is documented as returning the truncated
principal square root. The contract has two universal bounds:

  * **Lower bound** — `r² ≤ a` (always, no precondition).
  * **Upper bound** — `a < (r+1)²`, stated at the `Nat` level so the
    "modulo u64 overflow" caveat from the Rust property test
    disappears (when `r = 2³² − 1` the product `(r+1)*(r+1)` equals
    `2⁶⁴`, still strictly exceeding `a.toNat ≤ 2⁶⁴ − 1`).

The function is total: no precondition is needed. -/

/-- Master existential for `sqrt_u64`: returns some `r` simultaneously
    satisfying the lower and upper square-root bounds. The individual
    contract clauses below project out of this lemma. -/
theorem sqrt_u64_postcondition (a : u64) :
    ∃ r : u64, nth_root_u64.sqrt_u64 a = RustM.ok r ∧
      r.toNat * r.toNat ≤ a.toNat ∧
      a.toNat < (r.toNat + 1) * (r.toNat + 1) := by
  unfold nth_root_u64.sqrt_u64
  dsimp only
  rw [show (a <? (4 : u64) : RustM Bool) = pure (decide (a < 4)) from rfl]
  simp only [pure_bind]
  by_cases hlt : a < 4
  · rw [decide_eq_true hlt]
    simp only [if_true]
    have h_gt_eqq : (a >? (0 : u64) : RustM Bool) = pure (decide (a > 0)) := rfl
    rw [h_gt_eqq]
    simp only [pure_bind]
    have ha_lt_4 : a.toNat < 4 := UInt64.lt_iff_toNat_lt.mp hlt
    by_cases hzero : a > 0
    · rw [decide_eq_true hzero]
      simp only [if_true]
      refine ⟨1, rfl, ?_, ?_⟩
      · have h1 : (1 : u64).toNat = 1 := rfl
        rw [h1]
        have hpos : 0 < a.toNat := UInt64.lt_iff_toNat_lt.mp hzero
        omega
      · have h1 : (1 : u64).toNat = 1 := rfl
        rw [h1]; omega
    · rw [decide_eq_false hzero]
      simp only [Bool.false_eq_true, if_false]
      refine ⟨0, rfl, ?_, ?_⟩
      · have h0 : (0 : u64).toNat = 0 := rfl; rw [h0]; omega
      · have h0 : (0 : u64).toNat = 0 := rfl; rw [h0]
        have ha_zero : a.toNat = 0 := by
          have h_not_pos : ¬ (0 < a.toNat) := fun h => hzero (UInt64.lt_iff_toNat_lt.mpr h)
          omega
        rw [ha_zero]; decide
  · rw [decide_eq_false hlt]
    simp only [Bool.false_eq_true, if_false]
    -- Big-case arm: a ≥ 4. Compute initial guess via sqrt_guess_u64.
    have h_a_ge : 4 ≤ a.toNat := by
      have : ¬ a.toNat < 4 := fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h)
      omega
    have h_a_pos_master : 1 ≤ a.toNat := by omega
    have h_a_lt_2_64 : a.toNat < 2 ^ 64 := a.toNat_lt
    have h_log2_le_63 : Nat.log2 a.toNat ≤ 63 :=
      nat_log2_le_63 a.toNat h_a_pos_master h_a_lt_2_64
    have h_log2_ge_2 : Nat.log2 a.toNat ≥ 2 := by
      rcases Nat.lt_or_ge (Nat.log2 a.toNat) 2 with h | h
      · exfalso
        have h_a_lt_4 : a.toNat < 4 := by
          have h_lt_pow : a.toNat < 2 ^ (Nat.log2 a.toNat + 1) :=
            nat_lt_pow_succ_log2 a.toNat h_a_pos_master
          have h_pow_le : 2 ^ (Nat.log2 a.toNat + 1) ≤ 4 := by
            have h_le : Nat.log2 a.toNat + 1 ≤ 2 := by omega
            have := Nat.pow_le_pow_right (show 1 ≤ 2 from by decide) h_le
            have h_4 : 2 ^ 2 = 4 := by decide
            omega
          omega
        omega
      · exact h
    -- Unfold sqrt_guess_u64
    unfold nth_root_u64.sqrt_guess_u64
    -- log2_u64 reduces to log2_rec with count = 0.
    have h_log2_u64_eq : nth_root_u64.log2_u64 a = RustM.ok (UInt32.ofNat (Nat.log2 a.toNat)) := by
      show nth_root_u64.log2_rec a (0 : UInt32) = _
      have h := log2_rec_correct a (0 : UInt32) (by
        show (0 : UInt32).toNat + Nat.log2 a.toNat < 2 ^ 32
        have h0 : (0 : UInt32).toNat = 0 := rfl
        rw [h0]; omega)
      rw [h]
      have h0 : (0 : UInt32).toNat = 0 := rfl
      rw [h0, Nat.zero_add]
    rw [h_log2_u64_eq]
    simp only [RustM_ok_bind]
    -- hi := UInt32.ofNat (Nat.log2 a.toNat). Now compute (hi +? 2) /? 2.
    have h_hi_toNat : (UInt32.ofNat (Nat.log2 a.toNat)).toNat = Nat.log2 a.toNat :=
      UInt32.toNat_ofNat_of_lt' (by omega : Nat.log2 a.toNat < 2 ^ 32)
    have h_add2 : (UInt32.ofNat (Nat.log2 a.toNat) +? (2 : u32) : RustM u32)
        = pure (UInt32.ofNat (Nat.log2 a.toNat) + 2) := by
      show (rust_primitives.ops.arith.Add.add (UInt32.ofNat (Nat.log2 a.toNat)) (2 : u32) : RustM u32)
           = pure (UInt32.ofNat (Nat.log2 a.toNat) + 2)
      show (if BitVec.uaddOverflow (UInt32.ofNat (Nat.log2 a.toNat)).toBitVec (2 : u32).toBitVec then
              (.fail .integerOverflow : RustM u32)
            else pure (UInt32.ofNat (Nat.log2 a.toNat) + 2)) = _
      have h_no_ovf : BitVec.uaddOverflow (UInt32.ofNat (Nat.log2 a.toNat)).toBitVec
                        (2 : u32).toBitVec = false := by
        cases h_eq : BitVec.uaddOverflow (UInt32.ofNat (Nat.log2 a.toNat)).toBitVec
                        (2 : u32).toBitVec with
        | false => rfl
        | true =>
          exfalso
          have : UInt32.addOverflow (UInt32.ofNat (Nat.log2 a.toNat)) (2 : u32) = true := h_eq
          rw [UInt32.addOverflow_iff] at this
          have h2 : (2 : UInt32).toNat = 2 := rfl
          rw [h_hi_toNat, h2] at this
          omega
      rw [h_no_ovf]; rfl
    rw [h_add2]
    simp only [pure_bind]
    have h_hi_2_toNat : (UInt32.ofNat (Nat.log2 a.toNat) + 2).toNat
                        = Nat.log2 a.toNat + 2 := by
      have h2 : (2 : UInt32).toNat = 2 := rfl
      have h_no_ovf : (UInt32.ofNat (Nat.log2 a.toNat)).toNat + (2 : UInt32).toNat < 2 ^ 32 := by
        rw [h_hi_toNat, h2]; omega
      have h_eq := UInt32.toNat_add_of_lt h_no_ovf
      rw [h_eq, h_hi_toNat, h2]
    -- (... + 2) /? 2.
    have h_div2 : ((UInt32.ofNat (Nat.log2 a.toNat) + 2) /? (2 : u32) : RustM u32)
        = pure ((UInt32.ofNat (Nat.log2 a.toNat) + 2) / 2) := by
      show (rust_primitives.ops.arith.Div.div (UInt32.ofNat (Nat.log2 a.toNat) + 2) (2 : u32)
            : RustM u32)
           = pure ((UInt32.ofNat (Nat.log2 a.toNat) + 2) / 2)
      show (if (2 : u32) = 0 then (.fail .divisionByZero : RustM u32)
            else pure ((UInt32.ofNat (Nat.log2 a.toNat) + 2) / 2)) = _
      rw [if_neg (by decide : (2 : u32) ≠ 0)]
    rw [h_div2]
    simp only [pure_bind]
    -- k := (log2 a + 2) / 2. Then pow2_loop k 0 1 = 2^k.
    have h_k_toNat : ((UInt32.ofNat (Nat.log2 a.toNat) + 2) / 2).toNat
                     = (Nat.log2 a.toNat + 2) / 2 := by
      rw [UInt32.toNat_div, h_hi_2_toNat]
      have h2 : (2 : UInt32).toNat = 2 := rfl
      rw [h2]
    have h_k_ge_2 : 2 ≤ (Nat.log2 a.toNat + 2) / 2 := by
      have h_le : 4 ≤ Nat.log2 a.toNat + 2 := by omega
      have : (4 : Nat) / 2 ≤ (Nat.log2 a.toNat + 2) / 2 := Nat.div_le_div_right h_le
      have h_4d : (4 : Nat) / 2 = 2 := by decide
      omega
    have h_k_le_32 : (Nat.log2 a.toNat + 2) / 2 ≤ 32 := by
      have h_le : Nat.log2 a.toNat + 2 ≤ 65 := by omega
      have : (Nat.log2 a.toNat + 2) / 2 ≤ 65 / 2 := Nat.div_le_div_right h_le
      have h_65d : (65 : Nat) / 2 = 32 := by decide
      omega
    -- Apply pow2_loop_correct with k = (log2 a + 2) / 2, i = 0, g = 1.
    have h_pow_ovf : (1 : u64).toNat * 2 ^ (((UInt32.ofNat (Nat.log2 a.toNat) + 2) / 2).toNat - (0 : u32).toNat) < 2 ^ 64 := by
      have h0 : ((0 : u32)).toNat = 0 := rfl
      have h1 : ((1 : u64)).toNat = 1 := rfl
      rw [h0, h1, h_k_toNat, Nat.sub_zero, Nat.one_mul]
      have h_pow_le : 2 ^ ((Nat.log2 a.toNat + 2) / 2) ≤ 2 ^ 32 :=
        Nat.pow_le_pow_right (by decide) h_k_le_32
      have h_32_lt : (2 : Nat) ^ 32 < 2 ^ 64 := by decide
      omega
    have h_k_i_le : ((0 : u32)).toNat ≤ ((UInt32.ofNat (Nat.log2 a.toNat) + 2) / 2).toNat := by
      have h0 : ((0 : u32)).toNat = 0 := rfl
      rw [h0]; exact Nat.zero_le _
    have h_k_le : ((UInt32.ofNat (Nat.log2 a.toNat) + 2) / 2).toNat ≤ 63 := by
      rw [h_k_toNat]; omega
    obtain ⟨x0, hx0_eq, hx0_toNat⟩ :=
      pow2_loop_correct ((UInt32.ofNat (Nat.log2 a.toNat) + 2) / 2) (0 : u32) (1 : u64)
        h_k_i_le h_k_le h_pow_ovf
    rw [hx0_eq]
    simp only [RustM_ok_bind]
    -- Now x0.toNat = 1 * 2^((log2 a + 2) / 2 - 0) = 2^((log2 a + 2) / 2).
    have h_x0_eq : x0.toNat = 2 ^ ((Nat.log2 a.toNat + 2) / 2) := by
      rw [hx0_toNat]
      have h0 : ((0 : u32)).toNat = 0 := rfl
      have h1 : ((1 : u64)).toNat = 1 := rfl
      rw [h0, h1, h_k_toNat, Nat.sub_zero, Nat.one_mul]
    have h_x0_pos : 0 < x0.toNat := by
      rw [h_x0_eq]; exact Nat.pow_pos (by decide : 0 < 2)
    have h_x0_ge_2 : 2 ≤ x0.toNat := by
      rw [h_x0_eq]
      have : 2 ^ 1 ≤ 2 ^ ((Nat.log2 a.toNat + 2) / 2) :=
        Nat.pow_le_pow_right (by decide) (by omega : 1 ≤ (Nat.log2 a.toNat + 2) / 2)
      have h_p1 : (2 : Nat) ^ 1 = 2 := by decide
      omega
    have h_x0_le_2_32 : x0.toNat ≤ 2 ^ 32 := by
      rw [h_x0_eq]
      exact Nat.pow_le_pow_right (by decide) h_k_le_32
    -- Bounds on k = (log2 a + 2) / 2.
    have h_2k_ge : 2 * ((Nat.log2 a.toNat + 2) / 2) ≥ Nat.log2 a.toNat + 1 := by
      have h_d := Nat.div_add_mod (Nat.log2 a.toNat + 2) 2
      have h_m_lt : (Nat.log2 a.toNat + 2) % 2 < 2 := Nat.mod_lt _ (by decide)
      omega
    have h_2k_le : 2 * ((Nat.log2 a.toNat + 2) / 2) ≤ Nat.log2 a.toNat + 2 := by
      have h_d := Nat.div_mul_le_self (Nat.log2 a.toNat + 2) 2
      omega
    have h_x0_sq_eq : x0.toNat * x0.toNat = 2 ^ (2 * ((Nat.log2 a.toNat + 2) / 2)) := by
      rw [h_x0_eq, ← Nat.pow_add]
      congr 1; omega
    have h_pow_log_le : 2 ^ Nat.log2 a.toNat ≤ a.toNat :=
      nat_pow_log2_le a.toNat h_a_pos_master
    have h_a_lt_pow : a.toNat < 2 ^ (Nat.log2 a.toNat + 1) :=
      nat_lt_pow_succ_log2 a.toNat h_a_pos_master
    -- x0^2 ≤ 2^(log2 a + 2) = 4 * 2^(log2 a) ≤ 4 * a.
    have h_x0_sq_le_4a : x0.toNat * x0.toNat ≤ 4 * a.toNat := by
      rw [h_x0_sq_eq]
      have h_le_log_p2 : 2 ^ (2 * ((Nat.log2 a.toNat + 2) / 2))
          ≤ 2 ^ (Nat.log2 a.toNat + 2) :=
        Nat.pow_le_pow_right (by decide) h_2k_le
      have h_pow_le_4a : 2 ^ (Nat.log2 a.toNat + 2) ≤ 4 * a.toNat := by
        have h_eq : 2 ^ (Nat.log2 a.toNat + 2) = 4 * 2 ^ Nat.log2 a.toNat := by
          rw [show Nat.log2 a.toNat + 2 = Nat.log2 a.toNat + 1 + 1 from by omega,
              Nat.pow_succ, show Nat.log2 a.toNat + 1 = 1 + Nat.log2 a.toNat from by omega,
              Nat.pow_add]
          have h4 : 2 ^ 1 * 2 = 4 := by decide
          have : 2 ^ 1 * 2 ^ Nat.log2 a.toNat * 2 = 4 * 2 ^ Nat.log2 a.toNat := by
            rw [Nat.mul_comm (2 ^ 1 * 2 ^ Nat.log2 a.toNat) 2,
                ← Nat.mul_assoc, Nat.mul_comm 2 (2 ^ 1), h4]
          exact this
        rw [h_eq]
        have := Nat.mul_le_mul_left 4 h_pow_log_le
        exact this
      omega
    -- 4 * x0^2 ≥ a (since x0² ≥ 2^(log2 a + 1) > a).
    have h_4_x0_sq_ge_a : 4 * (x0.toNat * x0.toNat) ≥ a.toNat := by
      rw [h_x0_sq_eq]
      have h_ge_log_p1 : 2 ^ (Nat.log2 a.toNat + 1) ≤ 2 ^ (2 * ((Nat.log2 a.toNat + 2) / 2)) :=
        Nat.pow_le_pow_right (by decide) h_2k_ge
      have h_4_pow_ge : 4 * 2 ^ (2 * ((Nat.log2 a.toNat + 2) / 2)) ≥ 2 ^ (Nat.log2 a.toNat + 1) :=
        Nat.le_trans h_ge_log_p1 (by
          have h_one_le : 1 ≤ 4 := by decide
          have := Nat.le_mul_of_pos_left (2 ^ (2 * ((Nat.log2 a.toNat + 2) / 2)))
            (show 0 < 4 from by decide)
          omega)
      have : a.toNat ≤ 2 ^ (Nat.log2 a.toNat + 1) := Nat.le_of_lt h_a_lt_pow
      omega
    -- x0 ≤ a.toNat since x0² ≤ 4a ≤ a*a for a ≥ 4.
    have h_x0_le_a : x0.toNat ≤ a.toNat := by
      rcases Nat.lt_or_ge a.toNat x0.toNat with h_lt | h_ge
      · exfalso
        have h_x0_ge : a.toNat + 1 ≤ x0.toNat := h_lt
        have h_sq_ge : x0.toNat * x0.toNat ≥ (a.toNat + 1) * (a.toNat + 1) :=
          Nat.mul_le_mul h_x0_ge h_x0_ge
        have h_succ_sq : (a.toNat + 1) * (a.toNat + 1) = a.toNat * a.toNat + 2 * a.toNat + 1 :=
          nat_succ_sq a.toNat
        have h_a_sq_ge_4a : 4 * a.toNat ≤ a.toNat * a.toNat := by
          rw [Nat.mul_comm 4 a.toNat]
          exact Nat.mul_le_mul_left _ h_a_ge
        omega
      · exact h_ge
    -- a/x0 + x0 < 2^64.
    have h_no_ovf_init : a.toNat / x0.toNat + x0.toNat < 2 ^ 64 := by
      have h_div_le : a.toNat / x0.toNat ≤ 4 * x0.toNat := by
        have h_a_le_4_x0_sq : a.toNat ≤ 4 * (x0.toNat * x0.toNat) := h_4_x0_sq_ge_a
        have h_div_le_4_x0 : a.toNat / x0.toNat ≤ (4 * (x0.toNat * x0.toNat)) / x0.toNat :=
          Nat.div_le_div_right h_a_le_4_x0_sq
        have h_simp : (4 * (x0.toNat * x0.toNat)) / x0.toNat = 4 * x0.toNat := by
          rw [show 4 * (x0.toNat * x0.toNat) = (4 * x0.toNat) * x0.toNat from by
            rw [Nat.mul_assoc]]
          exact Nat.mul_div_cancel (4 * x0.toNat) h_x0_pos
        omega
      have h_sum_le : a.toNat / x0.toNat + x0.toNat ≤ 5 * x0.toNat := by omega
      have h_5_x0_le : 5 * x0.toNat ≤ 5 * 2 ^ 32 := Nat.mul_le_mul_left 5 h_x0_le_2_32
      have h_5_pow_lt : 5 * 2 ^ 32 < 2 ^ 64 := by decide
      omega
    -- Reduce a /? x0.
    have h_x0_ne_zero : x0 ≠ 0 := by
      intro hcon
      have : x0.toNat = 0 := by rw [hcon]; rfl
      omega
    have h_div_a_x0 : (a /? x0 : RustM u64) = pure (a / x0) := by
      show (rust_primitives.ops.arith.Div.div a x0 : RustM u64) = pure (a / x0)
      show (if x0 = 0 then (.fail .divisionByZero : RustM u64) else pure (a / x0)) = _
      rw [if_neg h_x0_ne_zero]
    rw [h_div_a_x0]
    simp only [pure_bind]
    have h_a_div_x0_toNat : (a / x0).toNat = a.toNat / x0.toNat := UInt64.toNat_div a x0
    -- Reduce (a / x0) +? x0.
    have h_add_a_x0 : ((a / x0) +? x0 : RustM u64) = pure ((a / x0) + x0) := by
      show (rust_primitives.ops.arith.Add.add (a / x0) x0 : RustM u64) = pure ((a / x0) + x0)
      show (if BitVec.uaddOverflow (a / x0).toBitVec x0.toBitVec then
              (.fail .integerOverflow : RustM u64)
            else pure ((a / x0) + x0)) = _
      have h_no_ovf : BitVec.uaddOverflow (a / x0).toBitVec x0.toBitVec = false := by
        cases h_eq : BitVec.uaddOverflow (a / x0).toBitVec x0.toBitVec with
        | false => rfl
        | true =>
          exfalso
          have : UInt64.addOverflow (a / x0) x0 = true := h_eq
          rw [UInt64.addOverflow_iff] at this
          rw [h_a_div_x0_toNat] at this
          omega
      rw [h_no_ovf]; rfl
    rw [h_add_a_x0]
    simp only [pure_bind]
    have h_sum_toNat : ((a / x0) + x0).toNat = a.toNat / x0.toNat + x0.toNat := by
      apply UInt64.toNat_add_of_lt
      rw [h_a_div_x0_toNat]; exact h_no_ovf_init
    -- Reduce ... >>>? 1.
    have h_shr_xn0 : (((a / x0) + x0) >>>? (1 : i32) : RustM u64)
        = pure (((a / x0) + x0) >>> (1 : UInt64)) := by
      show (rust_primitives.ops.bit.Shr.shr ((a / x0) + x0) (1 : i32) : RustM u64) = _
      show (if ((0 : Int32) ≤ (1 : Int32) && (1 : Int32) < 64) then
              pure (((a / x0) + x0) >>> ((1 : Int32).toNatClampNeg.toUInt64))
            else .fail .integerOverflow) = pure (((a / x0) + x0) >>> (1 : UInt64))
      rw [show ((0 : Int32) ≤ (1 : Int32) && (1 : Int32) < 64) = true from rfl]
      simp only [if_true]
      have : (1 : Int32).toNatClampNeg.toUInt64 = (1 : UInt64) := rfl
      rw [this]
    rw [h_shr_xn0]
    simp only [pure_bind]
    have h_xn0_expr_toNat : (((a / x0) + x0) >>> (1 : UInt64)).toNat
        = (a.toNat / x0.toNat + x0.toNat) / 2 := by
      rw [UInt64.toNat_shiftRight, UInt64.toNat_one]
      show ((a / x0) + x0).toNat >>> (1 % 64) = _
      rw [show (1 % 64 : Nat) = 1 from rfl, Nat.shiftRight_eq_div_pow,
          show (2 ^ 1 : Nat) = 2 from rfl, h_sum_toNat]
    generalize xn0_def : ((a / x0) + x0) >>> (1 : UInt64) = xn0
    rw [xn0_def] at h_xn0_expr_toNat
    have h_xn0_toNat : xn0.toNat = (a.toNat / x0.toNat + x0.toNat) / 2 := h_xn0_expr_toNat
    -- Apply sqrt_loop_up_spec.
    obtain ⟨x1, xn1, h_up_eq, h_xn1_le, h_x1_pos, h_xn1_eq, h_x1_ub, h_x1_sq_ub⟩ :=
      sqrt_loop_up_spec a x0 xn0 h_x0_pos h_a_pos_master h_x0_le_a h_xn0_toNat h_no_ovf_init
        h_4_x0_sq_ge_a h_x0_sq_le_4a
    -- Derive x1 small bound.
    have h_x1_small : 2 * x1.toNat + 2 < 2 ^ 64 := by
      have h_x1_sq_lt : x1.toNat * x1.toNat < 2 ^ 66 := by
        have h_4a_lt : 4 * a.toNat < 4 * 2 ^ 64 :=
          (Nat.mul_lt_mul_left (by decide : 0 < 4)).mpr h_a_lt_2_64
        have h_4_2_64 : 4 * (2 : Nat) ^ 64 = 2 ^ 66 := by decide
        omega
      rcases Nat.lt_or_ge (2 * x1.toNat + 2) (2 ^ 64) with h | h
      · exact h
      · exfalso
        have h_x1_ge : x1.toNat ≥ (2 ^ 64 - 2) / 2 := by omega
        have h_simp : (2 ^ 64 - 2) / 2 = 2 ^ 63 - 1 := by decide
        rw [h_simp] at h_x1_ge
        have h_x1_sq_ge : x1.toNat * x1.toNat ≥ (2 ^ 63 - 1) * (2 ^ 63 - 1) :=
          Nat.mul_le_mul h_x1_ge h_x1_ge
        have h_compute : (2 ^ 63 - 1) * (2 ^ 63 - 1 : Nat) ≥ 2 ^ 66 := by decide
        omega
    -- Apply sqrt_loop_down_spec.
    obtain ⟨r, h_down_eq, hlb, hub⟩ :=
      sqrt_loop_down_spec a x1 xn1 h_x1_pos h_x1_ub h_xn1_eq h_a_pos_master h_x1_small
    refine ⟨r, ?_, hlb, hub⟩
    rw [h_up_eq]
    simp only [RustM_ok_bind]
    exact h_down_eq

/-- Totality / no-panic for `sqrt_u64`. The Rust source has no `panic!`;
    failure modes (`/?` divisor of zero on the initial guess, `+?`
    overflow on `a/x + x`, `>>>?` shift-overflow on the halving,
    `<<<?` shift-overflow on the power-of-two guess) are all ruled
    out by the loop invariants summarised in `sqrt_u64_postcondition`. -/
theorem sqrt_u64_total (a : u64) :
    ∃ r : u64, nth_root_u64.sqrt_u64 a = RustM.ok r := by
  obtain ⟨r, hr, _, _⟩ := sqrt_u64_postcondition a
  exact ⟨r, hr⟩

/-- Lower bound (independent clause) for `sqrt_u64`: `sqrt(a)² ≤ a`.
    Captures the property test `prop_sqrt_lower_bound`. A buggy
    implementation that returns too large a value would fail here. -/
theorem sqrt_u64_lower_bound (a : u64) :
    ∃ r : u64, nth_root_u64.sqrt_u64 a = RustM.ok r ∧
      r.toNat * r.toNat ≤ a.toNat := by
  obtain ⟨r, hr, hlb, _⟩ := sqrt_u64_postcondition a
  exact ⟨r, hr, hlb⟩

/-- Upper bound (independent clause) for `sqrt_u64`: `a < (sqrt(a) + 1)²`,
    stated at `Nat`-level so the Rust test's "modulo overflow" vacuous
    case becomes a genuine inequality that still holds (since
    `a.toNat < 2⁶⁴ ≤ (r+1)²` when `r = 2³² − 1`). Captures
    `prop_sqrt_upper_bound`. Independent from the lower bound: an
    implementation always returning `0` would pass the lower bound
    but fail this one. -/
theorem sqrt_u64_upper_bound (a : u64) :
    ∃ r : u64, nth_root_u64.sqrt_u64 a = RustM.ok r ∧
      a.toNat < (r.toNat + 1) * (r.toNat + 1) := by
  obtain ⟨r, hr, _, hub⟩ := sqrt_u64_postcondition a
  exact ⟨r, hr, hub⟩

/-! ## Cubic helper lemmas (for cbrt_u64 proof) -/

/-- Polynomial identity for `(a + b)²` with the cross-term collected. -/
private theorem nat_sq_expand (a b : Nat) :
    (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  have h1 : (a + b) * (a + b) = a * (a + b) + b * (a + b) := Nat.add_mul a b (a + b)
  have h2 : a * (a + b) = a * a + a * b := Nat.mul_add a a b
  have h3 : b * (a + b) = b * a + b * b := Nat.mul_add b a b
  have h4 : b * a = a * b := Nat.mul_comm b a
  omega

/-- 2-variable AM-GM: `q² + x² ≥ 2qx`. -/
private theorem nat_sq_sum_ge_2_mul (q x : Nat) : 2*(q*x) ≤ q*q + x*x := by
  by_cases h : q ≥ x
  · obtain ⟨d, rfl⟩ : ∃ d, q = x + d := ⟨q - x, by omega⟩
    have h_sq := nat_sq_expand x d
    have h_mul : (x+d)*x = x*x + d*x := by rw [Nat.add_mul]
    rw [h_mul, h_sq]
    have h_dx_xd : d*x = x*d := Nat.mul_comm d x
    omega
  · obtain ⟨d, rfl⟩ : ∃ d, x = q + d := ⟨x - q, by omega⟩
    have h_sq := nat_sq_expand q d
    have h_mul : q*(q+d) = q*q + q*d := by rw [Nat.mul_add]
    rw [h_mul, h_sq]
    omega

/-- Binomial cube expansion. -/
private theorem nat_cube_expand (a b : Nat) :
    (a + b) * (a + b) * (a + b) = a*a*a + 3*(a*a*b) + 3*(a*b*b) + b*b*b := by
  have h_sq : (a + b) * (a + b) = a*a + 2*(a*b) + b*b := nat_sq_expand a b
  show (a + b) * (a + b) * (a + b) = _
  rw [h_sq, Nat.add_mul, Nat.add_mul,
      Nat.mul_add (a*a) a b, Nat.mul_add (2*(a*b)) a b, Nat.mul_add (b*b) a b]
  have h1 : 2*(a*b)*a = 2*(a*a*b) := by
    have h_swap : (a*b)*a = a*a*b := by
      rw [Nat.mul_assoc a b a, Nat.mul_comm b a, ← Nat.mul_assoc]
    rw [Nat.mul_assoc 2 (a*b) a, h_swap]
  have h2 : 2*(a*b)*b = 2*(a*b*b) := Nat.mul_assoc 2 (a*b) b
  have h3 : b*b*a = a*b*b := by
    rw [Nat.mul_comm (b*b) a, ← Nat.mul_assoc]
  rw [h1, h2, h3]
  omega

/-- Cubic AM-GM: `(q + 2x)³ ≥ 27qx²`. -/
private theorem nat_cubic_amgm (q x : Nat) :
    27 * (q * x * x) ≤ (q + 2*x) * (q + 2*x) * (q + 2*x) := by
  have h_cube : (q + 2*x) * (q + 2*x) * (q + 2*x) =
      q*q*q + 6*(q*q*x) + 12*(q*x*x) + 8*(x*x*x) := by
    rw [nat_cube_expand q (2*x)]
    have e1 : q*q*(2*x) = 2*(q*q*x) := by
      rw [← Nat.mul_assoc (q*q) 2 x, Nat.mul_comm (q*q) 2, Nat.mul_assoc]
    have e2 : q*(2*x)*(2*x) = 4*(q*x*x) := by
      have step1 : q*(2*x) = 2*(q*x) := by
        rw [← Nat.mul_assoc q 2 x, Nat.mul_comm q 2, Nat.mul_assoc]
      rw [step1, Nat.mul_assoc 2 (q*x) (2*x)]
      have step2 : (q*x)*(2*x) = 2*((q*x)*x) := by
        rw [← Nat.mul_assoc (q*x) 2 x, Nat.mul_comm (q*x) 2, Nat.mul_assoc]
      rw [step2, ← Nat.mul_assoc]
    have e3 : (2*x)*(2*x)*(2*x) = 8*(x*x*x) := by
      have step1 : (2*x)*(2*x) = 4*(x*x) := by
        rw [← Nat.mul_assoc (2*x) 2 x, Nat.mul_comm (2*x) 2, Nat.mul_assoc]
        rw [show (2*x*x : Nat) = 2*(x*x) from Nat.mul_assoc 2 x x]
        rw [← Nat.mul_assoc 2 2 (x*x)]
      rw [step1, Nat.mul_assoc 4 (x*x) (2*x)]
      have step2 : (x*x)*(2*x) = 2*((x*x)*x) := by
        rw [← Nat.mul_assoc (x*x) 2 x, Nat.mul_comm (x*x) 2, Nat.mul_assoc]
      rw [step2, ← Nat.mul_assoc]
    rw [e1, e2, e3]
    omega
  have h_amgm := nat_sq_sum_ge_2_mul q x
  have h_a : 2*(q*q*x) ≤ q*q*q + q*x*x := by
    have h := Nat.mul_le_mul_right q h_amgm
    have e_lhs : 2*(q*x) * q = 2*(q*q*x) := by
      rw [Nat.mul_assoc 2 (q*x) q, Nat.mul_comm (q*x) q, ← Nat.mul_assoc q q x]
    have e_rhs : (q*q + x*x) * q = q*q*q + q*x*x := by
      rw [Nat.add_mul]
      have h_xxq : x*x*q = q*x*x := by
        rw [Nat.mul_comm (x*x) q, ← Nat.mul_assoc]
      rw [h_xxq]
    rw [e_lhs, e_rhs] at h
    exact h
  have h_b : 2*(q*x*x) ≤ q*q*x + x*x*x := by
    have h := Nat.mul_le_mul_right x h_amgm
    have e_lhs : 2*(q*x) * x = 2*(q*x*x) := by
      rw [Nat.mul_assoc 2 (q*x) x]
    have e_rhs : (q*q + x*x) * x = q*q*x + x*x*x := by
      rw [Nat.add_mul]
    rw [e_lhs, e_rhs] at h
    exact h
  rw [h_cube]
  omega

/-- `(3·n)³ = 27·n³`. -/
private theorem nat_three_mul_cube (n : Nat) :
    (3*n) * (3*n) * (3*n) = 27 * (n*n*n) := by
  have h1 : 3*n*(3*n) = 9*(n*n) := by
    rw [Nat.mul_assoc 3 n (3*n)]
    have h_in : n * (3*n) = 3 * (n*n) := by
      rw [← Nat.mul_assoc n 3 n, Nat.mul_comm n 3, Nat.mul_assoc]
    rw [h_in, ← Nat.mul_assoc]
  rw [h1, Nat.mul_assoc 9 (n*n) (3*n)]
  have h2 : n*n*(3*n) = 3*(n*n*n) := by
    rw [← Nat.mul_assoc (n*n) 3 n, Nat.mul_comm (n*n) 3, Nat.mul_assoc]
  rw [h2, ← Nat.mul_assoc]

/-- Newton step lower bound: `a < ((a/x² + 2x)/3 + 1)³` for `0 < x`. -/
private theorem nat_cubic_newton_lb (a x : Nat) (hx : 0 < x) :
    a < ((a / (x*x) + 2*x) / 3 + 1) * ((a / (x*x) + 2*x) / 3 + 1)
          * ((a / (x*x) + 2*x) / 3 + 1) := by
  have hxx_pos : 0 < x * x := Nat.mul_pos hx hx
  have h_q_lb : a / (x*x) * (x*x) ≤ a := Nat.div_mul_le_self a (x*x)
  have h_q_ub : a < (a / (x*x) + 1) * (x*x) := by
    have h_div_mod := Nat.div_add_mod a (x*x)
    have h_mod_lt : a % (x*x) < x*x := Nat.mod_lt a hxx_pos
    have h_comm : (x*x) * (a / (x*x)) = a / (x*x) * (x*x) := Nat.mul_comm _ _
    have h_factor : a / (x*x) * (x*x) + x*x = (a / (x*x) + 1) * (x*x) := by
      rw [Nat.add_mul, Nat.one_mul]
    omega
  have h_3f : 3 * ((a / (x*x) + 2*x) / 3 + 1) ≥ a / (x*x) + 2*x + 1 := by
    have h_div_mod := Nat.div_add_mod (a / (x*x) + 2*x) 3
    have h_mod_lt : (a / (x*x) + 2*x) % 3 < 3 := Nat.mod_lt _ (by decide)
    omega
  have h_amgm := nat_cubic_amgm (a / (x*x) + 1) x
  have h_q1xx : (a / (x*x) + 1) * x * x = (a / (x*x) + 1) * (x*x) := by
    rw [Nat.mul_assoc]
  have h_q1xx_ge : (a / (x*x) + 1) * (x*x) ≥ a + 1 := by
    have h := h_q_ub; omega
  have h_q1_cube : (a / (x*x) + 1 + 2*x) * (a / (x*x) + 1 + 2*x)
                     * (a / (x*x) + 1 + 2*x) ≥ 27 * a + 27 := by
    have h := h_amgm
    rw [h_q1xx] at h
    have h_mul_27 : 27 * ((a / (x*x) + 1) * (x*x)) ≥ 27 * (a + 1) := by
      exact Nat.mul_le_mul_left 27 h_q1xx_ge
    omega
  have h_rearrange : a / (x*x) + 2*x + 1 = a / (x*x) + 1 + 2*x := by omega
  rw [h_rearrange] at h_3f
  have h_cube_ge : (3 * ((a / (x*x) + 2*x) / 3 + 1))
                     * (3 * ((a / (x*x) + 2*x) / 3 + 1))
                     * (3 * ((a / (x*x) + 2*x) / 3 + 1))
                   ≥ (a / (x*x) + 1 + 2*x) * (a / (x*x) + 1 + 2*x)
                       * (a / (x*x) + 1 + 2*x) :=
    Nat.mul_le_mul (Nat.mul_le_mul h_3f h_3f) h_3f
  have h_27_cube := nat_three_mul_cube ((a / (x*x) + 2*x) / 3 + 1)
  have h_27_f1 : 27 * (((a / (x*x) + 2*x) / 3 + 1) * ((a / (x*x) + 2*x) / 3 + 1)
                     * ((a / (x*x) + 2*x) / 3 + 1)) ≥ 27 * a + 27 := by
    rw [← h_27_cube]
    omega
  omega

/-- Loop-up exit: if `(a/x²+2x)/3 ≤ x` then `a < (x+1)³`. -/
private theorem nat_iter_cbrt_le_self_implies (a x : Nat) (hx : 0 < x)
    (h_le : (a / (x*x) + 2*x) / 3 ≤ x) :
    a < (x + 1) * (x + 1) * (x + 1) := by
  have h_lb := nat_cubic_newton_lb a x hx
  have h_sq_le : ((a / (x*x) + 2*x) / 3 + 1) * ((a / (x*x) + 2*x) / 3 + 1)
                  * ((a / (x*x) + 2*x) / 3 + 1)
                ≤ (x + 1) * (x + 1) * (x + 1) := by
    have h_step : (a / (x*x) + 2*x) / 3 + 1 ≤ x + 1 :=
      Nat.add_le_add_right h_le 1
    exact Nat.mul_le_mul (Nat.mul_le_mul h_step h_step) h_step
  omega

/-- Loop-down exit: `x ≤ (a/x²+2x)/3 ↔ x³ ≤ a`. -/
private theorem nat_iter_cbrt_ge_self_iff (a x : Nat) (hx : 0 < x) :
    x ≤ (a / (x*x) + 2*x) / 3 ↔ x * x * x ≤ a := by
  have hxx_pos : 0 < x * x := Nat.mul_pos hx hx
  constructor
  · intro h
    have h_3x : 3 * x ≤ 3 * ((a / (x*x) + 2*x) / 3) := Nat.mul_le_mul_left 3 h
    have h_div_le : 3 * ((a / (x*x) + 2*x) / 3) ≤ a / (x*x) + 2*x := by
      have h_div_mod := Nat.div_add_mod (a / (x*x) + 2*x) 3
      omega
    have h_q_ge : a / (x*x) ≥ x := by omega
    have h_a_ge : a ≥ a / (x*x) * (x*x) := Nat.div_mul_le_self a (x*x)
    have h_mul_ge : a / (x*x) * (x*x) ≥ x * (x*x) := Nat.mul_le_mul_right (x*x) h_q_ge
    have h_xx_x : x * (x*x) = x * x * x := by rw [← Nat.mul_assoc]
    omega
  · intro h_x3_le
    have h_x3 : x * x * x = x * (x*x) := by rw [Nat.mul_assoc]
    have h_a_ge_xxx : x * (x*x) ≤ a := by rw [← h_x3]; exact h_x3_le
    have h_q_ge : a / (x*x) ≥ x := by
      have h_div_ge : (x * (x*x)) / (x*x) ≤ a / (x*x) := Nat.div_le_div_right h_a_ge_xxx
      have h_self : x * (x*x) / (x*x) = x := Nat.mul_div_cancel x hxx_pos
      omega
    have h_sum_ge : a / (x*x) + 2*x ≥ 3 * x := by omega
    have h_div_ge : (a / (x*x) + 2*x) / 3 ≥ (3 * x) / 3 := Nat.div_le_div_right h_sum_ge
    have h_simp : (3 * x) / 3 = x := by
      rw [Nat.mul_comm]; exact Nat.mul_div_cancel x (by decide)
    omega

/-- Cube expansion: `(y+1)³ = y³ + 3y² + 3y + 1`. -/
private theorem nat_succ_cube (y : Nat) :
    (y + 1) * (y + 1) * (y + 1) = y * y * y + 3 * (y * y) + 3 * y + 1 := by
  have h_sq : (y + 1) * (y + 1) = y * y + 2 * y + 1 := by
    have h := nat_sq_expand y 1
    have h_y1 : y * 1 = y := Nat.mul_one y
    have h_1 : (1 : Nat) * 1 = 1 := rfl
    omega
  rw [h_sq]
  have h_e := Nat.mul_add (y * y + 2 * y + 1) y 1
  have h_e1 := Nat.add_mul (y * y + 2 * y) 1 y
  have h_e2 := Nat.add_mul (y * y) (2 * y) y
  have h_2yy : (2 * y) * y = 2 * (y * y) := by
    rw [Nat.mul_assoc]
  have h_1y : (1 : Nat) * y = y := Nat.one_mul _
  have h_e_one : (y * y + 2 * y + 1) * 1 = y * y + 2 * y + 1 := Nat.mul_one _
  omega

/-- `(2·n)³ = 8·n³`. -/
private theorem nat_two_mul_cube (n : Nat) :
    (2*n) * (2*n) * (2*n) = 8 * (n*n*n) := by
  have h1 : 2*n*(2*n) = 4*(n*n) := by
    rw [Nat.mul_assoc 2 n (2*n)]
    have h_in : n * (2*n) = 2 * (n*n) := by
      rw [← Nat.mul_assoc n 2 n, Nat.mul_comm n 2, Nat.mul_assoc]
    rw [h_in, ← Nat.mul_assoc]
  rw [h1, Nat.mul_assoc 4 (n*n) (2*n)]
  have h2 : n*n*(2*n) = 2*(n*n*n) := by
    rw [← Nat.mul_assoc (n*n) 2 n, Nat.mul_comm (n*n) 2, Nat.mul_assoc]
  rw [h2, ← Nat.mul_assoc]

/-- Bound: `a < (xn+1)³ → a/(xn*xn) ≤ 8*xn` for `xn ≥ 1`. -/
private theorem nat_a_div_xnxn_le_8xn (a xn : Nat) (hxn : 0 < xn)
    (h_a_lt : a < (xn + 1) * (xn + 1) * (xn + 1)) :
    a / (xn * xn) ≤ 8 * xn := by
  have h_xn1_le : xn + 1 ≤ 2 * xn := by omega
  have h_cube_le : (xn + 1) * (xn + 1) * (xn + 1) ≤ (2 * xn) * (2 * xn) * (2 * xn) :=
    Nat.mul_le_mul (Nat.mul_le_mul h_xn1_le h_xn1_le) h_xn1_le
  have h_2xn_cube : (2 * xn) * (2 * xn) * (2 * xn) = 8 * (xn * xn * xn) := nat_two_mul_cube xn
  have h_a_lt' : a < 8 * (xn * xn * xn) := by omega
  have h_factor : 8 * (xn * xn * xn) = (8 * xn) * (xn * xn) := by
    rw [Nat.mul_assoc 8 xn (xn*xn)]
    have h_eq : xn * (xn * xn) = (xn * xn) * xn := Nat.mul_comm _ _
    rw [h_eq, ← Nat.mul_assoc]
  have hxx_pos : 0 < xn * xn := Nat.mul_pos hxn hxn
  rw [h_factor] at h_a_lt'
  have h_div_lt : a / (xn * xn) < 8 * xn :=
    (Nat.div_lt_iff_lt_mul hxx_pos).mpr h_a_lt'
  omega

/-- Reduction of `(x : u64) *? x` when `x.toNat ≤ 2^22`. -/
private theorem u64_mul_self_no_ovf (x : u64) (h : x.toNat ≤ 2 ^ 22) :
    (x *? x : RustM u64) = pure (x * x) := by
  show (rust_primitives.ops.arith.Mul.mul x x : RustM u64) = pure (x * x)
  show (if BitVec.umulOverflow x.toBitVec x.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (x * x)) = pure (x * x)
  have h_no_ovf' : BitVec.umulOverflow x.toBitVec x.toBitVec = false := by
    cases h_eq : BitVec.umulOverflow x.toBitVec x.toBitVec with
    | false => rfl
    | true =>
      exfalso
      have : UInt64.mulOverflow x x = true := h_eq
      rw [UInt64.mulOverflow_iff] at this
      have h_sq_le : x.toNat * x.toNat ≤ 2^22 * 2^22 := Nat.mul_le_mul h h
      have h_pow : (2 : Nat)^22 * 2^22 = 2^44 := by rw [← Nat.pow_add]
      have h_44_64 : (2 : Nat)^44 < 2^64 := by decide
      omega
  rw [h_no_ovf']; rfl

/-- Reduction for `x *? 2` when `x.toNat ≤ 2^22`. -/
private theorem u64_mul_2_no_ovf (x : u64) (h : x.toNat ≤ 2 ^ 22) :
    (x *? (2 : u64) : RustM u64) = pure (x * 2) := by
  show (rust_primitives.ops.arith.Mul.mul x (2 : u64) : RustM u64) = pure (x * 2)
  show (if BitVec.umulOverflow x.toBitVec (2 : u64).toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (x * 2)) = pure (x * 2)
  have h_no_ovf' : BitVec.umulOverflow x.toBitVec (2 : u64).toBitVec = false := by
    cases h_eq : BitVec.umulOverflow x.toBitVec (2 : u64).toBitVec with
    | false => rfl
    | true =>
      exfalso
      have : UInt64.mulOverflow x (2 : u64) = true := h_eq
      rw [UInt64.mulOverflow_iff] at this
      have h2 : (2 : UInt64).toNat = 2 := rfl
      rw [h2] at this
      omega
  rw [h_no_ovf']; rfl

/-! ## Additional cubic helpers used by cbrt_u32_loop and cbrt_loop_down -/

/-- `(2y)·(2y) = 4·y²`. -/
private theorem nat_two_y_sq (y : Nat) : (2 * y) * (2 * y) = 4 * (y * y) := by
  rw [Nat.mul_assoc 2 y (2 * y), Nat.mul_comm y (2 * y),
      Nat.mul_assoc 2 y y, ← Nat.mul_assoc]

/-- `(2y)·(2y)·(2y) = 8·y³`. -/
private theorem nat_two_y_cube (y : Nat) :
    (2 * y) * (2 * y) * (2 * y) = 8 * (y * y * y) := by
  rw [nat_two_y_sq, Nat.mul_assoc 4 (y * y) (2 * y)]
  have h_yy_2y : y * y * (2 * y) = 2 * (y * y * y) := by
    rw [← Nat.mul_assoc (y*y) 2 y, Nat.mul_comm (y*y) 2, Nat.mul_assoc]
  rw [h_yy_2y, ← Nat.mul_assoc]

/-- `(2y+1)² = 4y² + 4y + 1`. -/
private theorem nat_2y1_sq (y : Nat) :
    (2 * y + 1) * (2 * y + 1) = 4 * (y * y) + 4 * y + 1 := by
  have h := nat_sq_expand (2 * y) 1
  have h_4yy : (2 * y) * (2 * y) = 4 * (y * y) := nat_two_y_sq y
  have h_4y : 2 * ((2 * y) * 1) = 4 * y := by
    rw [Nat.mul_one, ← Nat.mul_assoc]
  rw [h_4yy, h_4y, show (1 : Nat) * 1 = 1 from rfl] at h
  exact h

/-- `(2y+1)³ = 8y³ + 12y² + 6y + 1`. -/
private theorem nat_2y1_cube (y : Nat) :
    (2 * y + 1) * (2 * y + 1) * (2 * y + 1) =
    8 * (y * y * y) + 12 * (y * y) + 6 * y + 1 := by
  have h := nat_cube_expand (2 * y) 1
  have h_8y3 : (2 * y) * (2 * y) * (2 * y) = 8 * (y * y * y) := nat_two_y_cube y
  have h_4yy_1 : (2 * y) * (2 * y) * 1 = 4 * (y * y) := by
    rw [Nat.mul_one]; exact nat_two_y_sq y
  have h_2y_11 : (2 * y) * 1 * 1 = 2 * y := by rw [Nat.mul_one, Nat.mul_one]
  have h_111 : (1 : Nat) * 1 * 1 = 1 := rfl
  rw [h_8y3, h_4yy_1, h_2y_11, h_111] at h
  rw [h]
  rw [show 3 * (4 * (y * y)) = 12 * (y * y) from by rw [← Nat.mul_assoc]]
  rw [show 3 * (2 * y) = 6 * y from by rw [← Nat.mul_assoc]]

/-- `b ≤ n / c ↔ b * c ≤ n` for positive `c`. -/
private theorem nat_div_ge_iff_mul_le (b n c : Nat) (hc : 0 < c) :
    b ≤ n / c ↔ b * c ≤ n := by
  constructor
  · intro h
    have h1 : b * c ≤ (n / c) * c := Nat.mul_le_mul_right c h
    have h2 : (n / c) * c ≤ n := Nat.div_mul_le_self n c
    omega
  · intro h
    rcases Nat.lt_or_ge (n / c) b with h_lt | h_ge
    · exfalso
      have h_le' : n / c + 1 ≤ b := h_lt
      have h_mul : (n / c + 1) * c ≤ b * c := Nat.mul_le_mul_right c h_le'
      have h_mod_lt : n % c < c := Nat.mod_lt _ hc
      have h_div_mod : c * (n / c) + n % c = n := Nat.div_add_mod n c
      have h_swap : (n / c) * c = c * (n / c) := Nat.mul_comm _ _
      have h_dist : (n / c + 1) * c = (n / c) * c + c := by
        rw [Nat.add_mul, Nat.one_mul]
      omega
    · exact h_ge

/-! ## `cbrt_u32_loop_correct`: Hacker's-Delight icbrt2 invariant -/

private theorem cbrt_u32_loop_correct
    (s_iter : u32) (x : u32) (y2 : u32) (y : u32) (a_orig : Nat)
    (h_a_lt : a_orig < 2 ^ 32)
    (h_s_le_11 : s_iter.toNat ≤ 11)
    (h_y2_eq : y2.toNat = y.toNat * y.toNat)
    (h_y_cube_le : y.toNat * y.toNat * y.toNat * 8 ^ s_iter.toNat ≤ a_orig)
    (h_a_lt_succ_cube : a_orig <
      (y.toNat + 1) * (y.toNat + 1) * (y.toNat + 1) * 8 ^ s_iter.toNat)
    (h_x_eq : x.toNat = a_orig - y.toNat * y.toNat * y.toNat * 8 ^ s_iter.toNat) :
    ∃ y' : u32, nth_root_u64.cbrt_u32_loop s_iter x y2 y = RustM.ok y' ∧
      y'.toNat * y'.toNat * y'.toNat ≤ a_orig ∧
      a_orig < (y'.toNat + 1) * (y'.toNat + 1) * (y'.toNat + 1) := by
  induction hk : s_iter.toNat using Nat.strongRecOn generalizing s_iter x y2 y with
  | _ k ih =>
    subst hk
    unfold nth_root_u64.cbrt_u32_loop
    have h_eq_eqq : (s_iter ==? (0 : u32) : RustM Bool) = pure (decide (s_iter = 0)) := rfl
    rw [h_eq_eqq]
    simp only [pure_bind]
    by_cases h_zero : s_iter = 0
    · simp only [decide_eq_true h_zero, if_true]
      refine ⟨y, rfl, ?_, ?_⟩
      · have h_s0 : s_iter.toNat = 0 := by rw [h_zero]; rfl
        rw [h_s0] at h_y_cube_le
        simp at h_y_cube_le
        exact h_y_cube_le
      · have h_s0 : s_iter.toNat = 0 := by rw [h_zero]; rfl
        rw [h_s0] at h_a_lt_succ_cube
        simp at h_a_lt_succ_cube
        exact h_a_lt_succ_cube
    · simp only [decide_eq_false h_zero, Bool.false_eq_true, if_false]
      have h_y_lt_2048 : y.toNat < 2048 := by
        rcases Nat.lt_or_ge y.toNat 2048 with hlt | hge
        · exact hlt
        · exfalso
          have h_y3 : 2048 * 2048 * 2048 ≤ y.toNat * y.toNat * y.toNat :=
            Nat.mul_le_mul (Nat.mul_le_mul hge hge) hge
          have h_8s_pos : 1 ≤ 8 ^ s_iter.toNat :=
            Nat.one_le_iff_ne_zero.mpr
              (Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide : 0 < 8)))
          have h_mul : 2048 * 2048 * 2048 * 1 ≤
              y.toNat * y.toNat * y.toNat * 8 ^ s_iter.toNat :=
            Nat.mul_le_mul h_y3 h_8s_pos
          rw [Nat.mul_one] at h_mul
          have h_compute : 2048 * 2048 * 2048 = 8589934592 := by decide
          have h_2_32 : (2 : Nat) ^ 32 = 4294967296 := by decide
          omega
      have h_s_pos : 1 ≤ s_iter.toNat := by
        rcases Nat.eq_zero_or_pos s_iter.toNat with h | h
        · exfalso
          apply h_zero
          apply UInt32.toNat_inj.mp
          rw [h]; rfl
        · exact h
      have h_1_toNat : ((1 : u32)).toNat = 1 := rfl
      have h_2_toNat : ((2 : u32)).toNat = 2 := rfl
      have h_3_toNat : ((3 : u32)).toNat = 3 := rfl
      have h_4_toNat : ((4 : u32)).toNat = 4 := rfl
      have h_sub_step : (s_iter -? (1 : u32) : RustM u32) = pure (s_iter - 1) := by
        show (rust_primitives.ops.arith.Sub.sub s_iter (1 : u32) : RustM u32) =
             pure (s_iter - 1)
        show (if BitVec.usubOverflow s_iter.toBitVec (1 : u32).toBitVec then
                (.fail .integerOverflow : RustM u32)
              else pure (s_iter - 1)) = pure (s_iter - 1)
        have h_no_ovf : BitVec.usubOverflow s_iter.toBitVec ((1 : u32).toBitVec) = false := by
          cases h_eq : BitVec.usubOverflow s_iter.toBitVec ((1 : u32).toBitVec) with
          | false => rfl
          | true =>
            exfalso
            have : UInt32.subOverflow s_iter (1 : u32) = true := h_eq
            rw [UInt32.subOverflow_iff] at this
            rw [h_1_toNat] at this
            omega
        rw [h_no_ovf]; rfl
      rw [h_sub_step]
      simp only [pure_bind]
      have h_sn_toNat : (s_iter - (1 : u32)).toNat = s_iter.toNat - 1 := by
        apply UInt32.toNat_sub_of_le'
        rw [h_1_toNat]; omega
      have h_sn_le_10 : (s_iter - (1 : u32)).toNat ≤ 10 := by rw [h_sn_toNat]; omega
      have h_mul_3 : ((s_iter - (1 : u32)) *? (3 : u32) : RustM u32) =
                     pure ((s_iter - 1) * 3) := by
        show (rust_primitives.ops.arith.Mul.mul (s_iter - 1) (3 : u32) : RustM u32) =
             pure ((s_iter - 1) * 3)
        show (if BitVec.umulOverflow (s_iter - 1).toBitVec (3 : u32).toBitVec then
                (.fail .integerOverflow : RustM u32)
              else pure ((s_iter - 1) * 3)) = _
        have h_no_ovf : BitVec.umulOverflow (s_iter - 1).toBitVec ((3 : u32).toBitVec) = false := by
          cases h_eq : BitVec.umulOverflow (s_iter - 1).toBitVec ((3 : u32).toBitVec) with
          | false => rfl
          | true =>
            exfalso
            have : UInt32.mulOverflow (s_iter - 1) (3 : u32) = true := h_eq
            rw [UInt32.mulOverflow_iff] at this
            rw [h_3_toNat] at this
            have h_le : (s_iter - 1).toNat * 3 ≤ 10 * 3 := Nat.mul_le_mul_right 3 h_sn_le_10
            omega
        rw [h_no_ovf]; rfl
      rw [h_mul_3]
      simp only [pure_bind]
      have h_s_toNat : ((s_iter - (1 : u32)) * (3 : u32)).toNat = (s_iter.toNat - 1) * 3 := by
        rw [UInt32.toNat_mul_of_lt, h_sn_toNat, h_3_toNat]
        rw [h_3_toNat]
        have h_le : (s_iter - 1).toNat * 3 ≤ 10 * 3 := Nat.mul_le_mul_right 3 h_sn_le_10
        rw [h_sn_toNat] at h_le; omega
      have h_s_le_30 : ((s_iter - (1 : u32)) * (3 : u32)).toNat ≤ 30 := by
        rw [h_s_toNat]; omega
      have h_y2_lt : y2.toNat < 2 ^ 22 := by
        rw [h_y2_eq]
        have h_le : y.toNat * y.toNat ≤ 2047 * 2047 :=
          Nat.mul_le_mul (by omega) (by omega)
        have h_c : 2047 * 2047 < (2 : Nat) ^ 22 := by decide
        omega
      have h_mul_4 : (y2 *? (4 : u32) : RustM u32) = pure (y2 * 4) := by
        show (rust_primitives.ops.arith.Mul.mul y2 (4 : u32) : RustM u32) = pure (y2 * 4)
        show (if BitVec.umulOverflow y2.toBitVec (4 : u32).toBitVec then
                (.fail .integerOverflow : RustM u32)
              else pure (y2 * 4)) = _
        have h_no_ovf : BitVec.umulOverflow y2.toBitVec ((4 : u32).toBitVec) = false := by
          cases h_eq : BitVec.umulOverflow y2.toBitVec ((4 : u32).toBitVec) with
          | false => rfl
          | true =>
            exfalso
            have : UInt32.mulOverflow y2 (4 : u32) = true := h_eq
            rw [UInt32.mulOverflow_iff] at this
            rw [h_4_toNat] at this
            have h_le : y2.toNat * 4 ≤ (2 ^ 22 - 1) * 4 := Nat.mul_le_mul_right 4 (by omega)
            have h_c : ((2 : Nat) ^ 22 - 1) * 4 < 2 ^ 32 := by decide
            omega
        rw [h_no_ovf]; rfl
      rw [h_mul_4]
      simp only [pure_bind]
      have h_y2d_toNat : (y2 * (4 : u32)).toNat = y2.toNat * 4 := by
        apply UInt32.toNat_mul_of_lt
        rw [h_4_toNat]
        have h_le : y2.toNat * 4 ≤ (2 ^ 22 - 1) * 4 := Nat.mul_le_mul_right 4 (by omega)
        have h_c : ((2 : Nat) ^ 22 - 1) * 4 < 2 ^ 32 := by decide
        omega
      have h_mul_2 : (y *? (2 : u32) : RustM u32) = pure (y * 2) := by
        show (rust_primitives.ops.arith.Mul.mul y (2 : u32) : RustM u32) = pure (y * 2)
        show (if BitVec.umulOverflow y.toBitVec (2 : u32).toBitVec then
                (.fail .integerOverflow : RustM u32)
              else pure (y * 2)) = _
        have h_no_ovf : BitVec.umulOverflow y.toBitVec ((2 : u32).toBitVec) = false := by
          cases h_eq : BitVec.umulOverflow y.toBitVec ((2 : u32).toBitVec) with
          | false => rfl
          | true =>
            exfalso
            have : UInt32.mulOverflow y (2 : u32) = true := h_eq
            rw [UInt32.mulOverflow_iff] at this
            rw [h_2_toNat] at this
            omega
        rw [h_no_ovf]; rfl
      rw [h_mul_2]
      simp only [pure_bind]
      have h_yd_toNat : (y * (2 : u32)).toNat = y.toNat * 2 := by
        apply UInt32.toNat_mul_of_lt
        rw [h_2_toNat]; omega
      have h_add_y2d_yd : (y2 * 4 +? y * 2 : RustM u32) = pure (y2 * 4 + y * 2) := by
        show (rust_primitives.ops.arith.Add.add (y2 * 4) (y * 2) : RustM u32) = _
        show (if BitVec.uaddOverflow (y2 * 4).toBitVec (y * 2).toBitVec then
                (.fail .integerOverflow : RustM u32)
              else pure (y2 * 4 + y * 2)) = _
        have h_no_ovf : BitVec.uaddOverflow (y2 * 4).toBitVec (y * 2).toBitVec = false := by
          cases h_eq : BitVec.uaddOverflow (y2 * 4).toBitVec (y * 2).toBitVec with
          | false => rfl
          | true =>
            exfalso
            have : UInt32.addOverflow (y2 * 4) (y * 2) = true := h_eq
            rw [UInt32.addOverflow_iff] at this
            rw [h_y2d_toNat, h_yd_toNat] at this
            have h_le2 : y2.toNat * 4 ≤ (2 ^ 22 - 1) * 4 := Nat.mul_le_mul_right 4 (by omega)
            have h_c : ((2 : Nat) ^ 22 - 1) * 4 + 2047 * 2 < 2 ^ 32 := by decide
            omega
        rw [h_no_ovf]; rfl
      rw [h_add_y2d_yd]
      simp only [pure_bind]
      have h_sum_toNat : (y2 * 4 + y * 2).toNat = y2.toNat * 4 + y.toNat * 2 := by
        rw [UInt32.toNat_add_of_lt]
        · rw [h_y2d_toNat, h_yd_toNat]
        rw [h_y2d_toNat, h_yd_toNat]
        have h_le2 : y2.toNat * 4 ≤ (2 ^ 22 - 1) * 4 := Nat.mul_le_mul_right 4 (by omega)
        have h_c : ((2 : Nat) ^ 22 - 1) * 4 + 2047 * 2 < 2 ^ 32 := by decide
        omega
      have h_sum_lt : (y2 * 4 + y * 2).toNat ≤ (2 ^ 22 - 1) * 4 + 2047 * 2 := by
        rw [h_sum_toNat]
        have h_le2 : y2.toNat * 4 ≤ (2 ^ 22 - 1) * 4 := Nat.mul_le_mul_right 4 (by omega)
        have h_le3 : y.toNat * 2 ≤ 2047 * 2 := Nat.mul_le_mul_right 2 (by omega)
        omega
      have h_mul_3_sum : ((3 : u32) *? (y2 * 4 + y * 2) : RustM u32) =
                        pure (3 * (y2 * 4 + y * 2)) := by
        show (rust_primitives.ops.arith.Mul.mul (3 : u32) (y2 * 4 + y * 2) : RustM u32) = _
        show (if BitVec.umulOverflow (3 : u32).toBitVec (y2 * 4 + y * 2).toBitVec then
                (.fail .integerOverflow : RustM u32)
              else pure (3 * (y2 * 4 + y * 2))) = _
        have h_no_ovf : BitVec.umulOverflow (3 : u32).toBitVec (y2 * 4 + y * 2).toBitVec = false := by
          cases h_eq : BitVec.umulOverflow (3 : u32).toBitVec (y2 * 4 + y * 2).toBitVec with
          | false => rfl
          | true =>
            exfalso
            have : UInt32.mulOverflow (3 : u32) (y2 * 4 + y * 2) = true := h_eq
            rw [UInt32.mulOverflow_iff] at this
            rw [h_3_toNat] at this
            have h_le : 3 * (y2 * 4 + y * 2).toNat ≤ 3 * ((2 ^ 22 - 1) * 4 + 2047 * 2) :=
              Nat.mul_le_mul_left 3 h_sum_lt
            have h_c : 3 * (((2 : Nat) ^ 22 - 1) * 4 + 2047 * 2) < 2 ^ 32 := by decide
            omega
        rw [h_no_ovf]; rfl
      rw [h_mul_3_sum]
      simp only [pure_bind]
      have h_3sum_toNat : ((3 : u32) * (y2 * 4 + y * 2)).toNat =
                         3 * (y2.toNat * 4 + y.toNat * 2) := by
        rw [UInt32.toNat_mul_of_lt]
        · rw [h_3_toNat, h_sum_toNat]
        rw [h_3_toNat]
        have h_le : 3 * (y2 * 4 + y * 2).toNat ≤ 3 * ((2 ^ 22 - 1) * 4 + 2047 * 2) :=
          Nat.mul_le_mul_left 3 h_sum_lt
        have h_c : 3 * (((2 : Nat) ^ 22 - 1) * 4 + 2047 * 2) < 2 ^ 32 := by decide
        omega
      have h_3sum_lt : ((3 : u32) * (y2 * 4 + y * 2)).toNat ≤
                       3 * ((2 ^ 22 - 1) * 4 + 2047 * 2) := by
        rw [h_3sum_toNat]
        have h_le2 : y2.toNat * 4 ≤ (2 ^ 22 - 1) * 4 := Nat.mul_le_mul_right 4 (by omega)
        have h_le3 : y.toNat * 2 ≤ 2047 * 2 := Nat.mul_le_mul_right 2 (by omega)
        omega
      have h_add_b_1 : ((3 : u32) * (y2 * 4 + y * 2) +? (1 : u32) : RustM u32) =
                       pure (3 * (y2 * 4 + y * 2) + 1) := by
        show (rust_primitives.ops.arith.Add.add (3 * (y2 * 4 + y * 2)) (1 : u32) : RustM u32) = _
        show (if BitVec.uaddOverflow (3 * (y2 * 4 + y * 2)).toBitVec (1 : u32).toBitVec then
                (.fail .integerOverflow : RustM u32)
              else pure (_)) = _
        have h_no_ovf : BitVec.uaddOverflow (3 * (y2 * 4 + y * 2)).toBitVec (1 : u32).toBitVec = false := by
          cases h_eq : BitVec.uaddOverflow (3 * (y2 * 4 + y * 2)).toBitVec (1 : u32).toBitVec with
          | false => rfl
          | true =>
            exfalso
            have : UInt32.addOverflow (3 * (y2 * 4 + y * 2)) (1 : u32) = true := h_eq
            rw [UInt32.addOverflow_iff] at this
            rw [h_1_toNat] at this
            have h_c : 3 * (((2 : Nat) ^ 22 - 1) * 4 + 2047 * 2) + 1 < 2 ^ 32 := by decide
            omega
        rw [h_no_ovf]; rfl
      rw [h_add_b_1]
      simp only [pure_bind]
      have h_b_toNat : ((3 : u32) * (y2 * 4 + y * 2) + (1 : u32)).toNat =
                      3 * (y2.toNat * 4 + y.toNat * 2) + 1 := by
        rw [UInt32.toNat_add_of_lt]
        · rw [h_3sum_toNat, h_1_toNat]
        rw [h_3sum_toNat, h_1_toNat]
        have h_c : 3 * (((2 : Nat) ^ 22 - 1) * 4 + 2047 * 2) + 1 < 2 ^ 32 := by decide
        omega
      have h_y2d_alg : (y2 * (4 : u32)).toNat = 4 * (y.toNat * y.toNat) := by
        rw [h_y2d_toNat, h_y2_eq]; exact Nat.mul_comm _ _
      have h_yd_alg : (y * (2 : u32)).toNat = 2 * y.toNat := by
        rw [h_yd_toNat]; exact Nat.mul_comm _ _
      have h_b_alg : ((3 : u32) * (y2 * 4 + y * 2) + (1 : u32)).toNat
                    = 12 * (y.toNat * y.toNat) + 6 * y.toNat + 1 := by
        rw [h_b_toNat, h_y2_eq,
            show y.toNat * y.toNat * 4 = 4 * (y.toNat * y.toNat) from Nat.mul_comm _ _,
            show y.toNat * 2 = 2 * y.toNat from Nat.mul_comm _ _,
            Nat.mul_add,
            show (3 : Nat) * (4 * (y.toNat * y.toNat)) = 12 * (y.toNat * y.toNat) from by
              rw [← Nat.mul_assoc],
            show (3 : Nat) * (2 * y.toNat) = 6 * y.toNat from by
              rw [← Nat.mul_assoc]]
      have h_cube_id : (2 * y.toNat + 1) * (2 * y.toNat + 1) * (2 * y.toNat + 1) =
                       8 * (y.toNat * y.toNat * y.toNat) +
                       (12 * (y.toNat * y.toNat) + 6 * y.toNat + 1) := by
        rw [nat_2y1_cube]
        omega
      have h_8_split : (8 : Nat) ^ s_iter.toNat =
                       8 * 8 ^ (s_iter.toNat - 1) := by
        have h_eq : s_iter.toNat = (s_iter.toNat - 1) + 1 := by omega
        calc (8 : Nat) ^ s_iter.toNat
            = 8 ^ ((s_iter.toNat - 1) + 1) := by rw [← h_eq]
          _ = 8 ^ (s_iter.toNat - 1) * 8 := Nat.pow_succ 8 _
          _ = 8 * 8 ^ (s_iter.toNat - 1) := Nat.mul_comm _ _
      have h_2s_eq : (2 : Nat) ^ ((s_iter - (1 : u32)) * (3 : u32)).toNat =
                     8 ^ (s_iter.toNat - 1) := by
        rw [h_s_toNat]
        rw [show (8 : Nat) = 2 ^ 3 from rfl, ← Nat.pow_mul]
        congr 1
        exact Nat.mul_comm _ _
      have h_shr : (x >>>? ((s_iter - (1 : u32)) * (3 : u32)) : RustM u32) =
                   pure (x >>> ((s_iter - 1) * 3)) := by
        show (rust_primitives.ops.bit.Shr.shr x ((s_iter - 1) * 3) : RustM u32) =
             pure (x >>> ((s_iter - 1) * 3))
        show (if (0 : u32) ≤ (s_iter - 1) * 3 && (s_iter - 1) * 3 < (32 : u32) then
                pure (x >>> ((s_iter - 1) * 3))
              else (.fail .integerOverflow : RustM u32)) = _
        have h_0_le : (0 : u32) ≤ (s_iter - 1) * 3 :=
          UInt32.le_iff_toNat_le.mpr (by show 0 ≤ _; omega)
        have h_lt_32 : (s_iter - 1) * 3 < (32 : u32) :=
          UInt32.lt_iff_toNat_lt.mpr (by
            show ((s_iter - 1) * 3).toNat < (32 : u32).toNat
            show _ < 32
            omega)
        rw [show ((0 : u32) ≤ (s_iter - 1) * 3 && (s_iter - 1) * 3 < (32 : u32)) = true from by
              rw [show (decide ((0 : u32) ≤ (s_iter - 1) * 3) = true) from decide_eq_true h_0_le]
              rw [show (decide ((s_iter - 1) * 3 < (32 : u32)) = true) from decide_eq_true h_lt_32]
              rfl]
        rfl
      rw [h_shr]
      simp only [pure_bind]
      have h_xshr_toNat : (x >>> ((s_iter - 1) * 3)).toNat =
                          x.toNat / 2 ^ ((s_iter - (1 : u32)) * (3 : u32)).toNat := by
        rw [UInt32.toNat_shiftRight]
        show x.toNat >>> (((s_iter - 1) * 3).toNat % 32) = _
        rw [Nat.mod_eq_of_lt (by omega : ((s_iter - 1) * 3).toNat < 32),
            Nat.shiftRight_eq_div_pow]
      have h_ge_eqq : ((x >>> ((s_iter - 1) * 3)) >=? ((3 : u32) * (y2 * 4 + y * 2) + (1 : u32))
                       : RustM Bool) =
                      pure (decide (x >>> ((s_iter - 1) * 3) ≥
                                    (3 : u32) * (y2 * 4 + y * 2) + (1 : u32))) := rfl
      rw [h_ge_eqq]
      simp only [pure_bind]
      have h_ge_iff : (x >>> ((s_iter - 1) * 3) ≥
                       (3 : u32) * (y2 * 4 + y * 2) + (1 : u32)) ↔
                      ((3 : u32) * (y2 * 4 + y * 2) + (1 : u32)).toNat *
                        2 ^ ((s_iter - (1 : u32)) * (3 : u32)).toNat ≤ x.toNat := by
        show ((3 : u32) * (y2 * 4 + y * 2) + (1 : u32)) ≤ x >>> ((s_iter - 1) * 3) ↔ _
        rw [UInt32.le_iff_toNat_le, h_xshr_toNat]
        exact nat_div_ge_iff_mul_le _ _ _ (Nat.pow_pos (by decide : 0 < 2))
      have h_y3_split : y.toNat * y.toNat * y.toNat * 8 ^ s_iter.toNat =
                        8 * (y.toNat * y.toNat * y.toNat) * 8 ^ (s_iter.toNat - 1) := by
        rw [h_8_split]
        rw [← Nat.mul_assoc (y.toNat * y.toNat * y.toNat) 8 (8 ^ (s_iter.toNat - 1))]
        rw [Nat.mul_comm (y.toNat * y.toNat * y.toNat) 8]
      have h_x_inv : x.toNat + y.toNat * y.toNat * y.toNat * 8 ^ s_iter.toNat = a_orig := by
        rw [h_x_eq]; omega
      by_cases h_ge : x >>> ((s_iter - 1) * 3) ≥ (3 : u32) * (y2 * 4 + y * 2) + (1 : u32)
      · simp only [decide_eq_true h_ge, if_true]
        have h_x_ge : ((3 : u32) * (y2 * 4 + y * 2) + (1 : u32)).toNat *
                      2 ^ ((s_iter - (1 : u32)) * (3 : u32)).toNat ≤ x.toNat :=
          h_ge_iff.mp h_ge
        have h_b2s_lt_32 : ((3 : u32) * (y2 * 4 + y * 2) + (1 : u32)).toNat *
                           2 ^ ((s_iter - (1 : u32)) * (3 : u32)).toNat < 2 ^ 32 := by
          have h_x_lt : x.toNat < 2 ^ 32 := x.toNat_lt
          omega
        have h_shl_b : (((3 : u32) * (y2 * 4 + y * 2) + (1 : u32)) <<<?
                         ((s_iter - (1 : u32)) * (3 : u32)) : RustM u32) =
                       pure ((3 * (y2 * 4 + y * 2) + 1) <<< ((s_iter - 1) * 3)) := by
          show (rust_primitives.ops.bit.Shl.shl
                  (3 * (y2 * 4 + y * 2) + 1) ((s_iter - 1) * 3) : RustM u32) = _
          show (if (0 : u32) ≤ (s_iter - 1) * 3 && (s_iter - 1) * 3 < (32 : u32) then
                  pure ((3 * (y2 * 4 + y * 2) + 1) <<< ((s_iter - 1) * 3))
                else (.fail .integerOverflow : RustM u32)) = _
          have h_0_le : (0 : u32) ≤ (s_iter - 1) * 3 :=
            UInt32.le_iff_toNat_le.mpr (by show 0 ≤ _; omega)
          have h_lt_32 : (s_iter - 1) * 3 < (32 : u32) :=
            UInt32.lt_iff_toNat_lt.mpr (by
              show ((s_iter - 1) * 3).toNat < (32 : u32).toNat
              show _ < 32
              omega)
          rw [show ((0 : u32) ≤ (s_iter - 1) * 3 && (s_iter - 1) * 3 < (32 : u32)) = true from by
                rw [show (decide ((0 : u32) ≤ (s_iter - 1) * 3) = true) from decide_eq_true h_0_le]
                rw [show (decide ((s_iter - 1) * 3 < (32 : u32)) = true) from decide_eq_true h_lt_32]
                rfl]
          rfl
        rw [h_shl_b]
        simp only [pure_bind]
        have h_bshl_toNat : ((3 * (y2 * 4 + y * 2) + 1) <<< ((s_iter - 1) * 3)).toNat =
                            ((3 : u32) * (y2 * 4 + y * 2) + (1 : u32)).toNat *
                              2 ^ ((s_iter - (1 : u32)) * (3 : u32)).toNat := by
          rw [UInt32.toNat_shiftLeft]
          show (((3 : u32) * (y2 * 4 + y * 2) + (1 : u32)).toNat <<<
                  (((s_iter - 1) * 3).toNat % 32)) % 2 ^ 32 = _
          rw [Nat.mod_eq_of_lt (by omega : ((s_iter - 1) * 3).toNat < 32),
              Nat.shiftLeft_eq]
          exact Nat.mod_eq_of_lt h_b2s_lt_32
        have h_sub_x : (x -? ((3 * (y2 * 4 + y * 2) + 1) <<< ((s_iter - 1) * 3))
                        : RustM u32) =
                       pure (x - ((3 * (y2 * 4 + y * 2) + 1) <<< ((s_iter - 1) * 3))) := by
          show (rust_primitives.ops.arith.Sub.sub x
                  ((3 * (y2 * 4 + y * 2) + 1) <<< ((s_iter - 1) * 3)) : RustM u32) = _
          show (if BitVec.usubOverflow x.toBitVec
                  ((3 * (y2 * 4 + y * 2) + 1) <<< ((s_iter - 1) * 3)).toBitVec then
                  (.fail .integerOverflow : RustM u32)
                else pure (_)) = _
          have h_no_ovf : BitVec.usubOverflow x.toBitVec
              ((3 * (y2 * 4 + y * 2) + 1) <<< ((s_iter - 1) * 3)).toBitVec = false := by
            cases h_eq : BitVec.usubOverflow x.toBitVec
              ((3 * (y2 * 4 + y * 2) + 1) <<< ((s_iter - 1) * 3)).toBitVec with
            | false => rfl
            | true =>
              exfalso
              have : UInt32.subOverflow x
                ((3 * (y2 * 4 + y * 2) + 1) <<< ((s_iter - 1) * 3)) = true := h_eq
              rw [UInt32.subOverflow_iff] at this
              rw [h_bshl_toNat] at this
              omega
          rw [h_no_ovf]; rfl
        rw [h_sub_x]
        simp only [pure_bind]
        have h_xnew_toNat : (x - (3 * (y2 * 4 + y * 2) + 1) <<< ((s_iter - 1) * 3)).toNat =
                            x.toNat -
                            ((3 : u32) * (y2 * 4 + y * 2) + (1 : u32)).toNat *
                              2 ^ ((s_iter - (1 : u32)) * (3 : u32)).toNat := by
          rw [UInt32.toNat_sub_of_le' (by rw [h_bshl_toNat]; exact h_x_ge), h_bshl_toNat]
        have h_mul_2_yd : ((2 : u32) *? (y * 2) : RustM u32) = pure (2 * (y * 2)) := by
          show (rust_primitives.ops.arith.Mul.mul (2 : u32) (y * 2) : RustM u32) = _
          show (if BitVec.umulOverflow (2 : u32).toBitVec (y * 2).toBitVec then
                  (.fail .integerOverflow : RustM u32)
                else pure (2 * (y * 2))) = _
          have h_no_ovf : BitVec.umulOverflow (2 : u32).toBitVec (y * 2).toBitVec = false := by
            cases h_eq : BitVec.umulOverflow (2 : u32).toBitVec (y * 2).toBitVec with
            | false => rfl
            | true =>
              exfalso
              have : UInt32.mulOverflow (2 : u32) (y * 2) = true := h_eq
              rw [UInt32.mulOverflow_iff] at this
              rw [h_2_toNat, h_yd_toNat] at this
              omega
          rw [h_no_ovf]; rfl
        rw [h_mul_2_yd]
        simp only [pure_bind]
        have h_2yd_toNat : ((2 : u32) * (y * 2)).toNat = 2 * (y.toNat * 2) := by
          rw [UInt32.toNat_mul_of_lt]
          · rw [h_2_toNat, h_yd_toNat]
          rw [h_2_toNat, h_yd_toNat]; omega
        have h_add_y2new : (y2 * 4 +? (2 : u32) * (y * 2) : RustM u32) =
                           pure (y2 * 4 + 2 * (y * 2)) := by
          show (rust_primitives.ops.arith.Add.add (y2 * 4) ((2 : u32) * (y * 2)) : RustM u32) = _
          show (if BitVec.uaddOverflow (y2 * 4).toBitVec ((2 : u32) * (y * 2)).toBitVec then
                  (.fail .integerOverflow : RustM u32)
                else pure (_)) = _
          have h_no_ovf : BitVec.uaddOverflow (y2 * 4).toBitVec ((2 : u32) * (y * 2)).toBitVec = false := by
            cases h_eq : BitVec.uaddOverflow (y2 * 4).toBitVec ((2 : u32) * (y * 2)).toBitVec with
            | false => rfl
            | true =>
              exfalso
              have : UInt32.addOverflow (y2 * 4) ((2 : u32) * (y * 2)) = true := h_eq
              rw [UInt32.addOverflow_iff] at this
              rw [h_y2d_toNat, h_2yd_toNat] at this
              have h_le2 : y2.toNat * 4 ≤ (2 ^ 22 - 1) * 4 := Nat.mul_le_mul_right 4 (by omega)
              have h_c : ((2 : Nat) ^ 22 - 1) * 4 + 2 * (2047 * 2) < 2 ^ 32 := by decide
              omega
          rw [h_no_ovf]; rfl
        rw [h_add_y2new]
        simp only [pure_bind]
        have h_y2new_sum_toNat : (y2 * 4 + (2 : u32) * (y * 2)).toNat =
                                  y2.toNat * 4 + 2 * (y.toNat * 2) := by
          rw [UInt32.toNat_add_of_lt]
          · rw [h_y2d_toNat, h_2yd_toNat]
          rw [h_y2d_toNat, h_2yd_toNat]
          have h_le2 : y2.toNat * 4 ≤ (2 ^ 22 - 1) * 4 := Nat.mul_le_mul_right 4 (by omega)
          have h_c : ((2 : Nat) ^ 22 - 1) * 4 + 2 * (2047 * 2) < 2 ^ 32 := by decide
          omega
        have h_add_y2new_1 : ((y2 * 4 + (2 : u32) * (y * 2)) +? (1 : u32) : RustM u32) =
                              pure (y2 * 4 + 2 * (y * 2) + 1) := by
          show (rust_primitives.ops.arith.Add.add
                  (y2 * 4 + (2 : u32) * (y * 2)) (1 : u32) : RustM u32) = _
          show (if BitVec.uaddOverflow (y2 * 4 + (2 : u32) * (y * 2)).toBitVec
                  (1 : u32).toBitVec then
                  (.fail .integerOverflow : RustM u32)
                else pure (_)) = _
          have h_no_ovf : BitVec.uaddOverflow (y2 * 4 + (2 : u32) * (y * 2)).toBitVec
                            (1 : u32).toBitVec = false := by
            cases h_eq : BitVec.uaddOverflow (y2 * 4 + (2 : u32) * (y * 2)).toBitVec
                          (1 : u32).toBitVec with
            | false => rfl
            | true =>
              exfalso
              have : UInt32.addOverflow (y2 * 4 + (2 : u32) * (y * 2)) (1 : u32) = true := h_eq
              rw [UInt32.addOverflow_iff] at this
              rw [h_1_toNat, h_y2new_sum_toNat] at this
              have h_le2 : y2.toNat * 4 ≤ (2 ^ 22 - 1) * 4 := Nat.mul_le_mul_right 4 (by omega)
              have h_c : ((2 : Nat) ^ 22 - 1) * 4 + 2 * (2047 * 2) + 1 < 2 ^ 32 := by decide
              omega
          rw [h_no_ovf]; rfl
        rw [h_add_y2new_1]
        simp only [pure_bind]
        have h_y2new_toNat : ((y2 * 4 + (2 : u32) * (y * 2)) + (1 : u32)).toNat =
                              y2.toNat * 4 + 2 * (y.toNat * 2) + 1 := by
          rw [UInt32.toNat_add_of_lt]
          · rw [h_y2new_sum_toNat, h_1_toNat]
          rw [h_y2new_sum_toNat, h_1_toNat]
          have h_le2 : y2.toNat * 4 ≤ (2 ^ 22 - 1) * 4 := Nat.mul_le_mul_right 4 (by omega)
          have h_c : ((2 : Nat) ^ 22 - 1) * 4 + 2 * (2047 * 2) + 1 < 2 ^ 32 := by decide
          omega
        have h_add_yd_1 : (y * 2 +? (1 : u32) : RustM u32) = pure (y * 2 + 1) := by
          show (rust_primitives.ops.arith.Add.add (y * 2) (1 : u32) : RustM u32) = _
          show (if BitVec.uaddOverflow (y * 2).toBitVec (1 : u32).toBitVec then
                  (.fail .integerOverflow : RustM u32)
                else pure (y * 2 + 1)) = _
          have h_no_ovf : BitVec.uaddOverflow (y * 2).toBitVec (1 : u32).toBitVec = false := by
            cases h_eq : BitVec.uaddOverflow (y * 2).toBitVec (1 : u32).toBitVec with
            | false => rfl
            | true =>
              exfalso
              have : UInt32.addOverflow (y * 2) (1 : u32) = true := h_eq
              rw [UInt32.addOverflow_iff] at this
              rw [h_1_toNat, h_yd_toNat] at this
              omega
          rw [h_no_ovf]; rfl
        rw [h_add_yd_1]
        simp only [pure_bind]
        have h_ynew_toNat : (y * 2 + (1 : u32)).toNat = y.toNat * 2 + 1 := by
          rw [UInt32.toNat_add_of_lt]
          · rw [h_yd_toNat, h_1_toNat]
          rw [h_yd_toNat, h_1_toNat]; omega
        have h_meas : (s_iter - (1 : u32)).toNat < s_iter.toNat := by
          rw [h_sn_toNat]; omega
        have h_s_le_11' : (s_iter - (1 : u32)).toNat ≤ 11 := by rw [h_sn_toNat]; omega
        have h_ynew_alg : (y * 2 + (1 : u32)).toNat = 2 * y.toNat + 1 := by
          rw [h_ynew_toNat, Nat.mul_comm y.toNat 2]
        have h_y2new_eq_sq : ((y2 * 4 + (2 : u32) * (y * 2)) + (1 : u32)).toNat =
                              (y * 2 + (1 : u32)).toNat * (y * 2 + (1 : u32)).toNat := by
          rw [h_y2new_toNat, h_ynew_alg, h_y2_eq, nat_2y1_sq,
              show y.toNat * y.toNat * 4 = 4 * (y.toNat * y.toNat) from Nat.mul_comm _ _,
              show 2 * (y.toNat * 2) = 4 * y.toNat from by
                rw [Nat.mul_comm y.toNat 2, ← Nat.mul_assoc]]
        have h_ynew_cube_le : (y * 2 + (1 : u32)).toNat * (y * 2 + (1 : u32)).toNat *
            (y * 2 + (1 : u32)).toNat * 8 ^ (s_iter - (1 : u32)).toNat ≤ a_orig := by
          rw [h_ynew_alg, h_cube_id, h_sn_toNat]
          rw [Nat.add_mul]
          rw [← h_y3_split]
          have h_2s_rw : (8 : Nat) ^ (s_iter.toNat - 1) =
              2 ^ ((s_iter - (1 : u32)) * (3 : u32)).toNat := by
            rw [h_2s_eq]
          rw [h_2s_rw]
          rw [← h_b_alg]
          omega
        have h_a_lt_succ_new : a_orig <
            ((y * 2 + (1 : u32)).toNat + 1) * ((y * 2 + (1 : u32)).toNat + 1) *
            ((y * 2 + (1 : u32)).toNat + 1) * 8 ^ (s_iter - (1 : u32)).toNat := by
          rw [h_ynew_alg, h_sn_toNat]
          have h_rw : (2 * y.toNat + 1 + 1) * (2 * y.toNat + 1 + 1) *
                      (2 * y.toNat + 1 + 1) * 8 ^ (s_iter.toNat - 1) =
                     (y.toNat + 1) * (y.toNat + 1) * (y.toNat + 1) *
                       (8 * 8 ^ (s_iter.toNat - 1)) := by
            have h_2y2 : 2 * y.toNat + 1 + 1 = 2 * (y.toNat + 1) := by omega
            rw [h_2y2, nat_two_y_cube (y.toNat + 1),
                Nat.mul_comm 8 ((y.toNat + 1) * (y.toNat + 1) * (y.toNat + 1)),
                Nat.mul_assoc ((y.toNat + 1) * (y.toNat + 1) * (y.toNat + 1)) 8
                              (8 ^ (s_iter.toNat - 1))]
          rw [h_rw, ← h_8_split]
          exact h_a_lt_succ_cube
        have h_xnew_inv : (x - (3 * (y2 * 4 + y * 2) + 1) <<< ((s_iter - 1) * 3)).toNat =
                          a_orig - (y * 2 + (1 : u32)).toNat *
                                     (y * 2 + (1 : u32)).toNat *
                                     (y * 2 + (1 : u32)).toNat *
                                     8 ^ (s_iter - (1 : u32)).toNat := by
          rw [h_xnew_toNat, h_ynew_alg, h_cube_id, h_sn_toNat, Nat.add_mul,
              ← h_y3_split]
          have h_2s_rw : (8 : Nat) ^ (s_iter.toNat - 1) =
              2 ^ ((s_iter - (1 : u32)) * (3 : u32)).toNat := by
            rw [h_2s_eq]
          rw [h_2s_rw, ← h_b_alg]
          omega
        exact ih (s_iter - (1 : u32)).toNat h_meas
                 (s_iter - (1 : u32))
                 (x - (3 * (y2 * 4 + y * 2) + 1) <<< ((s_iter - 1) * 3))
                 ((y2 * 4 + (2 : u32) * (y * 2)) + (1 : u32))
                 (y * 2 + (1 : u32))
                 h_s_le_11' h_y2new_eq_sq h_ynew_cube_le h_a_lt_succ_new h_xnew_inv rfl
      · simp only [decide_eq_false h_ge, Bool.false_eq_true, if_false]
        have h_x_lt : x.toNat < ((3 : u32) * (y2 * 4 + y * 2) + (1 : u32)).toNat *
                                2 ^ ((s_iter - (1 : u32)) * (3 : u32)).toNat := by
          rcases Nat.lt_or_ge x.toNat (((3 : u32) * (y2 * 4 + y * 2) + (1 : u32)).toNat *
                                       2 ^ ((s_iter - (1 : u32)) * (3 : u32)).toNat) with h | h
          · exact h
          · exfalso; exact h_ge (h_ge_iff.mpr h)
        have h_meas : (s_iter - (1 : u32)).toNat < s_iter.toNat := by
          rw [h_sn_toNat]; omega
        have h_s_le_11' : (s_iter - (1 : u32)).toNat ≤ 11 := by rw [h_sn_toNat]; omega
        have h_y2d_eq_sq : (y2 * (4 : u32)).toNat = (y * (2 : u32)).toNat * (y * (2 : u32)).toNat := by
          rw [h_y2d_alg, h_yd_alg]
          exact (nat_two_y_sq y.toNat).symm
        have h_yd_cube_le : (y * (2 : u32)).toNat * (y * (2 : u32)).toNat *
            (y * (2 : u32)).toNat * 8 ^ (s_iter - (1 : u32)).toNat ≤ a_orig := by
          rw [h_yd_alg, h_sn_toNat]
          have h_rw : 2 * y.toNat * (2 * y.toNat) * (2 * y.toNat) * 8 ^ (s_iter.toNat - 1) =
                      y.toNat * y.toNat * y.toNat * (8 * 8 ^ (s_iter.toNat - 1)) := by
            rw [nat_two_y_cube,
                Nat.mul_comm 8 (y.toNat * y.toNat * y.toNat),
                Nat.mul_assoc (y.toNat * y.toNat * y.toNat) 8 (8 ^ (s_iter.toNat - 1))]
          rw [h_rw, ← h_8_split]
          exact h_y_cube_le
        have h_a_lt_succ_d : a_orig <
            ((y * (2 : u32)).toNat + 1) * ((y * (2 : u32)).toNat + 1) *
            ((y * (2 : u32)).toNat + 1) * 8 ^ (s_iter - (1 : u32)).toNat := by
          rw [h_yd_alg, h_sn_toNat]
          rw [show (2 * y.toNat + 1) * (2 * y.toNat + 1) * (2 * y.toNat + 1) *
                   8 ^ (s_iter.toNat - 1) =
                   (2 * y.toNat + 1) * (2 * y.toNat + 1) * (2 * y.toNat + 1) *
                   8 ^ (s_iter.toNat - 1) from rfl]
          rw [h_cube_id, Nat.add_mul, ← h_y3_split]
          have h_2s_rw : (8 : Nat) ^ (s_iter.toNat - 1) =
              2 ^ ((s_iter - (1 : u32)) * (3 : u32)).toNat := by
            rw [h_2s_eq]
          rw [h_2s_rw, ← h_b_alg]
          omega
        have h_x_inv_d : x.toNat = a_orig - (y * (2 : u32)).toNat *
                                              (y * (2 : u32)).toNat *
                                              (y * (2 : u32)).toNat *
                                              8 ^ (s_iter - (1 : u32)).toNat := by
          rw [h_yd_alg, h_sn_toNat]
          have h_rw : 2 * y.toNat * (2 * y.toNat) * (2 * y.toNat) * 8 ^ (s_iter.toNat - 1) =
                      y.toNat * y.toNat * y.toNat * (8 * 8 ^ (s_iter.toNat - 1)) := by
            rw [nat_two_y_cube,
                Nat.mul_comm 8 (y.toNat * y.toNat * y.toNat),
                Nat.mul_assoc (y.toNat * y.toNat * y.toNat) 8 (8 ^ (s_iter.toNat - 1))]
          rw [h_rw, ← h_8_split]
          exact h_x_eq
        exact ih (s_iter - (1 : u32)).toNat h_meas
                 (s_iter - (1 : u32))
                 x
                 (y2 * (4 : u32))
                 (y * (2 : u32))
                 h_s_le_11' h_y2d_eq_sq h_yd_cube_le h_a_lt_succ_d h_x_inv_d rfl

/-- Top-level `cbrt_u32` correctness. Initial state: s_iter=11, x=a, y2=0, y=0. -/
private theorem cbrt_u32_correct (a : u32) :
    ∃ y : u32, nth_root_u64.cbrt_u32 a = RustM.ok y ∧
      y.toNat * y.toNat * y.toNat ≤ a.toNat ∧
      a.toNat < (y.toNat + 1) * (y.toNat + 1) * (y.toNat + 1) := by
  unfold nth_root_u64.cbrt_u32
  have h_11_toNat : (11 : u32).toNat = 11 := rfl
  have h_0_toNat : (0 : u32).toNat = 0 := rfl
  have h_a_lt : a.toNat < 2 ^ 32 := a.toNat_lt
  refine cbrt_u32_loop_correct (11 : u32) a (0 : u32) (0 : u32) a.toNat h_a_lt
    ?_ ?_ ?_ ?_ ?_
  · rw [h_11_toNat]; omega
  · rw [h_0_toNat]
  · rw [h_0_toNat, h_11_toNat]
    omega
  · rw [h_0_toNat, h_11_toNat]
    have h_8_11 : (8 : Nat) ^ 11 = 2 ^ 33 := by decide
    have h_2_33 : (2 : Nat) ^ 33 > 2 ^ 32 := by decide
    show a.toNat < (0 + 1) * (0 + 1) * (0 + 1) * 8 ^ 11
    omega
  · rw [h_0_toNat, h_11_toNat]
    omega

/-! ## `cbrt_guess_u64` correctness -/

private theorem cbrt_guess_u64_correct (a : u64) (h_a_ge : a.toNat ≥ 2 ^ 32) :
    ∃ g : u64, nth_root_u64.cbrt_guess_u64 a = RustM.ok g ∧
      0 < g.toNat ∧
      g.toNat ≤ 2 ^ 22 ∧
      a.toNat ≤ g.toNat * g.toNat * g.toNat := by
  unfold nth_root_u64.cbrt_guess_u64
  have h_a_pos : 0 < a.toNat := by omega
  have h_a_lt : a.toNat < 2 ^ 64 := a.toNat_lt
  have h_log2_le : Nat.log2 a.toNat ≤ 63 := nat_log2_le_63 a.toNat h_a_pos h_a_lt
  have h_log2_ge : Nat.log2 a.toNat ≥ 32 := by
    rcases Nat.lt_or_ge (Nat.log2 a.toNat) 32 with h | h
    · exfalso
      have h_x_lt : a.toNat < 2 ^ (Nat.log2 a.toNat + 1) := nat_lt_pow_succ_log2 a.toNat h_a_pos
      have h_pow_le : 2 ^ (Nat.log2 a.toNat + 1) ≤ 2 ^ 32 :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · exact h
  -- Unfold log2_u64.
  have h_log2_u64_eq : nth_root_u64.log2_u64 a = RustM.ok (UInt32.ofNat (Nat.log2 a.toNat)) := by
    show nth_root_u64.log2_rec a (0 : UInt32) = _
    have h := log2_rec_correct a (0 : UInt32) (by
      show (0 : UInt32).toNat + Nat.log2 a.toNat < 2 ^ 32
      have h0 : (0 : UInt32).toNat = 0 := rfl
      rw [h0]; omega)
    rw [h]
    have h0 : (0 : UInt32).toNat = 0 := rfl
    rw [h0, Nat.zero_add]
  rw [h_log2_u64_eq]
  simp only [RustM_ok_bind]
  have h_log2_toNat : (UInt32.ofNat (Nat.log2 a.toNat)).toNat = Nat.log2 a.toNat :=
    UInt32.toNat_ofNat_of_lt' (by omega : Nat.log2 a.toNat < 2 ^ 32)
  have h_add3 : ((UInt32.ofNat (Nat.log2 a.toNat)) +? (3 : u32) : RustM u32) =
                pure (UInt32.ofNat (Nat.log2 a.toNat) + 3) := by
    show (rust_primitives.ops.arith.Add.add (UInt32.ofNat (Nat.log2 a.toNat)) (3 : u32) : RustM u32) =
         pure (UInt32.ofNat (Nat.log2 a.toNat) + 3)
    show (if BitVec.uaddOverflow (UInt32.ofNat (Nat.log2 a.toNat)).toBitVec (3 : u32).toBitVec then
            (.fail .integerOverflow : RustM u32)
          else pure (UInt32.ofNat (Nat.log2 a.toNat) + 3)) =
         pure (UInt32.ofNat (Nat.log2 a.toNat) + 3)
    have h_no_ovf : BitVec.uaddOverflow (UInt32.ofNat (Nat.log2 a.toNat)).toBitVec (3 : u32).toBitVec = false := by
      cases h_eq : BitVec.uaddOverflow (UInt32.ofNat (Nat.log2 a.toNat)).toBitVec (3 : u32).toBitVec with
      | false => rfl
      | true =>
        exfalso
        have : UInt32.addOverflow (UInt32.ofNat (Nat.log2 a.toNat)) (3 : u32) = true := h_eq
        rw [UInt32.addOverflow_iff] at this
        rw [h_log2_toNat, show (3 : UInt32).toNat = 3 from rfl] at this
        omega
    rw [h_no_ovf]; rfl
  rw [h_add3]
  simp only [pure_bind]
  have h_log2p3_toNat : (UInt32.ofNat (Nat.log2 a.toNat) + 3).toNat = Nat.log2 a.toNat + 3 := by
    have h_no_ovf : (UInt32.ofNat (Nat.log2 a.toNat)).toNat + (3 : UInt32).toNat < 2 ^ 32 := by
      rw [h_log2_toNat, show (3 : UInt32).toNat = 3 from rfl]; omega
    rw [UInt32.toNat_add_of_lt h_no_ovf, h_log2_toNat, show (3 : UInt32).toNat = 3 from rfl]
  have h_div3 : ((UInt32.ofNat (Nat.log2 a.toNat) + 3) /? (3 : u32) : RustM u32) =
                pure ((UInt32.ofNat (Nat.log2 a.toNat) + 3) / 3) := by
    show (rust_primitives.ops.arith.Div.div (UInt32.ofNat (Nat.log2 a.toNat) + 3) (3 : u32) : RustM u32) =
         pure ((UInt32.ofNat (Nat.log2 a.toNat) + 3) / 3)
    show (if (3 : u32) = 0 then (.fail .divisionByZero : RustM u32) else pure ((UInt32.ofNat (Nat.log2 a.toNat) + 3) / 3)) =
         pure ((UInt32.ofNat (Nat.log2 a.toNat) + 3) / 3)
    rw [if_neg (by decide : (3 : u32) ≠ 0)]
  rw [h_div3]
  simp only [pure_bind]
  have h_k_toNat : ((UInt32.ofNat (Nat.log2 a.toNat) + 3) / 3).toNat
                   = (Nat.log2 a.toNat + 3) / 3 := by
    rw [UInt32.toNat_div, h_log2p3_toNat, show (3 : UInt32).toNat = 3 from rfl]
  have h_k_ge_11 : 11 ≤ (Nat.log2 a.toNat + 3) / 3 := by
    have h_div_ge : (35 : Nat) / 3 ≤ (Nat.log2 a.toNat + 3) / 3 :=
      Nat.div_le_div_right (by omega)
    have h35 : (35 : Nat) / 3 = 11 := by decide
    omega
  have h_k_le_22 : (Nat.log2 a.toNat + 3) / 3 ≤ 22 := by
    have h_le : Nat.log2 a.toNat + 3 ≤ 66 := by omega
    have h_div_le : (Nat.log2 a.toNat + 3) / 3 ≤ 66 / 3 :=
      Nat.div_le_div_right h_le
    have h66 : (66 : Nat) / 3 = 22 := by decide
    omega
  have h_1_toNat : (1 : u64).toNat = 1 := rfl
  have h_0_toNat : (0 : u32).toNat = 0 := rfl
  have h_no_ovf : (1 : u64).toNat * 2 ^ (((UInt32.ofNat (Nat.log2 a.toNat) + 3) / 3).toNat - (0 : u32).toNat) < 2 ^ 64 := by
    rw [h_1_toNat, h_0_toNat, h_k_toNat, Nat.sub_zero, Nat.one_mul]
    have h_pow_le : (2 : Nat) ^ ((Nat.log2 a.toNat + 3) / 3) ≤ 2 ^ 22 :=
      Nat.pow_le_pow_right (by decide) h_k_le_22
    have h_2_22 : (2 : Nat) ^ 22 < 2 ^ 64 := by decide
    omega
  have h_k_le_63 : ((UInt32.ofNat (Nat.log2 a.toNat) + 3) / 3).toNat ≤ 63 := by
    rw [h_k_toNat]; omega
  have h_0_le_k : (0 : u32).toNat ≤ ((UInt32.ofNat (Nat.log2 a.toNat) + 3) / 3).toNat := by
    rw [h_0_toNat]; omega
  obtain ⟨g, hg_eq, hg_toNat⟩ :=
    pow2_loop_correct ((UInt32.ofNat (Nat.log2 a.toNat) + 3) / 3) (0 : u32) (1 : u64)
      h_0_le_k h_k_le_63 h_no_ovf
  have h_g_toNat_eq : g.toNat = 2 ^ ((Nat.log2 a.toNat + 3) / 3) := by
    rw [hg_toNat, h_1_toNat, h_0_toNat, Nat.sub_zero, Nat.one_mul, h_k_toNat]
  refine ⟨g, hg_eq, ?_, ?_, ?_⟩
  · rw [h_g_toNat_eq]
    exact Nat.pow_pos (by decide : 0 < 2)
  · rw [h_g_toNat_eq]
    exact Nat.pow_le_pow_right (by decide) h_k_le_22
  · rw [h_g_toNat_eq]
    have h_3k_ge : 3 * ((Nat.log2 a.toNat + 3) / 3) ≥ Nat.log2 a.toNat + 1 := by
      have h_div_mod := Nat.div_add_mod (Nat.log2 a.toNat + 3) 3
      have h_mod_lt : (Nat.log2 a.toNat + 3) % 3 < 3 := Nat.mod_lt _ (by decide)
      omega
    have h_pow_log_a : a.toNat < 2 ^ (Nat.log2 a.toNat + 1) := nat_lt_pow_succ_log2 a.toNat h_a_pos
    have h_pow_chain : 2 ^ (Nat.log2 a.toNat + 1) ≤ 2 ^ (3 * ((Nat.log2 a.toNat + 3) / 3)) :=
      Nat.pow_le_pow_right (by decide) h_3k_ge
    have h_pow_cube : 2 ^ (3 * ((Nat.log2 a.toNat + 3) / 3)) =
      2 ^ ((Nat.log2 a.toNat + 3) / 3) * 2 ^ ((Nat.log2 a.toNat + 3) / 3) *
      2 ^ ((Nat.log2 a.toNat + 3) / 3) := by
      rw [show 3 * ((Nat.log2 a.toNat + 3) / 3) =
              (Nat.log2 a.toNat + 3) / 3 + (Nat.log2 a.toNat + 3) / 3 + (Nat.log2 a.toNat + 3) / 3
              from by omega,
          Nat.pow_add, Nat.pow_add]
    rw [h_pow_cube] at h_pow_chain
    omega

/-! ## `cbrt_loop_up` and `cbrt_loop_down` specs -/

/-- `cbrt_loop_up` when called with an overestimate (`x³ ≥ a`) exits
    immediately. -/
private theorem cbrt_loop_up_spec_overest (a x xn : u64)
    (h_x_pos : 0 < x.toNat)
    (h_x_cube_ge : a.toNat ≤ x.toNat * x.toNat * x.toNat)
    (h_xn_eq : xn.toNat = (a.toNat / (x.toNat * x.toNat) + 2 * x.toNat) / 3) :
    nth_root_u64.cbrt_loop_up a x xn
      = RustM.ok (rust_primitives.hax.Tuple2.mk x xn)
    ∧ xn.toNat ≤ x.toNat := by
  have h_xn_le_x : xn.toNat ≤ x.toNat := by
    rw [h_xn_eq]
    have hxx_pos : 0 < x.toNat * x.toNat := Nat.mul_pos h_x_pos h_x_pos
    have h_a_le : a.toNat ≤ x.toNat * (x.toNat * x.toNat) := by
      rw [← Nat.mul_assoc]; exact h_x_cube_ge
    have h_div_le : a.toNat / (x.toNat * x.toNat) ≤ (x.toNat * (x.toNat * x.toNat)) / (x.toNat * x.toNat) :=
      Nat.div_le_div_right h_a_le
    have h_self : x.toNat * (x.toNat * x.toNat) / (x.toNat * x.toNat) = x.toNat :=
      Nat.mul_div_cancel x.toNat hxx_pos
    have h_q_le : a.toNat / (x.toNat * x.toNat) ≤ x.toNat := by omega
    have h_sum_le : a.toNat / (x.toNat * x.toNat) + 2 * x.toNat ≤ 3 * x.toNat := by omega
    have h_div_le2 : (a.toNat / (x.toNat * x.toNat) + 2 * x.toNat) / 3 ≤ (3 * x.toNat) / 3 :=
      Nat.div_le_div_right h_sum_le
    have h_simp : (3 * x.toNat) / 3 = x.toNat := by
      rw [Nat.mul_comm]; exact Nat.mul_div_cancel x.toNat (by decide)
    omega
  refine ⟨?_, h_xn_le_x⟩
  unfold nth_root_u64.cbrt_loop_up
  have h_lt_eqq : (x <? xn : RustM Bool) = pure (decide (x < xn)) := rfl
  rw [h_lt_eqq]
  simp only [pure_bind]
  have h_not_lt : ¬ x < xn := by
    intro h
    have h_lt_N : x.toNat < xn.toNat := UInt64.lt_iff_toNat_lt.mp h
    omega
  rw [decide_eq_false h_not_lt]
  simp only [Bool.false_eq_true, if_false]
  rfl

/-- `cbrt_loop_down` spec: descends from `(x, xn)` with `a < (x+1)³` to
    `r = floor(cbrt a)`, provided `x ≤ 2^22`. -/
private theorem cbrt_loop_down_spec (a x xn : u64)
    (h_x_pos : 0 < x.toNat)
    (h_x_ub : a.toNat < (x.toNat + 1) * (x.toNat + 1) * (x.toNat + 1))
    (h_xn_eq : xn.toNat = (a.toNat / (x.toNat * x.toNat) + 2 * x.toNat) / 3)
    (h_a_pos : 1 ≤ a.toNat)
    (h_x_le : x.toNat ≤ 2 ^ 22) :
    ∃ r : u64, nth_root_u64.cbrt_loop_down a x xn = RustM.ok r ∧
      r.toNat * r.toNat * r.toNat ≤ a.toNat ∧
      a.toNat < (r.toNat + 1) * (r.toNat + 1) * (r.toNat + 1) := by
  induction hk : x.toNat using Nat.strongRecOn generalizing x xn with
  | _ k ih =>
    subst hk
    unfold nth_root_u64.cbrt_loop_down
    have h_gt_eqq : (x >? xn : RustM Bool) = pure (decide (x > xn)) := rfl
    rw [h_gt_eqq]
    simp only [pure_bind]
    by_cases hgt : x > xn
    · simp only [decide_eq_true hgt, if_true]
      have h_xn_lt_x : xn.toNat < x.toNat := UInt64.lt_iff_toNat_lt.mp hgt
      have h_xn_pos : 0 < xn.toNat := by
        rw [h_xn_eq]
        rcases Nat.lt_or_ge x.toNat 2 with h_x_lt | h_x_ge
        · have hx1 : x.toNat = 1 := by omega
          rw [hx1]
          have h_one : (1 : Nat) * 1 = 1 := rfl
          rw [h_one, Nat.div_one]
          have h_sum_ge : 3 ≤ a.toNat + 2 * 1 := by omega
          have h_div_le : (3 : Nat) / 3 ≤ (a.toNat + 2 * 1) / 3 := Nat.div_le_div_right h_sum_ge
          have h_three : (3 : Nat) / 3 = 1 := by decide
          omega
        · have h_2x_ge : 2 * x.toNat ≥ 4 := by omega
          have h_div_nn : 0 ≤ a.toNat / (x.toNat * x.toNat) := Nat.zero_le _
          have h_sum_ge : 4 ≤ a.toNat / (x.toNat * x.toNat) + 2 * x.toNat := by omega
          have h_div_le : (4 : Nat) / 3 ≤ (a.toNat / (x.toNat * x.toNat) + 2 * x.toNat) / 3 :=
            Nat.div_le_div_right h_sum_ge
          have h_four : (4 : Nat) / 3 = 1 := by decide
          omega
      have h_xn_le_22 : xn.toNat ≤ 2 ^ 22 := by omega
      rw [u64_mul_self_no_ovf xn h_xn_le_22]
      simp only [pure_bind]
      have h_xnxn_toNat : (xn * xn).toNat = xn.toNat * xn.toNat := by
        apply UInt64.toNat_mul_of_lt
        have h_sq_le : xn.toNat * xn.toNat ≤ 2^22 * 2^22 := Nat.mul_le_mul h_xn_le_22 h_xn_le_22
        have h_pow : (2 : Nat)^22 * 2^22 = 2^44 := by rw [← Nat.pow_add]
        have h_44_64 : (2 : Nat)^44 < 2^64 := by decide
        omega
      have h_xn_xn_ne : xn * xn ≠ 0 := by
        intro hcon
        have h0 : (xn * xn).toNat = 0 := by rw [hcon]; rfl
        rw [h_xnxn_toNat] at h0
        have h_n0 : xn.toNat = 0 := by
          rcases Nat.eq_zero_or_pos xn.toNat with h | h
          · exact h
          · exfalso; have := Nat.mul_pos h h; omega
        omega
      have h_div_a : (a /? (xn * xn) : RustM u64) = pure (a / (xn * xn)) := by
        show (rust_primitives.ops.arith.Div.div a (xn * xn) : RustM u64) = pure (a / (xn * xn))
        show (if (xn * xn) = 0 then (.fail .divisionByZero : RustM u64) else _) = _
        rw [if_neg h_xn_xn_ne]
      rw [h_div_a]
      simp only [pure_bind]
      have h_a_div_toNat : (a / (xn * xn)).toNat = a.toNat / (xn.toNat * xn.toNat) := by
        rw [UInt64.toNat_div, h_xnxn_toNat]
      rw [u64_mul_2_no_ovf xn h_xn_le_22]
      simp only [pure_bind]
      have h_xn2_toNat : (xn * (2 : u64)).toNat = xn.toNat * 2 := by
        apply UInt64.toNat_mul_of_lt
        have h2 : (2 : UInt64).toNat = 2 := rfl
        rw [h2]
        have h_xn_2 : xn.toNat * 2 ≤ 2^22 * 2 := Nat.mul_le_mul_right 2 h_xn_le_22
        have h_pow : (2 : Nat)^22 * 2 < 2^64 := by decide
        omega
      have h_iter_lb : a.toNat < (xn.toNat + 1) * (xn.toNat + 1) * (xn.toNat + 1) := by
        have h_lb := nat_cubic_newton_lb a.toNat x.toNat h_x_pos
        rw [← h_xn_eq] at h_lb
        exact h_lb
      have h_a_div_le : a.toNat / (xn.toNat * xn.toNat) ≤ 8 * xn.toNat :=
        nat_a_div_xnxn_le_8xn a.toNat xn.toNat h_xn_pos h_iter_lb
      have h_no_ovf : a.toNat / (xn.toNat * xn.toNat) + xn.toNat * 2 < 2 ^ 64 := by
        have h_pow_lt : 10 * (2 : Nat)^22 < 2^64 := by decide
        have h_10xn : 10 * xn.toNat ≤ 10 * 2^22 := Nat.mul_le_mul_left 10 h_xn_le_22
        omega
      have h_add : ((a / (xn * xn)) +? (xn * 2) : RustM u64) =
                   pure ((a / (xn * xn)) + (xn * 2)) := by
        show (rust_primitives.ops.arith.Add.add (a / (xn * xn)) (xn * 2) : RustM u64) = _
        show (if BitVec.uaddOverflow (a / (xn * xn)).toBitVec (xn * 2).toBitVec then
                (.fail .integerOverflow : RustM u64)
              else pure ((a / (xn * xn)) + (xn * 2))) = _
        have h_no_ovf' : BitVec.uaddOverflow (a / (xn * xn)).toBitVec (xn * 2).toBitVec = false := by
          cases h_eq : BitVec.uaddOverflow (a / (xn * xn)).toBitVec (xn * 2).toBitVec with
          | false => rfl
          | true =>
            exfalso
            have : UInt64.addOverflow (a / (xn * xn)) (xn * 2) = true := h_eq
            rw [UInt64.addOverflow_iff] at this
            rw [h_a_div_toNat, h_xn2_toNat] at this
            omega
        rw [h_no_ovf']; rfl
      rw [h_add]
      simp only [pure_bind]
      have h_sumN : ((a / (xn * xn)) + (xn * 2)).toNat
                    = a.toNat / (xn.toNat * xn.toNat) + xn.toNat * 2 := by
        rw [UInt64.toNat_add_of_lt]
        · rw [h_a_div_toNat, h_xn2_toNat]
        rw [h_a_div_toNat, h_xn2_toNat]; exact h_no_ovf
      have h_div3 : ((a / (xn * xn) + xn * 2) /? (3 : u64) : RustM u64) =
                    pure ((a / (xn * xn) + xn * 2) / 3) := by
        show (rust_primitives.ops.arith.Div.div ((a / (xn * xn)) + (xn * 2)) (3 : u64) : RustM u64) = _
        show (if (3 : u64) = 0 then (.fail .divisionByZero : RustM u64) else _) = _
        rw [if_neg (by decide : (3 : u64) ≠ 0)]
      rw [h_div3]
      simp only [pure_bind]
      have h_newxn_N : ((a / (xn * xn) + xn * 2) / 3).toNat
                      = (a.toNat / (xn.toNat * xn.toNat) + xn.toNat * 2) / 3 := by
        rw [UInt64.toNat_div, h_sumN]
        have h3 : (3 : UInt64).toNat = 3 := rfl; rw [h3]
      have h_newxn_N' : ((a / (xn * xn) + xn * 2) / 3).toNat
                      = (a.toNat / (xn.toNat * xn.toNat) + 2 * xn.toNat) / 3 := by
        rw [h_newxn_N, Nat.mul_comm xn.toNat 2]
      obtain ⟨r, hr_eq, hr_lb, hr_ub⟩ :=
        ih xn.toNat h_xn_lt_x xn ((a / (xn * xn) + xn * 2) / 3)
          h_xn_pos h_iter_lb h_newxn_N' h_xn_le_22 rfl
      exact ⟨r, hr_eq, hr_lb, hr_ub⟩
    · simp only [decide_eq_false hgt, Bool.false_eq_true, if_false]
      refine ⟨x, rfl, ?_, h_x_ub⟩
      have h_x_le_xn : x.toNat ≤ xn.toNat := by
        have h_not : ¬ x.toNat > xn.toNat := fun h => hgt (UInt64.lt_iff_toNat_lt.mpr h)
        omega
      have h_x_le_iter : x.toNat ≤ (a.toNat / (x.toNat * x.toNat) + 2 * x.toNat) / 3 := by
        rw [← h_xn_eq]; exact h_x_le_xn
      exact (nat_iter_cbrt_ge_self_iff a.toNat x.toNat h_x_pos).mp h_x_le_iter

/-! ## `cbrt_u64` contract clauses

`cbrt_u64 : u64 → RustM u64` is documented as returning the truncated
principal cube root. Same two-clause shape as `sqrt_u64`, exponent 3. -/

/-- Master existential for `cbrt_u64`: returns some `r` simultaneously
    satisfying the lower and upper cube-root bounds. The individual
    contract clauses below project out of this lemma. -/
theorem cbrt_u64_postcondition (a : u64) :
    ∃ r : u64, nth_root_u64.cbrt_u64 a = RustM.ok r ∧
      r.toNat * r.toNat * r.toNat ≤ a.toNat ∧
      a.toNat < (r.toNat + 1) * (r.toNat + 1) * (r.toNat + 1) := by
  unfold nth_root_u64.cbrt_u64
  dsimp only
  rw [show (a <? (8 : u64) : RustM Bool) = pure (decide (a < 8)) from rfl]
  simp only [pure_bind]
  by_cases h_lt_8 : a < 8
  · -- Small-case arm.
    rw [decide_eq_true h_lt_8]
    simp only [if_true]
    rw [show (a >? (0 : u64) : RustM Bool) = pure (decide (a > 0)) from rfl]
    simp only [pure_bind]
    have ha_lt_8 : a.toNat < 8 := UInt64.lt_iff_toNat_lt.mp h_lt_8
    by_cases h_pos : a > 0
    · rw [decide_eq_true h_pos]
      simp only [if_true]
      have ha_pos : 0 < a.toNat := UInt64.lt_iff_toNat_lt.mp h_pos
      refine ⟨1, rfl, ?_, ?_⟩
      · have h1 : (1 : u64).toNat = 1 := rfl
        rw [h1]; omega
      · have h1 : (1 : u64).toNat = 1 := rfl
        rw [h1]; omega
    · rw [decide_eq_false h_pos]
      simp only [Bool.false_eq_true, if_false]
      have ha_zero : a.toNat = 0 := by
        have h_not_pos : ¬ (0 < a.toNat) := fun h => h_pos (UInt64.lt_iff_toNat_lt.mpr h)
        omega
      refine ⟨0, rfl, ?_, ?_⟩
      · have h0 : (0 : u64).toNat = 0 := rfl; rw [h0]; omega
      · have h0 : (0 : u64).toNat = 0 := rfl; rw [h0, ha_zero]; decide
  · -- a ≥ 8.
    rw [decide_eq_false h_lt_8]
    simp only [Bool.false_eq_true, if_false]
    rw [show (a <=? (4294967295 : u64) : RustM Bool) = pure (decide (a ≤ 4294967295)) from rfl]
    simp only [pure_bind]
    have ha_ge_8 : a.toNat ≥ 8 := by
      have h_not : ¬ a.toNat < 8 := fun h => h_lt_8 (UInt64.lt_iff_toNat_lt.mpr h)
      omega
    by_cases h_le_u32 : a ≤ 4294967295
    · -- u32 branch.
      rw [decide_eq_true h_le_u32]
      simp only [if_true]
      have h_cast1 : (rust_primitives.hax.cast_op a : RustM u32) = pure a.toUInt32 := rfl
      rw [h_cast1]
      simp only [pure_bind]
      have ha_le_2_32 : a.toNat ≤ 2 ^ 32 - 1 := by
        have h := UInt64.le_iff_toNat_le.mp h_le_u32
        have h_simp : (4294967295 : u64).toNat = 4294967295 := rfl
        rw [h_simp] at h
        omega
      have h_toU32_toNat : a.toUInt32.toNat = a.toNat := by
        rw [UInt64.toNat_toUInt32]
        exact Nat.mod_eq_of_lt (by omega)
      obtain ⟨y32, hy32_eq, hy32_lb, hy32_ub⟩ := cbrt_u32_correct a.toUInt32
      rw [hy32_eq]
      simp only [RustM_ok_bind]
      have h_cast2 : (rust_primitives.hax.cast_op y32 : RustM u64) = pure y32.toUInt64 := rfl
      rw [h_cast2]
      refine ⟨y32.toUInt64, rfl, ?_, ?_⟩
      · have h_eq : y32.toUInt64.toNat = y32.toNat := UInt32.toNat_toUInt64 y32
        rw [h_eq]
        rw [h_toU32_toNat] at hy32_lb
        exact hy32_lb
      · have h_eq : y32.toUInt64.toNat = y32.toNat := UInt32.toNat_toUInt64 y32
        rw [h_eq]
        rw [h_toU32_toNat] at hy32_ub
        exact hy32_ub
    · -- Newton branch (a > u32::MAX).
      rw [decide_eq_false h_le_u32]
      simp only [Bool.false_eq_true, if_false]
      have ha_ge_2_32 : a.toNat ≥ 2 ^ 32 := by
        have h_not : ¬ a ≤ 4294967295 := h_le_u32
        have h_iff : ¬ a.toNat ≤ (4294967295 : u64).toNat := by
          intro hcon
          exact h_not (UInt64.le_iff_toNat_le.mpr hcon)
        have h_simp : (4294967295 : u64).toNat = 4294967295 := rfl
        rw [h_simp] at h_iff
        omega
      obtain ⟨g, hg_eq, hg_pos, hg_le, hg_cube_ge⟩ := cbrt_guess_u64_correct a ha_ge_2_32
      rw [hg_eq]
      simp only [RustM_ok_bind]
      have h_g_sq_lt : g.toNat * g.toNat < 2 ^ 64 := by
        have h_g_sq_le : g.toNat * g.toNat ≤ 2 ^ 22 * 2 ^ 22 :=
          Nat.mul_le_mul hg_le hg_le
        have h_pow_add : (2 : Nat) ^ 22 * 2 ^ 22 = 2 ^ 44 := by
          rw [← Nat.pow_add]
        have h_2_44 : (2 : Nat) ^ 44 < 2 ^ 64 := by decide
        omega
      rw [u64_mul_self_no_ovf g hg_le]
      simp only [pure_bind]
      have h_gg_toNat : (g * g).toNat = g.toNat * g.toNat := by
        apply UInt64.toNat_mul_of_lt
        exact h_g_sq_lt
      have h_gg_ne : g * g ≠ 0 := by
        intro hcon
        have h0 : (g * g).toNat = 0 := by rw [hcon]; rfl
        rw [h_gg_toNat] at h0
        have : g.toNat = 0 := by
          rcases Nat.eq_zero_or_pos g.toNat with h | h
          · exact h
          · exfalso; have := Nat.mul_pos h h; omega
        omega
      have h_div_a : (a /? (g * g) : RustM u64) = pure (a / (g * g)) := by
        show (rust_primitives.ops.arith.Div.div a (g * g) : RustM u64) = pure (a / (g * g))
        show (if (g * g) = 0 then (.fail .divisionByZero : RustM u64) else pure (a / (g * g))) =
             pure (a / (g * g))
        rw [if_neg h_gg_ne]
      rw [h_div_a]
      simp only [pure_bind]
      have h_agg_toNat : (a / (g * g)).toNat = a.toNat / (g.toNat * g.toNat) := by
        rw [UInt64.toNat_div, h_gg_toNat]
      rw [u64_mul_2_no_ovf g hg_le]
      simp only [pure_bind]
      have h_g2_toNat : (g * (2 : u64)).toNat = g.toNat * 2 := by
        apply UInt64.toNat_mul_of_lt
        have h2 : (2 : UInt64).toNat = 2 := rfl
        rw [h2]
        have h_g_le_22 : g.toNat ≤ 2^22 := hg_le
        have h_g_2 : g.toNat * 2 ≤ 2^22 * 2 := Nat.mul_le_mul_right 2 h_g_le_22
        have h_pow : (2 : Nat)^22 * 2 < 2^64 := by decide
        omega
      have h_agg_le_g : a.toNat / (g.toNat * g.toNat) ≤ g.toNat := by
        have h_a_le : a.toNat ≤ g.toNat * g.toNat * g.toNat := hg_cube_ge
        have h_a_le2 : a.toNat ≤ g.toNat * (g.toNat * g.toNat) := by
          rw [Nat.mul_assoc] at h_a_le; exact h_a_le
        have h_gg_pos : 0 < g.toNat * g.toNat := Nat.mul_pos hg_pos hg_pos
        have h_div_le : a.toNat / (g.toNat * g.toNat) ≤ (g.toNat * (g.toNat * g.toNat)) / (g.toNat * g.toNat) :=
          Nat.div_le_div_right h_a_le2
        have h_self : g.toNat * (g.toNat * g.toNat) / (g.toNat * g.toNat) = g.toNat :=
          Nat.mul_div_cancel g.toNat h_gg_pos
        omega
      have h_g_2_22 : g.toNat * 2 ≤ 2 ^ 23 := by
        have h_g_le_22 : g.toNat ≤ 2^22 := hg_le
        have h_pow_eq : (2 : Nat) ^ 22 * 2 = 2 ^ 23 := by decide
        have : g.toNat * 2 ≤ 2 ^ 22 * 2 := Nat.mul_le_mul_right 2 h_g_le_22
        omega
      have h_add_no_ovf : a.toNat / (g.toNat * g.toNat) + g.toNat * 2 < 2 ^ 64 := by
        have h_3g : 3 * g.toNat ≤ 3 * 2^22 := Nat.mul_le_mul_left 3 hg_le
        have h_pow_lt : 3 * (2 : Nat)^22 < 2^64 := by decide
        omega
      have h_add : ((a / (g * g)) +? (g * 2) : RustM u64) = pure ((a / (g * g)) + (g * 2)) := by
        show (rust_primitives.ops.arith.Add.add (a / (g * g)) (g * 2) : RustM u64) = _
        show (if BitVec.uaddOverflow (a / (g * g)).toBitVec (g * 2).toBitVec then
                (.fail .integerOverflow : RustM u64)
              else pure ((a / (g * g)) + (g * 2))) = _
        have h_no_ovf' : BitVec.uaddOverflow (a / (g * g)).toBitVec (g * 2).toBitVec = false := by
          cases h_eq : BitVec.uaddOverflow (a / (g * g)).toBitVec (g * 2).toBitVec with
          | false => rfl
          | true =>
            exfalso
            have : UInt64.addOverflow (a / (g * g)) (g * 2) = true := h_eq
            rw [UInt64.addOverflow_iff] at this
            rw [h_agg_toNat, h_g2_toNat] at this
            omega
        rw [h_no_ovf']; rfl
      rw [h_add]
      simp only [pure_bind]
      have h_sumN : ((a / (g * g)) + (g * 2)).toNat = a.toNat / (g.toNat * g.toNat) + g.toNat * 2 := by
        rw [UInt64.toNat_add_of_lt]; · rw [h_agg_toNat, h_g2_toNat]
        rw [h_agg_toNat, h_g2_toNat]; exact h_add_no_ovf
      have h_div3 : ((a / (g * g) + g * 2) /? (3 : u64) : RustM u64) =
                    pure ((a / (g * g) + g * 2) / 3) := by
        show (rust_primitives.ops.arith.Div.div ((a / (g * g)) + (g * 2)) (3 : u64) : RustM u64) = _
        show (if (3 : u64) = 0 then (.fail .divisionByZero : RustM u64) else _) = _
        rw [if_neg (by decide : (3 : u64) ≠ 0)]
      rw [h_div3]
      simp only [pure_bind]
      have h_xn0N : ((a / (g * g) + g * 2) / 3).toNat
                    = (a.toNat / (g.toNat * g.toNat) + g.toNat * 2) / 3 := by
        rw [UInt64.toNat_div, h_sumN]
        have h3 : (3 : UInt64).toNat = 3 := rfl
        rw [h3]
      have h_xn0N' : ((a / (g * g) + g * 2) / 3).toNat
                    = (a.toNat / (g.toNat * g.toNat) + 2 * g.toNat) / 3 := by
        rw [h_xn0N, Nat.mul_comm g.toNat 2]
      -- Apply cbrt_loop_up_spec_overest.
      have ha_pos : 0 < a.toNat := by omega
      obtain ⟨h_up_eq, h_xn_le_g⟩ :=
        cbrt_loop_up_spec_overest a g ((a / (g * g) + g * 2) / 3) hg_pos hg_cube_ge h_xn0N'
      rw [h_up_eq]
      simp only [RustM_ok_bind]
      -- Apply cbrt_loop_down_spec.
      have h_a_ub_g : a.toNat < (g.toNat + 1) * (g.toNat + 1) * (g.toNat + 1) := by
        have h_succ_cube := nat_succ_cube g.toNat
        omega
      have h_a_pos : 1 ≤ a.toNat := by omega
      obtain ⟨r, hr_eq, hr_lb, hr_ub⟩ :=
        cbrt_loop_down_spec a g ((a / (g * g) + g * 2) / 3) hg_pos h_a_ub_g h_xn0N' h_a_pos hg_le
      exact ⟨r, hr_eq, hr_lb, hr_ub⟩

/-- Totality / no-panic for `cbrt_u64`. -/
theorem cbrt_u64_total (a : u64) :
    ∃ r : u64, nth_root_u64.cbrt_u64 a = RustM.ok r := by
  obtain ⟨r, hr, _, _⟩ := cbrt_u64_postcondition a
  exact ⟨r, hr⟩

/-- Lower bound (independent clause) for `cbrt_u64`: `cbrt(a)³ ≤ a`.
    Captures the property test `prop_cbrt_lower_bound`. -/
theorem cbrt_u64_lower_bound (a : u64) :
    ∃ r : u64, nth_root_u64.cbrt_u64 a = RustM.ok r ∧
      r.toNat * r.toNat * r.toNat ≤ a.toNat := by
  obtain ⟨r, hr, hlb, _⟩ := cbrt_u64_postcondition a
  exact ⟨r, hr, hlb⟩

/-- Upper bound (independent clause) for `cbrt_u64`: `a < (cbrt(a) + 1)³`,
    stated at `Nat`-level. Captures `prop_cbrt_upper_bound`. -/
theorem cbrt_u64_upper_bound (a : u64) :
    ∃ r : u64, nth_root_u64.cbrt_u64 a = RustM.ok r ∧
      a.toNat < (r.toNat + 1) * (r.toNat + 1) * (r.toNat + 1) := by
  obtain ⟨r, hr, _, hub⟩ := cbrt_u64_postcondition a
  exact ⟨r, hr, hub⟩

/-! ## `nth_root` contract clauses

`nth_root : u64 → u32 → RustM u64` is documented as returning the
truncated principal `n`-th root of its first argument for `n ≥ 1`.
The contract has three clauses:

  * **Failure (panic)** — `n == 0` triggers a u32 underflow inside
    the `n - 1` subtraction. Hax models this as
    `RustM.fail Error.integerOverflow`, which is the same observable
    effect as the original `panic!("…")` (see the crate-level comment
    on why `panic!` with a format string is rewritten this way).
    Captured by the `#[should_panic] zeroth_root` test.
  * **Lower bound** — `r^n ≤ a` for any `n ≥ 1` and any `a`. Captures
    `prop_nth_root_lower_bound`.
  * **Upper bound** — `a < (r+1)^n`, stated at the `Nat` level so the
    "modulo overflow" caveat from the Rust property test drops out
    (when `n ≥ 64` the bound `(1+1)^n ≥ 2⁶⁴ > a.toNat` is automatic).
    Captures `prop_nth_root_upper_bound`.

Feasibility note: the proptest samples `n in 1u32..=128`, but the
universal statement (any `n ≥ 1`) is in fact correct in the Lean
model — the `n ≥ 64` branch returns `1` (or `0` at `a = 0`) from a
fast-path arm that never touches the Newton iteration, with bounds
that hold trivially. So we use the full universal precondition
`1 ≤ n.toNat` rather than mimicking the proptest's sampling range. -/

/-! ## Foundational lemmas for the general n-th root Newton step -/

/-- Helper: `y * y + x * x ≥ 2 * y * x` (from `(y - x)^2 ≥ 0`). -/
private theorem nat_sq_ge_2yx (y x : Nat) : y * y + x * x ≥ 2 * y * x := by
  rcases Nat.le_total x y with h | h
  · obtain ⟨d, hd⟩ : ∃ d, y = x + d := ⟨y - x, by omega⟩
    subst hd
    -- Goal: (x+d)*(x+d) + x*x ≥ 2*(x+d)*x
    have h_lhs : (x + d) * (x + d) = x*x + x*d + x*d + d*d := nat_sum_sq_expand x d
    have h_rhs : 2 * (x + d) * x = 2*(x*x) + 2*(x*d) := by
      have e1 : 2 * (x + d) * x = 2 * ((x + d) * x) := Nat.mul_assoc _ _ _
      have e2 : (x + d) * x = x*x + d*x := Nat.add_mul _ _ _
      have e3 : 2 * (x*x + d*x) = 2*(x*x) + 2*(d*x) := Nat.mul_add _ _ _
      have e4 : d * x = x * d := Nat.mul_comm _ _
      omega
    have h_d_sq_nn : d * d ≥ 0 := Nat.zero_le _
    omega
  · obtain ⟨d, hd⟩ : ∃ d, x = y + d := ⟨x - y, by omega⟩
    subst hd
    -- Goal: y*y + (y+d)*(y+d) ≥ 2*y*(y+d)
    have h_lhs : (y + d) * (y + d) = y*y + y*d + y*d + d*d := nat_sum_sq_expand y d
    have h_rhs : 2 * y * (y + d) = 2*(y*y) + 2*(y*d) := by
      have e1 : 2 * y * (y + d) = 2 * (y * (y + d)) := Nat.mul_assoc _ _ _
      have e2 : y * (y + d) = y*y + y*d := Nat.mul_add _ _ _
      have e3 : 2 * (y*y + y*d) = 2*(y*y) + 2*(y*d) := Nat.mul_add _ _ _
      omega
    have h_d_sq_nn : d * d ≥ 0 := Nat.zero_le _
    omega

/-- Young's inequality for natural numbers:
    `y^(n+1) + n * x^(n+1) ≥ (n+1) * y * x^n`.
    Proved by induction on n using `(y-x)² ≥ 0`. -/
private theorem nat_young (y x : Nat) (n : Nat) :
    y ^ (n + 1) + n * x ^ (n + 1) ≥ (n + 1) * y * x ^ n := by
  induction n with
  | zero =>
    show y ^ 1 + 0 * x ^ 1 ≥ 1 * y * x ^ 0
    rw [Nat.pow_one, Nat.pow_one, Nat.pow_zero, Nat.zero_mul, Nat.add_zero,
        Nat.mul_one, Nat.one_mul]
    exact Nat.le_refl _
  | succ k ih =>
    -- Goal: y^(k+1+1) + (k+1)*x^(k+1+1) ≥ (k+1+1)*y*x^(k+1)
    have hXkX : x ^ k * x = x ^ (k + 1) := (Nat.pow_succ x k).symm
    have hXk1X : x ^ (k + 1) * x = x ^ (k + 1 + 1) := (Nat.pow_succ x (k+1)).symm
    have hYY1 : y * y ^ (k + 1) = y ^ (k + 1 + 1) := by
      rw [show y ^ (k + 1 + 1) = y ^ (k + 1) * y from Nat.pow_succ y (k+1),
          Nat.mul_comm y (y ^ (k + 1))]
    -- (P1): y^(k+1+1) + k * (y * x^(k+1)) ≥ (k+1) * (y*y) * x^k.
    have hP1 : y ^ (k + 1 + 1) + k * (y * x ^ (k + 1))
             ≥ (k + 1) * (y * y) * x ^ k := by
      have hMy : y * (y ^ (k + 1) + k * x ^ (k + 1)) ≥ y * ((k + 1) * y * x ^ k) :=
        Nat.mul_le_mul_left y ih
      have hMy_LHS : y * (y ^ (k + 1) + k * x ^ (k + 1))
                    = y ^ (k + 1 + 1) + k * (y * x ^ (k + 1)) := by
        rw [Nat.mul_add, hYY1]
        congr 1
        rw [← Nat.mul_assoc, Nat.mul_comm y k, Nat.mul_assoc]
      have hMy_RHS : y * ((k + 1) * y * x ^ k) = (k + 1) * (y * y) * x ^ k := by
        calc y * ((k + 1) * y * x ^ k)
            = ((k + 1) * y * x ^ k) * y := Nat.mul_comm _ _
          _ = (k + 1) * y * (x ^ k * y) := Nat.mul_assoc _ _ _
          _ = (k + 1) * y * (y * x ^ k) := by rw [Nat.mul_comm (x^k) y]
          _ = (k + 1) * (y * (y * x ^ k)) := Nat.mul_assoc _ _ _
          _ = (k + 1) * (y * y * x ^ k) := by rw [Nat.mul_assoc y y (x^k)]
          _ = (k + 1) * (y * y) * x ^ k := (Nat.mul_assoc _ _ _).symm
      rw [hMy_LHS, hMy_RHS] at hMy
      exact hMy
    -- (P2): (k+1)*(y*y)*x^k + (k+1)*x^(k+1+1) ≥ 2*(k+1)*(y * x^(k+1)).
    have hP2 : (k + 1) * (y * y) * x ^ k + (k + 1) * x ^ (k + 1 + 1)
             ≥ 2 * (k + 1) * (y * x ^ (k + 1)) := by
      have hSq : y * y + x * x ≥ 2 * y * x := nat_sq_ge_2yx y x
      have hSqMul : (k + 1) * x ^ k * (y * y + x * x) ≥ (k + 1) * x ^ k * (2 * y * x) :=
        Nat.mul_le_mul_left _ hSq
      have hSqL : (k + 1) * x ^ k * (y * y + x * x)
                = (k + 1) * (y * y) * x ^ k + (k + 1) * x ^ (k + 1 + 1) := by
        rw [Nat.mul_add]
        congr 1
        · rw [Nat.mul_assoc (k+1) (x^k) (y*y), Nat.mul_comm (x^k) (y*y),
              ← Nat.mul_assoc]
        · rw [Nat.mul_assoc (k+1) (x^k) (x*x)]
          congr 1
          rw [← Nat.mul_assoc, hXkX, hXk1X]
      have hSqR : (k + 1) * x ^ k * (2 * y * x) = 2 * (k + 1) * (y * x ^ (k + 1)) := by
        calc (k + 1) * x ^ k * (2 * y * x)
            = (k + 1) * (x ^ k * (2 * y * x)) := Nat.mul_assoc _ _ _
          _ = (k + 1) * (2 * y * (x ^ k * x)) := by
              congr 1
              calc x ^ k * (2 * y * x)
                  = (2 * y * x) * x ^ k := Nat.mul_comm _ _
                _ = 2 * y * (x * x ^ k) := Nat.mul_assoc _ _ _
                _ = 2 * y * (x ^ k * x) := by rw [Nat.mul_comm x (x^k)]
          _ = (k + 1) * (2 * y * x ^ (k + 1)) := by rw [hXkX]
          _ = (k + 1) * (2 * (y * x ^ (k + 1))) := by rw [Nat.mul_assoc 2 y (x^(k+1))]
          _ = 2 * (k + 1) * (y * x ^ (k + 1)) := by
              rw [← Nat.mul_assoc (k+1) 2 (y * x^(k+1)),
                  Nat.mul_comm (k+1) 2,
                  Nat.mul_assoc 2 (k+1) (y * x^(k+1))]
      rw [hSqL, hSqR] at hSqMul
      exact hSqMul
    -- Combine P1 and P2 via omega over the four atoms:
    --   A := y^(k+1+1), B := y * x^(k+1), C := x^(k+1+1), D := (k+1)*(y*y)*x^k.
    show y ^ (k + 1 + 1) + (k + 1) * x ^ (k + 1 + 1) ≥ (k + 1 + 1) * y * x ^ (k + 1)
    have hGoalRHS : (k + 1 + 1) * y * x ^ (k + 1) = (k + 1 + 1) * (y * x ^ (k + 1)) :=
      Nat.mul_assoc _ _ _
    rw [hGoalRHS]
    -- Linear identity: 2*(k+1) * B = (k+1+1) * B + k * B (since 2*(k+1) = (k+1+1) + k).
    have hSplit : 2 * (k + 1) * (y * x ^ (k + 1))
                = (k + 1 + 1) * (y * x ^ (k + 1)) + k * (y * x ^ (k + 1)) := by
      rw [show (2 * (k + 1) : Nat) = (k + 1 + 1) + k from by omega, Nat.add_mul]
    omega

/-- AM-GM step lemma: if `n*y ≥ z + (n-1)*x`, then `y^n ≥ z * x^(n-1)`. -/
private theorem nat_amgm_step (n y z x : Nat) (hn : 1 ≤ n)
    (h : n * y ≥ z + (n - 1) * x) :
    y ^ n ≥ z * x ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h
  -- Goal currently: y^(m+1) ≥ z * x^(m + 1 - 1). Simplify the goal too.
  show y ^ (m + 1) ≥ z * x ^ m
  have h_young := nat_young y x m
  have hX : x ^ (m + 1) = x ^ m * x := Nat.pow_succ x m
  rw [hX] at h_young
  -- h_young : y^(m+1) + m * (x^m * x) ≥ (m+1) * y * x^m.
  have h_my_ge_mx : (m + 1) * y ≥ m * x := by omega
  have h_diff_ge : (m + 1) * y * x ^ m ≥ m * (x ^ m * x) := by
    have h_step1 : m * (x ^ m * x) = m * x * x ^ m := by
      rw [Nat.mul_comm (x ^ m) x, ← Nat.mul_assoc]
    rw [h_step1]
    exact Nat.mul_le_mul_right (x ^ m) h_my_ge_mx
  have h_y_ge : y ^ (m + 1) ≥ (m + 1) * y * x ^ m - m * (x ^ m * x) := by omega
  have h_factor : (m + 1) * y * x ^ m - m * (x ^ m * x)
                 = x ^ m * ((m + 1) * y - m * x) := by
    have h_eq1 : (m + 1) * y * x ^ m = x ^ m * ((m + 1) * y) := by
      rw [Nat.mul_comm ((m+1)*y) (x^m)]
    have h_eq2 : m * (x ^ m * x) = x ^ m * (m * x) := by
      rw [← Nat.mul_assoc, Nat.mul_comm m (x ^ m), Nat.mul_assoc]
    rw [h_eq1, h_eq2, ← Nat.mul_sub]
  rw [h_factor] at h_y_ge
  have h_diff_z : (m + 1) * y - m * x ≥ z := by omega
  have h_final : x ^ m * ((m + 1) * y - m * x) ≥ x ^ m * z :=
    Nat.mul_le_mul_left _ h_diff_z
  have h_comm : x ^ m * z = z * x ^ m := Nat.mul_comm _ _
  omega

/-- Nat-level lemma: the Newton step preserves the upper-bound invariant.
    Given `a < 2^64`, `x ≥ 1`, `n1 ≥ 1`, the Newton step
    `step := ((if x^n1 < 2^64 then a/x^n1 else 0) + x*n1) / (n1+1)`
    satisfies `a < (step + 1)^(n1+1)`. -/
private theorem nat_nth_root_step_ub_preserved
    (a x n1 : Nat) (h_a_lt : a < 2 ^ 64) (h_x_pos : 1 ≤ x) (h_n1_pos : 1 ≤ n1) :
    a < ((((if x ^ n1 < 2 ^ 64 then a / x ^ n1 else 0) + x * n1) / (n1 + 1)) + 1) ^ (n1 + 1) := by
  -- Introduce abbreviations via generalize.
  let y : Nat := if x ^ n1 < 2 ^ 64 then a / x ^ n1 else 0
  let step : Nat := (y + x * n1) / (n1 + 1)
  show a < (step + 1) ^ (n1 + 1)
  have h_n_pos : 1 ≤ n1 + 1 := by omega
  -- (y + 1) * x^n1 > a in both cases.
  have h_yplus1_xn1_gt_a : (y + 1) * x ^ n1 > a := by
    by_cases h_ovf : x ^ n1 < 2 ^ 64
    · have h_y_eq : y = a / x ^ n1 := if_pos h_ovf
      show (y + 1) * x ^ n1 > a
      rw [h_y_eq]
      have h_x_n1_pos : 0 < x ^ n1 := Nat.pow_pos h_x_pos
      have h_div_mod := Nat.div_add_mod a (x ^ n1)
      have h_mod_lt : a % x ^ n1 < x ^ n1 := Nat.mod_lt _ h_x_n1_pos
      have h_comm : x ^ n1 * (a / x ^ n1) = (a / x ^ n1) * x ^ n1 := Nat.mul_comm _ _
      have h_add_one : (a / x ^ n1 + 1) * x ^ n1 = (a / x ^ n1) * x ^ n1 + x ^ n1 := by
        rw [Nat.add_mul, Nat.one_mul]
      omega
    · have h_y_eq : y = 0 := if_neg h_ovf
      show (y + 1) * x ^ n1 > a
      rw [h_y_eq, Nat.zero_add, Nat.one_mul]
      have h_x_n1_ge : x ^ n1 ≥ 2 ^ 64 := Nat.le_of_not_lt h_ovf
      omega
  have h_step_ineq : (n1 + 1) * (step + 1) ≥ (y + 1) + n1 * x := by
    show (n1 + 1) * (step + 1) ≥ (y + 1) + n1 * x
    have h_div_mod := Nat.div_add_mod (y + x * n1) (n1 + 1)
    have h_mod_lt : (y + x * n1) % (n1 + 1) < n1 + 1 := Nat.mod_lt _ (by omega)
    have h_n_step : (n1 + 1) * step + (y + x * n1) % (n1 + 1) = y + x * n1 := by
      show (n1 + 1) * ((y + x * n1) / (n1 + 1)) + _ = _
      exact h_div_mod
    have h_xn1 : x * n1 = n1 * x := Nat.mul_comm x n1
    have h_lhs_eq : (n1 + 1) * (step + 1) = (n1 + 1) * step + (n1 + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
    omega
  have h_n_minus_eq : (n1 + 1) - 1 = n1 := by omega
  have h_step_ineq' : (n1 + 1) * (step + 1) ≥ (y + 1) + ((n1 + 1) - 1) * x := by
    rw [h_n_minus_eq]; exact h_step_ineq
  have h_amgm := nat_amgm_step (n1 + 1) (step + 1) (y + 1) x h_n_pos h_step_ineq'
  -- h_amgm : (step + 1)^(n1+1) ≥ (y + 1) * x^((n1+1)-1)
  rw [h_n_minus_eq] at h_amgm
  -- (step + 1)^(n1+1) ≥ (y + 1) * x^n1 > a
  omega

/-- Nat-level: if `step ≥ x` (loop exit), then `x^(n1+1) ≤ a` provided
    we're in the no-overflow regime (which is forced by step ≥ x ≥ 1). -/
private theorem nat_nth_root_step_exit_implies_lb
    (a x n1 : Nat) (h_x_pos : 1 ≤ x) (h_n1_pos : 1 ≤ n1) (h_a_lt : a < 2 ^ 64)
    (h_exit : x ≤ (((if x ^ n1 < 2 ^ 64 then a / x ^ n1 else 0) + x * n1) / (n1 + 1))) :
    x ^ (n1 + 1) ≤ a := by
  let y : Nat := if x ^ n1 < 2 ^ 64 then a / x ^ n1 else 0
  have h_x_le_y : x ≤ y := by
    show x ≤ y
    have h_div_mod := Nat.div_add_mod (y + x * n1) (n1 + 1)
    have h_mod_lt : (y + x * n1) % (n1 + 1) < n1 + 1 := Nat.mod_lt _ (by omega)
    have h_step_le : (n1 + 1) * ((y + x * n1) / (n1 + 1)) ≤ y + x * n1 := by omega
    have h_n_x : (n1 + 1) * x ≤ (n1 + 1) * ((y + x * n1) / (n1 + 1)) :=
      Nat.mul_le_mul_left (n1 + 1) h_exit
    have h_n_x_le : (n1 + 1) * x ≤ y + x * n1 := Nat.le_trans h_n_x h_step_le
    have h_xn1_comm : x * n1 = n1 * x := Nat.mul_comm _ _
    have h_n_x_expand : (n1 + 1) * x = n1 * x + x := by
      rw [Nat.add_mul, Nat.one_mul]
    omega
  -- y is non-overflow case (x ≥ 1 means y ≥ 1, so overflow case would give y = 0)
  show x ^ (n1 + 1) ≤ a
  by_cases h_ovf : x ^ n1 < 2 ^ 64
  · have h_y_eq : y = a / x ^ n1 := if_pos h_ovf
    rw [h_y_eq] at h_x_le_y
    -- x ≤ a / x^n1 implies x * x^n1 ≤ a
    have h_div_le : x * x ^ n1 ≤ (a / x ^ n1) * x ^ n1 := Nat.mul_le_mul_right _ h_x_le_y
    have h_div_mul_le : (a / x ^ n1) * x ^ n1 ≤ a := Nat.div_mul_le_self a (x ^ n1)
    have h_pow : x * x ^ n1 = x ^ (n1 + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm]
    omega
  · exfalso
    have h_y_zero : y = 0 := if_neg h_ovf
    rw [h_y_zero] at h_x_le_y
    omega

/-- Spec of `pow_u64_opt`: returns `.Some (x^n mod 2^64)` if it fits,
    else `.None`. -/
private theorem pow_u64_opt_spec (x : u64) (n : u32) :
    nth_root_u64.pow_u64_opt x n = RustM.ok
      (if x.toNat ^ n.toNat < 2 ^ 64
       then .Some (UInt64.ofNat (x.toNat ^ n.toNat))
       else .None) := by
  induction hk : n.toNat using Nat.strongRecOn generalizing n with
  | _ k ih =>
    subst hk
    unfold nth_root_u64.pow_u64_opt
    have h_eq_eqq : (n ==? (0 : u32) : RustM Bool) = pure (decide (n = 0)) := rfl
    rw [h_eq_eqq]
    simp only [pure_bind]
    by_cases h_n0 : n = 0
    · -- n = 0 case
      simp only [decide_eq_true h_n0, if_true]
      have h_n_toNat : n.toNat = 0 := by rw [h_n0]; rfl
      rw [h_n_toNat, Nat.pow_zero, if_pos (by decide : (1 : Nat) < 2 ^ 64)]
      have h_one : UInt64.ofNat 1 = 1 := rfl
      rw [h_one]
      rfl
    · -- n ≥ 1 case
      simp only [decide_eq_false h_n0, Bool.false_eq_true, if_false]
      have h_n_pos : 0 < n.toNat := by
        rcases Nat.eq_zero_or_pos n.toNat with h | h
        · exfalso; apply h_n0; apply UInt32.toNat_inj.mp; rw [h]; rfl
        · exact h
      have h_n_lt : n.toNat < 2 ^ 32 := n.toNat_lt
      have h_1_toNat : (1 : u32).toNat = 1 := rfl
      -- Reduce n -? 1.
      have h_sub : (n -? (1 : u32) : RustM u32) = pure (n - 1) := by
        show (rust_primitives.ops.arith.Sub.sub n (1 : u32) : RustM u32) = pure (n - 1)
        show (if BitVec.usubOverflow n.toBitVec (1 : u32).toBitVec then
                (.fail .integerOverflow : RustM u32)
              else pure (n - 1)) = _
        have h_no_ovf : BitVec.usubOverflow n.toBitVec ((1 : u32).toBitVec) = false := by
          cases h_eq : BitVec.usubOverflow n.toBitVec ((1 : u32).toBitVec) with
          | false => rfl
          | true =>
            exfalso
            have : UInt32.subOverflow n (1 : u32) = true := h_eq
            rw [UInt32.subOverflow_iff] at this
            rw [h_1_toNat] at this
            omega
        rw [h_no_ovf]; rfl
      rw [h_sub]
      simp only [pure_bind]
      have h_n_minus_toNat : (n - (1 : u32)).toNat = n.toNat - 1 := by
        apply UInt32.toNat_sub_of_le'
        rw [h_1_toNat]; omega
      have h_n_minus_lt : (n - (1 : u32)).toNat < n.toNat := by
        rw [h_n_minus_toNat]; omega
      -- Apply IH.
      rw [ih (n - (1 : u32)).toNat h_n_minus_lt (n - 1) rfl]
      simp only [RustM_ok_bind]
      -- Two cases on the IH: x^(n-1) < 2^64 or not.
      by_cases h_rec_ovf : x.toNat ^ (n - (1 : u32)).toNat < 2 ^ 64
      · rw [if_pos h_rec_ovf]
        simp only
        -- Match `Some rest`
        -- Now reduce x ==? 0
        have h_eq_eqq2 : (x ==? (0 : u64) : RustM Bool) = pure (decide (x = 0)) := rfl
        rw [h_eq_eqq2]
        simp only [pure_bind]
        by_cases h_x0 : x = 0
        · simp only [decide_eq_true h_x0, if_true]
          -- x = 0 case
          have h_x_toNat : x.toNat = 0 := by rw [h_x0]; rfl
          rw [h_x_toNat, Nat.zero_pow h_n_pos, if_pos (by decide : (0 : Nat) < 2 ^ 64)]
          have h_zero : UInt64.ofNat 0 = 0 := rfl
          rw [h_zero]
          rfl
        · simp only [decide_eq_false h_x0, Bool.false_eq_true, if_false]
          have h_x_pos : 0 < x.toNat := by
            rcases Nat.eq_zero_or_pos x.toNat with h | h
            · exfalso; apply h_x0; apply UInt64.toNat_inj.mp; rw [h]; rfl
            · exact h
          -- Now reduce 18446744073709551615 /? x.
          have h_max_div : ((18446744073709551615 : u64) /? x : RustM u64) =
                           pure ((18446744073709551615 : u64) / x) := by
            show (rust_primitives.ops.arith.Div.div (18446744073709551615 : u64) x : RustM u64) = _
            show (if x = 0 then (.fail .divisionByZero : RustM u64) else _) = _
            rw [if_neg h_x0]
          rw [h_max_div]
          simp only [pure_bind]
          have h_max_toNat : (18446744073709551615 : u64).toNat = 2 ^ 64 - 1 := by decide
          have h_max_div_toNat : ((18446744073709551615 : u64) / x).toNat =
                                  (2 ^ 64 - 1) / x.toNat := by
            rw [UInt64.toNat_div, h_max_toNat]
          -- Now reduce rest >? (MAX/x).
          have h_rest_toNat : (UInt64.ofNat (x.toNat ^ (n - (1 : u32)).toNat)).toNat =
                              x.toNat ^ (n - (1 : u32)).toNat :=
            UInt64.toNat_ofNat_of_lt' (by omega : x.toNat ^ (n - (1 : u32)).toNat < 2 ^ 64)
          have h_gt_eqq : ((UInt64.ofNat (x.toNat ^ (n - (1 : u32)).toNat)) >?
                            ((18446744073709551615 : u64) / x) : RustM Bool) =
                          pure (decide ((UInt64.ofNat (x.toNat ^ (n - (1 : u32)).toNat)) >
                                        ((18446744073709551615 : u64) / x))) := rfl
          rw [h_gt_eqq]
          simp only [pure_bind]
          -- Goal becomes if-decide on whether rest > MAX/x.
          by_cases h_rest_gt : (UInt64.ofNat (x.toNat ^ (n - (1 : u32)).toNat)) >
                               ((18446744073709551615 : u64) / x)
          · simp only [decide_eq_true h_rest_gt, if_true]
            -- This means overflow: x^n ≥ 2^64.
            have h_gt_N : x.toNat ^ (n - (1 : u32)).toNat > (2 ^ 64 - 1) / x.toNat := by
              have h := UInt64.lt_iff_toNat_lt.mp h_rest_gt
              rw [h_max_div_toNat, h_rest_toNat] at h
              exact h
            -- Need: x^n ≥ 2^64.
            have h_n_succ : n.toNat = (n - (1 : u32)).toNat + 1 := by
              rw [h_n_minus_toNat]; omega
            have h_pow_n : x.toNat ^ n.toNat = x.toNat ^ (n - (1 : u32)).toNat * x.toNat := by
              rw [h_n_succ, Nat.pow_succ]
            have h_rest_ge : x.toNat ^ (n - (1 : u32)).toNat ≥ (2 ^ 64 - 1) / x.toNat + 1 := by
              omega
            have h_mul_ge : (x.toNat ^ (n - (1 : u32)).toNat) * x.toNat ≥
                            ((2 ^ 64 - 1) / x.toNat + 1) * x.toNat :=
              Nat.mul_le_mul_right x.toNat h_rest_ge
            have h_factor : ((2 ^ 64 - 1) / x.toNat + 1) * x.toNat ≥ 2 ^ 64 := by
              have h_dm := Nat.div_add_mod (2 ^ 64 - 1) x.toNat
              have h_mod_lt : (2 ^ 64 - 1) % x.toNat < x.toNat := Nat.mod_lt _ h_x_pos
              have h_dist : ((2 ^ 64 - 1) / x.toNat + 1) * x.toNat
                          = (2 ^ 64 - 1) / x.toNat * x.toNat + x.toNat := by
                rw [Nat.add_mul, Nat.one_mul]
              have h_swap : x.toNat * ((2 ^ 64 - 1) / x.toNat)
                          = (2 ^ 64 - 1) / x.toNat * x.toNat := Nat.mul_comm _ _
              omega
            have h_pow_ge : x.toNat ^ n.toNat ≥ 2 ^ 64 := by
              rw [h_pow_n]; omega
            rw [if_neg (Nat.not_lt.mpr h_pow_ge)]
            rfl
          · simp only [decide_eq_false h_rest_gt, Bool.false_eq_true, if_false]
            -- No overflow: x^n < 2^64.
            have h_le_N : x.toNat ^ (n - (1 : u32)).toNat ≤ (2 ^ 64 - 1) / x.toNat := by
              have h_not_lt : ¬ ((18446744073709551615 : u64) / x) <
                              (UInt64.ofNat (x.toNat ^ (n - (1 : u32)).toNat)) :=
                fun h => h_rest_gt h
              have h_le : (UInt64.ofNat (x.toNat ^ (n - (1 : u32)).toNat)).toNat ≤
                          ((18446744073709551615 : u64) / x).toNat := by
                rcases Nat.lt_or_ge ((18446744073709551615 : u64) / x).toNat
                  (UInt64.ofNat (x.toNat ^ (n - (1 : u32)).toNat)).toNat with h | h
                · exfalso; apply h_not_lt; exact UInt64.lt_iff_toNat_lt.mpr h
                · exact h
              rw [h_max_div_toNat, h_rest_toNat] at h_le
              exact h_le
            -- x^n < 2^64.
            have h_n_succ : n.toNat = (n - (1 : u32)).toNat + 1 := by
              rw [h_n_minus_toNat]; omega
            have h_pow_n : x.toNat ^ n.toNat = x.toNat ^ (n - (1 : u32)).toNat * x.toNat := by
              rw [h_n_succ, Nat.pow_succ]
            have h_mul_lt : x.toNat ^ (n - (1 : u32)).toNat * x.toNat < 2 ^ 64 := by
              have h_step : x.toNat ^ (n - (1 : u32)).toNat * x.toNat ≤
                            ((2 ^ 64 - 1) / x.toNat) * x.toNat :=
                Nat.mul_le_mul_right x.toNat h_le_N
              have h_div_le : ((2 ^ 64 - 1) / x.toNat) * x.toNat ≤ 2 ^ 64 - 1 := by
                have h_dm := Nat.div_add_mod (2 ^ 64 - 1) x.toNat
                have h_comm : x.toNat * ((2 ^ 64 - 1) / x.toNat) = (2 ^ 64 - 1) / x.toNat * x.toNat :=
                  Nat.mul_comm _ _
                omega
              omega
            rw [if_pos (h_pow_n ▸ h_mul_lt)]
            -- Reduce rest *? x.
            have h_mul : ((UInt64.ofNat (x.toNat ^ (n - (1 : u32)).toNat)) *? x : RustM u64) =
                         pure ((UInt64.ofNat (x.toNat ^ (n - (1 : u32)).toNat)) * x) := by
              show (rust_primitives.ops.arith.Mul.mul
                      (UInt64.ofNat (x.toNat ^ (n - (1 : u32)).toNat)) x : RustM u64) = _
              show (if BitVec.umulOverflow
                       (UInt64.ofNat (x.toNat ^ (n - (1 : u32)).toNat)).toBitVec x.toBitVec then
                      (.fail .integerOverflow : RustM u64)
                    else pure (_)) = _
              have h_no_ovf : BitVec.umulOverflow
                  (UInt64.ofNat (x.toNat ^ (n - (1 : u32)).toNat)).toBitVec x.toBitVec = false := by
                cases h_eq : BitVec.umulOverflow
                    (UInt64.ofNat (x.toNat ^ (n - (1 : u32)).toNat)).toBitVec x.toBitVec with
                | false => rfl
                | true =>
                  exfalso
                  have : UInt64.mulOverflow
                      (UInt64.ofNat (x.toNat ^ (n - (1 : u32)).toNat)) x = true := h_eq
                  rw [UInt64.mulOverflow_iff, h_rest_toNat] at this
                  omega
              rw [h_no_ovf]; rfl
            rw [h_mul]
            simp only [pure_bind]
            -- Goal: pure (Some (rest * x)) = RustM.ok (Some (UInt64.ofNat (x^n)))
            -- Reduce pure on both sides via rfl, then show the inner equal via toNat_inj.
            apply congrArg (RustM.ok ∘ core_models.option.Option.Some)
            apply UInt64.toNat_inj.mp
            rw [UInt64.toNat_mul_of_lt (by rw [h_rest_toNat]; exact h_mul_lt),
                h_rest_toNat]
            have h_pow_lt : x.toNat ^ n.toNat < 2 ^ 64 := by rw [h_pow_n]; exact h_mul_lt
            rw [UInt64.toNat_ofNat_of_lt' h_pow_lt]
            rw [h_pow_n]
      · rw [if_neg h_rec_ovf]
        -- IH says result is None, so the match returns None.
        simp only
        -- Need: x^n ≥ 2^64 (since x^(n-1) ≥ 2^64, x^n ≥ x^(n-1) * 1 ≥ 2^64 for x ≥ 1)
        -- Actually if x=0 and n=1+: x^n=0, but x^(n-1) = 0 too which is < 2^64. So this case
        -- requires x ≥ 1.
        -- For x = 0: x^(n-1) = 0 < 2^64, so h_rec_ovf would be false, contradiction.
        have h_x_pos : x.toNat ≥ 1 := by
          rcases Nat.eq_zero_or_pos x.toNat with h | h
          · exfalso; apply h_rec_ovf
            rw [h]
            rcases Nat.eq_zero_or_pos (n - (1 : u32)).toNat with h2 | h2
            · rw [h2, Nat.pow_zero]; decide
            · rw [Nat.zero_pow h2]; decide
          · exact h
        have h_n_rec_ge : x.toNat ^ (n - (1 : u32)).toNat ≥ 2 ^ 64 := Nat.le_of_not_lt h_rec_ovf
        have h_n_succ : n.toNat = (n - (1 : u32)).toNat + 1 := by
          rw [h_n_minus_toNat]; omega
        have h_pow_n_ge : x.toNat ^ n.toNat ≥ 2 ^ 64 := by
          rw [h_n_succ, Nat.pow_succ]
          have h_mul_ge : x.toNat ^ (n - (1 : u32)).toNat * x.toNat ≥
                          x.toNat ^ (n - (1 : u32)).toNat * 1 :=
            Nat.mul_le_mul_left _ h_x_pos
          have h_one : x.toNat ^ (n - (1 : u32)).toNat * 1 = x.toNat ^ (n - (1 : u32)).toNat :=
            Nat.mul_one _
          omega
        rw [if_neg (Nat.not_lt.mpr h_pow_n_ge)]
        rfl

/-- Spec of `nth_root_step` under the Newton-arm preconditions
    (4 ≤ n < 64, x ≥ 2, x ≤ 2^31). Returns the Newton step value. -/
private theorem nth_root_step_correct
    (a : u64) (n1 n : u32) (x : u64)
    (h_n_eq : n.toNat = n1.toNat + 1)
    (h_n_le : n.toNat ≤ 63)
    (h_n1_ge : 3 ≤ n1.toNat)
    (h_x_ge : 2 ≤ x.toNat)
    (h_x_le : x.toNat ≤ 2 ^ 31) :
    ∃ s : u64, nth_root_u64.nth_root_step a n1 n x = RustM.ok s ∧
      s.toNat = (((if x.toNat ^ n1.toNat < 2 ^ 64 then a.toNat / x.toNat ^ n1.toNat else 0)
                  + x.toNat * n1.toNat) / n.toNat) := by
  unfold nth_root_u64.nth_root_step
  -- Helpful constants.
  have h_x_pos : 0 < x.toNat := by omega
  have h_a_lt : a.toNat < 2 ^ 64 := a.toNat_lt
  have h_n1_le : n1.toNat ≤ 62 := by omega
  have h_n_pos : 0 < n.toNat := by omega
  have h_n_ne_zero : n ≠ 0 := by
    intro h_n_zero
    have h_n_toNat_zero : n.toNat = 0 := by rw [h_n_zero]; rfl
    omega
  -- Step 1: reduce pow_u64_opt.
  rw [pow_u64_opt_spec x n1]
  simp only [RustM_ok_bind]
  -- Now we have an if-then-else on x^n1 < 2^64. Both branches: compute y.
  by_cases h_ovf : x.toNat ^ n1.toNat < 2 ^ 64
  · rw [if_pos h_ovf]
    -- Match Some (UInt64.ofNat (x^n1)).
    simp only
    -- ax = UInt64.ofNat (x^n1)
    have h_ax_toNat : (UInt64.ofNat (x.toNat ^ n1.toNat)).toNat = x.toNat ^ n1.toNat :=
      UInt64.toNat_ofNat_of_lt' h_ovf
    -- Reduce ax ==? 0.
    have h_ax_pos : 0 < x.toNat ^ n1.toNat := Nat.pow_pos h_x_pos
    have h_ax_ne_zero : (UInt64.ofNat (x.toNat ^ n1.toNat)) ≠ 0 := by
      intro h_eq
      have h_eq_toNat : (UInt64.ofNat (x.toNat ^ n1.toNat)).toNat = 0 := by rw [h_eq]; rfl
      rw [h_ax_toNat] at h_eq_toNat
      omega
    have h_eq_eqq : ((UInt64.ofNat (x.toNat ^ n1.toNat)) ==? (0 : u64) : RustM Bool) =
                    pure (decide ((UInt64.ofNat (x.toNat ^ n1.toNat)) = 0)) := rfl
    rw [h_eq_eqq]
    simp only [pure_bind]
    rw [decide_eq_false h_ax_ne_zero]
    simp only [Bool.false_eq_true, if_false]
    -- Compute a /? ax.
    have h_div : (a /? (UInt64.ofNat (x.toNat ^ n1.toNat)) : RustM u64) =
                 pure (a / (UInt64.ofNat (x.toNat ^ n1.toNat))) := by
      show (rust_primitives.ops.arith.Div.div a (UInt64.ofNat (x.toNat ^ n1.toNat)) : RustM u64) = _
      show (if (UInt64.ofNat (x.toNat ^ n1.toNat)) = 0 then (.fail .divisionByZero : RustM u64) else _) = _
      rw [if_neg h_ax_ne_zero]
    rw [h_div]
    simp only [pure_bind]
    have h_y_toNat : (a / (UInt64.ofNat (x.toNat ^ n1.toNat))).toNat =
                      a.toNat / x.toNat ^ n1.toNat := by
      rw [UInt64.toNat_div, h_ax_toNat]
    -- Now compute x *? n1.toUInt64.
    have h_n1_cast : (rust_primitives.hax.cast_op n1 : RustM u64) = pure n1.toUInt64 := rfl
    rw [h_n1_cast]
    simp only [pure_bind]
    have h_n1_u64_toNat : n1.toUInt64.toNat = n1.toNat :=
      UInt32.toNat_toUInt64 n1
    -- x *? n1.toUInt64.
    have h_x_n1 : x.toNat * n1.toNat ≤ 2 ^ 37 := by
      have h_le : x.toNat * n1.toNat ≤ 2 ^ 31 * 62 := Nat.mul_le_mul h_x_le h_n1_le
      have h_c : (2 : Nat) ^ 31 * 62 ≤ 2 ^ 37 := by decide
      omega
    have h_mul_no_ovf : (x *? n1.toUInt64 : RustM u64) = pure (x * n1.toUInt64) := by
      show (rust_primitives.ops.arith.Mul.mul x n1.toUInt64 : RustM u64) = pure (x * n1.toUInt64)
      show (if BitVec.umulOverflow x.toBitVec n1.toUInt64.toBitVec then
              (.fail .integerOverflow : RustM u64)
            else pure (x * n1.toUInt64)) = _
      have h_no_ovf : BitVec.umulOverflow x.toBitVec n1.toUInt64.toBitVec = false := by
        cases h_eq : BitVec.umulOverflow x.toBitVec n1.toUInt64.toBitVec with
        | false => rfl
        | true =>
          exfalso
          have : UInt64.mulOverflow x n1.toUInt64 = true := h_eq
          rw [UInt64.mulOverflow_iff, h_n1_u64_toNat] at this
          have h_c : (2 : Nat) ^ 37 < 2 ^ 64 := by decide
          omega
      rw [h_no_ovf]; rfl
    rw [h_mul_no_ovf]
    simp only [pure_bind]
    have h_xn1_toNat : (x * n1.toUInt64).toNat = x.toNat * n1.toNat := by
      rw [UInt64.toNat_mul_of_lt]
      · rw [h_n1_u64_toNat]
      rw [h_n1_u64_toNat]
      have h_c : (2 : Nat) ^ 37 < 2 ^ 64 := by decide
      omega
    -- y +? (x * n1.toUInt64).
    have h_y_le : (a / (UInt64.ofNat (x.toNat ^ n1.toNat))).toNat ≤ 2 ^ 63 := by
      rw [h_y_toNat]
      have h_x_n1_ge_2 : 2 ≤ x.toNat ^ n1.toNat := by
        have h_2_pow : (2 : Nat) ^ n1.toNat ≤ x.toNat ^ n1.toNat :=
          Nat.pow_le_pow_left h_x_ge _
        have h_2_n1_ge : (2 : Nat) ^ n1.toNat ≥ 2 := by
          have h_2_1 : (2 : Nat) ^ 1 ≤ 2 ^ n1.toNat :=
            Nat.pow_le_pow_right (by decide) (by omega)
          have : (2 : Nat) ^ 1 = 2 := by decide
          omega
        omega
      have h_div_le : a.toNat / x.toNat ^ n1.toNat ≤ a.toNat / 2 := Nat.div_le_div_left h_x_n1_ge_2 (by omega)
      have h_a_half : a.toNat / 2 ≤ (2 ^ 64 - 1) / 2 := Nat.div_le_div_right (by omega)
      have h_c : (2 ^ 64 - 1 : Nat) / 2 = 2 ^ 63 - 1 := by decide
      omega
    have h_add_no_ovf : ((a / (UInt64.ofNat (x.toNat ^ n1.toNat))) +? (x * n1.toUInt64) : RustM u64) =
                       pure ((a / (UInt64.ofNat (x.toNat ^ n1.toNat))) + (x * n1.toUInt64)) := by
      show (rust_primitives.ops.arith.Add.add
              (a / (UInt64.ofNat (x.toNat ^ n1.toNat))) (x * n1.toUInt64) : RustM u64) = _
      show (if BitVec.uaddOverflow (a / (UInt64.ofNat (x.toNat ^ n1.toNat))).toBitVec
              (x * n1.toUInt64).toBitVec then
              (.fail .integerOverflow : RustM u64)
            else pure (_)) = _
      have h_no_ovf : BitVec.uaddOverflow (a / (UInt64.ofNat (x.toNat ^ n1.toNat))).toBitVec
                        (x * n1.toUInt64).toBitVec = false := by
        cases h_eq : BitVec.uaddOverflow (a / (UInt64.ofNat (x.toNat ^ n1.toNat))).toBitVec
                       (x * n1.toUInt64).toBitVec with
        | false => rfl
        | true =>
          exfalso
          have : UInt64.addOverflow (a / (UInt64.ofNat (x.toNat ^ n1.toNat))) (x * n1.toUInt64) = true := h_eq
          rw [UInt64.addOverflow_iff, h_xn1_toNat] at this
          have h_c : (2 : Nat) ^ 63 + 2 ^ 37 < 2 ^ 64 := by decide
          omega
      rw [h_no_ovf]; rfl
    rw [h_add_no_ovf]
    simp only [pure_bind]
    have h_sum_toNat : ((a / (UInt64.ofNat (x.toNat ^ n1.toNat))) + (x * n1.toUInt64)).toNat =
                       a.toNat / x.toNat ^ n1.toNat + x.toNat * n1.toNat := by
      rw [UInt64.toNat_add_of_lt]
      · rw [h_y_toNat, h_xn1_toNat]
      rw [h_y_toNat, h_xn1_toNat]
      have h_c : (2 : Nat) ^ 63 + 2 ^ 37 < 2 ^ 64 := by decide
      omega
    -- /? (cast_op n : u64)
    have h_n_cast : (rust_primitives.hax.cast_op n : RustM u64) = pure n.toUInt64 := rfl
    rw [h_n_cast]
    simp only [pure_bind]
    have h_n_u64_toNat : n.toUInt64.toNat = n.toNat :=
      UInt32.toNat_toUInt64 n
    have h_n_u64_ne_zero : n.toUInt64 ≠ 0 := by
      intro h_eq
      have h_t : n.toUInt64.toNat = 0 := by rw [h_eq]; rfl
      rw [h_n_u64_toNat] at h_t
      omega
    have h_div_n : ((a / (UInt64.ofNat (x.toNat ^ n1.toNat))) + (x * n1.toUInt64)) /? n.toUInt64 =
                   pure (((a / (UInt64.ofNat (x.toNat ^ n1.toNat))) + (x * n1.toUInt64)) / n.toUInt64) := by
      show (rust_primitives.ops.arith.Div.div
              ((a / (UInt64.ofNat (x.toNat ^ n1.toNat))) + (x * n1.toUInt64))
              n.toUInt64 : RustM u64) = _
      show (if n.toUInt64 = 0 then (.fail .divisionByZero : RustM u64) else _) = _
      rw [if_neg h_n_u64_ne_zero]
    rw [h_div_n]
    -- Now we have the result.
    refine ⟨_, rfl, ?_⟩
    rw [UInt64.toNat_div, h_sum_toNat, h_n_u64_toNat]
    rw [if_pos h_ovf]
  · -- Overflow case: pow_u64_opt returns None, y = 0.
    rw [if_neg h_ovf]
    simp only
    -- y = 0.
    have h_n1_cast : (rust_primitives.hax.cast_op n1 : RustM u64) = pure n1.toUInt64 := rfl
    rw [h_n1_cast]
    simp only [pure_bind]
    have h_n1_u64_toNat : n1.toUInt64.toNat = n1.toNat :=
      UInt32.toNat_toUInt64 n1
    have h_x_n1 : x.toNat * n1.toNat ≤ 2 ^ 37 := by
      have h_le : x.toNat * n1.toNat ≤ 2 ^ 31 * 62 := Nat.mul_le_mul h_x_le h_n1_le
      have h_c : (2 : Nat) ^ 31 * 62 ≤ 2 ^ 37 := by decide
      omega
    have h_mul_no_ovf : (x *? n1.toUInt64 : RustM u64) = pure (x * n1.toUInt64) := by
      show (rust_primitives.ops.arith.Mul.mul x n1.toUInt64 : RustM u64) = pure (x * n1.toUInt64)
      show (if BitVec.umulOverflow x.toBitVec n1.toUInt64.toBitVec then
              (.fail .integerOverflow : RustM u64)
            else pure (x * n1.toUInt64)) = _
      have h_no_ovf : BitVec.umulOverflow x.toBitVec n1.toUInt64.toBitVec = false := by
        cases h_eq : BitVec.umulOverflow x.toBitVec n1.toUInt64.toBitVec with
        | false => rfl
        | true =>
          exfalso
          have : UInt64.mulOverflow x n1.toUInt64 = true := h_eq
          rw [UInt64.mulOverflow_iff, h_n1_u64_toNat] at this
          have h_c : (2 : Nat) ^ 37 < 2 ^ 64 := by decide
          omega
      rw [h_no_ovf]; rfl
    rw [h_mul_no_ovf]
    simp only [pure_bind]
    have h_xn1_toNat : (x * n1.toUInt64).toNat = x.toNat * n1.toNat := by
      rw [UInt64.toNat_mul_of_lt]
      · rw [h_n1_u64_toNat]
      rw [h_n1_u64_toNat]
      have h_c : (2 : Nat) ^ 37 < 2 ^ 64 := by decide
      omega
    have h_add_no_ovf : ((0 : u64) +? (x * n1.toUInt64) : RustM u64) =
                       pure ((0 : u64) + (x * n1.toUInt64)) := by
      show (rust_primitives.ops.arith.Add.add (0 : u64) (x * n1.toUInt64) : RustM u64) = _
      show (if BitVec.uaddOverflow (0 : u64).toBitVec (x * n1.toUInt64).toBitVec then
              (.fail .integerOverflow : RustM u64)
            else pure (_)) = _
      have h_no_ovf : BitVec.uaddOverflow (0 : u64).toBitVec (x * n1.toUInt64).toBitVec = false := by
        cases h_eq : BitVec.uaddOverflow (0 : u64).toBitVec (x * n1.toUInt64).toBitVec with
        | false => rfl
        | true =>
          exfalso
          have : UInt64.addOverflow (0 : u64) (x * n1.toUInt64) = true := h_eq
          rw [UInt64.addOverflow_iff, h_xn1_toNat] at this
          have h_zero : (0 : UInt64).toNat = 0 := rfl
          rw [h_zero] at this
          have h_c : (2 : Nat) ^ 37 < 2 ^ 64 := by decide
          omega
      rw [h_no_ovf]; rfl
    rw [h_add_no_ovf]
    simp only [pure_bind]
    have h_sum_toNat : ((0 : u64) + (x * n1.toUInt64)).toNat = x.toNat * n1.toNat := by
      rw [UInt64.toNat_add_of_lt]
      · rw [show (0 : u64).toNat = 0 from rfl, h_xn1_toNat]; omega
      rw [show (0 : u64).toNat = 0 from rfl, h_xn1_toNat]
      have h_c : (2 : Nat) ^ 37 < 2 ^ 64 := by decide
      omega
    have h_n_cast : (rust_primitives.hax.cast_op n : RustM u64) = pure n.toUInt64 := rfl
    rw [h_n_cast]
    simp only [pure_bind]
    have h_n_u64_toNat : n.toUInt64.toNat = n.toNat :=
      UInt32.toNat_toUInt64 n
    have h_n_u64_ne_zero : n.toUInt64 ≠ 0 := by
      intro h_eq
      have h_t : n.toUInt64.toNat = 0 := by rw [h_eq]; rfl
      rw [h_n_u64_toNat] at h_t
      omega
    have h_div_n : ((0 : u64) + (x * n1.toUInt64)) /? n.toUInt64 =
                   pure (((0 : u64) + (x * n1.toUInt64)) / n.toUInt64) := by
      show (rust_primitives.ops.arith.Div.div ((0 : u64) + (x * n1.toUInt64)) n.toUInt64 : RustM u64) = _
      show (if n.toUInt64 = 0 then (.fail .divisionByZero : RustM u64) else _) = _
      rw [if_neg h_n_u64_ne_zero]
    rw [h_div_n]
    refine ⟨_, rfl, ?_⟩
    rw [UInt64.toNat_div, h_sum_toNat, h_n_u64_toNat]
    rw [if_neg h_ovf, Nat.zero_add]

/-- Newton step bound: given the initial-guess invariant `a ≤ 2 * g^n`
    and the bracket `g ≤ x ≤ 2*g`, the Newton step from `x` stays
    bounded by `2*g`. Used by `nth_root_loop_up_spec` to preserve its
    strong-induction invariant across the recursive call. -/
private theorem nat_newton_step_le_2g
    (a g x n1 : Nat)
    (h_g_pos : 1 ≤ g)
    (h_g_inv : a ≤ 2 * g ^ (n1 + 1))
    (h_x_ge_g : g ≤ x)
    (h_x_le_2g : x ≤ 2 * g) :
    ((if x ^ n1 < 2 ^ 64 then a / x ^ n1 else 0) + x * n1) / (n1 + 1) ≤ 2 * g := by
  have h_n_pos : 0 < n1 + 1 := by omega
  have h_g_pow_pos : 0 < g ^ n1 := Nat.pow_pos h_g_pos
  have h_g_pow_le_x_pow : g ^ n1 ≤ x ^ n1 := Nat.pow_le_pow_left h_x_ge_g _
  -- Reshape `h_g_inv : a ≤ 2 * g^(n1+1)` into `a ≤ 2*g * g^n1`.
  have h_g_inv' : a ≤ 2 * g * g ^ n1 := by
    have h_pow_succ : g ^ (n1 + 1) = g ^ n1 * g := Nat.pow_succ g n1
    have h_eq : 2 * g ^ (n1 + 1) = 2 * g * g ^ n1 := by
      rw [h_pow_succ, Nat.mul_comm (g ^ n1) g, ← Nat.mul_assoc]
    omega
  by_cases h_ovf : x ^ n1 < 2 ^ 64
  · rw [if_pos h_ovf]
    -- a / x^n1 ≤ a / g^n1 (dividing by larger).
    have h_div_mono : a / x ^ n1 ≤ a / g ^ n1 :=
      Nat.div_le_div_left h_g_pow_le_x_pow h_g_pow_pos
    -- a / g^n1 ≤ 2*g (from `a ≤ 2*g * g^n1` and cancellation).
    have h_div_le : a / g ^ n1 ≤ 2 * g := by
      have h_le : a / g ^ n1 ≤ (2 * g * g ^ n1) / g ^ n1 :=
        Nat.div_le_div_right h_g_inv'
      have h_cancel : (2 * g * g ^ n1) / g ^ n1 = 2 * g :=
        Nat.mul_div_cancel (2 * g) h_g_pow_pos
      omega
    -- x*n1 ≤ 2*g*n1.
    have h_x_n1_le : x * n1 ≤ 2 * g * n1 := Nat.mul_le_mul_right n1 h_x_le_2g
    -- Sum ≤ 2*g + 2*g*n1 = 2*g*(n1+1).
    have h_a_x_le : a / x ^ n1 ≤ 2 * g := Nat.le_trans h_div_mono h_div_le
    have h_sum_le : a / x ^ n1 + x * n1 ≤ 2 * g * (n1 + 1) := by
      have h_factor : 2 * g * (n1 + 1) = 2 * g * n1 + 2 * g := by
        rw [Nat.mul_add, Nat.mul_one]
      omega
    -- Divide by (n1+1) and cancel.
    have h_div : (a / x ^ n1 + x * n1) / (n1 + 1) ≤ (2 * g * (n1 + 1)) / (n1 + 1) :=
      Nat.div_le_div_right h_sum_le
    have h_cancel2 : (2 * g * (n1 + 1)) / (n1 + 1) = 2 * g :=
      Nat.mul_div_cancel (2 * g) h_n_pos
    omega
  · rw [if_neg h_ovf, Nat.zero_add]
    -- x*n1 ≤ x*(n1+1), so x*n1/(n1+1) ≤ x*(n1+1)/(n1+1) = x ≤ 2*g.
    have h_le : x * n1 ≤ x * (n1 + 1) := Nat.mul_le_mul_left x (by omega)
    have h_div_le : x * n1 / (n1 + 1) ≤ x * (n1 + 1) / (n1 + 1) :=
      Nat.div_le_div_right h_le
    have h_cancel : x * (n1 + 1) / (n1 + 1) = x :=
      Nat.mul_div_cancel x h_n_pos
    omega

/-- `nth_root_loop_up` convergence spec. Used by `nth_root_postcondition`
    to close the Newton arm. -/
private theorem nth_root_loop_up_spec
    (a : u64) (n1 n : u32) (x xn g : u64)
    (h_n_eq : n.toNat = n1.toNat + 1)
    (h_n_le : n.toNat ≤ 63)
    (h_n1_ge : 3 ≤ n1.toNat)
    (h_a_ge_2n : a.toNat ≥ 2 ^ n.toNat)
    (h_g_ge_2 : 2 ≤ g.toNat)
    (h_g_le_2_16 : g.toNat ≤ 2 ^ 16)
    (h_g_inv : a.toNat ≤ 2 * g.toNat ^ n.toNat)
    (h_x_ge_g : g.toNat ≤ x.toNat)
    (h_x_le_2g : x.toNat ≤ 2 * g.toNat)
    (h_xn_eq : xn.toNat = (((if x.toNat ^ n1.toNat < 2 ^ 64
                             then a.toNat / x.toNat ^ n1.toNat else 0)
                            + x.toNat * n1.toNat) / n.toNat)) :
    ∃ x' xn' : u64, nth_root_u64.nth_root_loop_up a n1 n x xn
        = RustM.ok (rust_primitives.hax.Tuple2.mk x' xn') ∧
      xn'.toNat ≤ x'.toNat ∧
      g.toNat ≤ x'.toNat ∧
      x'.toNat ≤ 2 * g.toNat ∧
      a.toNat < (x'.toNat + 1) ^ n.toNat ∧
      xn'.toNat = (((if x'.toNat ^ n1.toNat < 2 ^ 64
                     then a.toNat / x'.toNat ^ n1.toNat else 0)
                    + x'.toNat * n1.toNat) / n.toNat) := by
  -- Strong induction on (2^32 - x.toNat). x grows in the recursive
  -- branch (x < xn = new_x), so the measure decreases.
  -- The `g`-bracket invariant `g ≤ x ≤ 2g` is preserved across the recursion
  -- via `nat_newton_step_le_2g`, which gives `xn ≤ 2g` from `g ≤ x ≤ 2g` and
  -- the initial-guess invariant `a ≤ 2·g^n`.
  induction hk : (2 ^ 32 - x.toNat) using Nat.strongRecOn generalizing x xn with
  | _ k ih =>
    subst hk
    unfold nth_root_u64.nth_root_loop_up
    have h_lt_eqq : (x <? xn : RustM Bool) = pure (decide (x < xn)) := rfl
    rw [h_lt_eqq]
    simp only [pure_bind]
    -- Useful derived facts (`x ≥ 2`, `x ≤ 2^31`) from the g-bracket.
    have h_g_pos : 1 ≤ g.toNat := by omega
    have h_x_ge : 2 ≤ x.toNat := by omega
    have h_x_le_31 : x.toNat ≤ 2 ^ 31 := by
      have h_c : 2 * (2 : Nat) ^ 16 ≤ 2 ^ 31 := by decide
      have h_2g : 2 * g.toNat ≤ 2 * 2 ^ 16 := Nat.mul_le_mul_left 2 h_g_le_2_16
      omega
    by_cases h_lt : x < xn
    · -- Recursive branch: x < xn, recurse with (xn, step(a, xn)).
      simp only [decide_eq_true h_lt, if_true]
      have h_x_lt_xn : x.toNat < xn.toNat := UInt64.lt_iff_toNat_lt.mp h_lt
      -- Invariant: a < (xn + 1)^n from step_ub_preserved.
      have h_a_lt : a.toNat < 2 ^ 64 := a.toNat_lt
      have h_n1_ge_1 : 1 ≤ n1.toNat := by omega
      have h_x_pos : 1 ≤ x.toNat := by omega
      have h_xn_ub : a.toNat < (xn.toNat + 1) ^ n.toNat := by
        have h_lb := nat_nth_root_step_ub_preserved a.toNat x.toNat n1.toNat h_a_lt h_x_pos h_n1_ge_1
        rw [← h_n_eq] at h_lb
        rw [← h_xn_eq] at h_lb
        exact h_lb
      -- xn ≥ 2 from a ≥ 2^n and a < (xn+1)^n.
      have h_xn_ge : 2 ≤ xn.toNat := by
        rcases Nat.lt_or_ge xn.toNat 2 with h | h
        · exfalso
          have h_xn_p1_le : xn.toNat + 1 ≤ 2 := by omega
          have h_pow_le : (xn.toNat + 1) ^ n.toNat ≤ 2 ^ n.toNat :=
            Nat.pow_le_pow_left h_xn_p1_le _
          omega
        · exact h
      -- KEY: xn ≤ 2*g via nat_newton_step_le_2g.
      have h_g_inv_n1 : a.toNat ≤ 2 * g.toNat ^ (n1.toNat + 1) := by
        rw [← h_n_eq]; exact h_g_inv
      have h_xn_le_2g : xn.toNat ≤ 2 * g.toNat := by
        rw [h_xn_eq, h_n_eq]
        exact nat_newton_step_le_2g a.toNat g.toNat x.toNat n1.toNat
          h_g_pos h_g_inv_n1 h_x_ge_g h_x_le_2g
      -- xn ≥ g (from g ≤ x < xn).
      have h_xn_ge_g : g.toNat ≤ xn.toNat := by omega
      -- xn ≤ 2^31 (needed by nth_root_step_correct).
      have h_xn_le_31 : xn.toNat ≤ 2 ^ 31 := by
        have h_c : 2 * (2 : Nat) ^ 16 ≤ 2 ^ 31 := by decide
        have h_2g : 2 * g.toNat ≤ 2 * 2 ^ 16 := Nat.mul_le_mul_left 2 h_g_le_2_16
        omega
      -- Compute new_xn = step(a, xn) via nth_root_step_correct.
      obtain ⟨new_xn, h_step_eq, h_new_xn_toNat⟩ :=
        nth_root_step_correct a n1 n xn h_n_eq h_n_le h_n1_ge h_xn_ge h_xn_le_31
      rw [h_step_eq]
      simp only [RustM_ok_bind]
      -- IH on (xn, new_xn). Measure: (2^32 - xn.toNat) < (2^32 - x.toNat).
      have h_meas : 2 ^ 32 - xn.toNat < 2 ^ 32 - x.toNat := by
        have h_xn_lt_pow : xn.toNat < 2 ^ 32 := by
          have h_c : (2 : Nat) ^ 31 < 2 ^ 32 := by decide
          omega
        omega
      exact ih (2 ^ 32 - xn.toNat) h_meas xn new_xn h_xn_ge_g h_xn_le_2g h_new_xn_toNat rfl
    · -- Exit branch: x ≥ xn, return (x, xn).
      simp only [decide_eq_false h_lt, Bool.false_eq_true, if_false]
      have h_xn_le_x : xn.toNat ≤ x.toNat := by
        have h_not : ¬ x.toNat < xn.toNat := fun h => h_lt (UInt64.lt_iff_toNat_lt.mpr h)
        omega
      refine ⟨x, xn, rfl, h_xn_le_x, h_x_ge_g, h_x_le_2g, ?_, h_xn_eq⟩
      -- a < (x+1)^n via step_ub_preserved + transferring (xn+1)^n ≤ (x+1)^n.
      have h_a_lt : a.toNat < 2 ^ 64 := a.toNat_lt
      have h_n1_ge_1 : 1 ≤ n1.toNat := by omega
      have h_x_pos : 1 ≤ x.toNat := by omega
      have h_lb := nat_nth_root_step_ub_preserved a.toNat x.toNat n1.toNat h_a_lt h_x_pos h_n1_ge_1
      rw [← h_n_eq] at h_lb
      rw [← h_xn_eq] at h_lb
      have h_pow_le : (xn.toNat + 1) ^ n.toNat ≤ (x.toNat + 1) ^ n.toNat :=
        Nat.pow_le_pow_left (by omega) _
      omega

/-- `nth_root_loop_up` exits immediately when `xn ≤ x` (overestimate
    starting condition), returning `(x, xn)`. -/
private theorem nth_root_loop_up_overest_exits
    (a : u64) (n1 n : u32) (x xn : u64) (h_xn_le_x : xn.toNat ≤ x.toNat) :
    nth_root_u64.nth_root_loop_up a n1 n x xn
      = RustM.ok (rust_primitives.hax.Tuple2.mk x xn) := by
  unfold nth_root_u64.nth_root_loop_up
  have h_lt_eqq : (x <? xn : RustM Bool) = pure (decide (x < xn)) := rfl
  rw [h_lt_eqq]
  simp only [pure_bind]
  have h_not_lt : ¬ x < xn := fun h => by
    have h_lt_N : x.toNat < xn.toNat := UInt64.lt_iff_toNat_lt.mp h
    omega
  rw [decide_eq_false h_not_lt]
  simp only [Bool.false_eq_true, if_false]
  rfl

/-- `nth_root_loop_down` convergence spec under Newton-arm preconditions.
    Requires `a ≥ 2^n` so the loop iterates stay ≥ 2. -/
private theorem nth_root_loop_down_spec
    (a : u64) (n1 n : u32) (x xn : u64)
    (h_n_eq : n.toNat = n1.toNat + 1)
    (h_n_le : n.toNat ≤ 63)
    (h_n1_ge : 3 ≤ n1.toNat)
    (h_a_ge_2n : a.toNat ≥ 2 ^ n.toNat)
    (h_x_le : x.toNat ≤ 2 ^ 31)
    (h_x_ub : a.toNat < (x.toNat + 1) ^ n.toNat)
    (h_xn_eq : xn.toNat = (((if x.toNat ^ n1.toNat < 2 ^ 64
                             then a.toNat / x.toNat ^ n1.toNat else 0)
                            + x.toNat * n1.toNat) / n.toNat)) :
    ∃ r : u64, nth_root_u64.nth_root_loop_down a n1 n x xn = RustM.ok r ∧
      r.toNat ^ n.toNat ≤ a.toNat ∧
      a.toNat < (r.toNat + 1) ^ n.toNat := by
  -- Derive x ≥ 2 from a ≥ 2^n and a < (x+1)^n.
  have h_x_ge_aux : ∀ (x' : Nat), a.toNat < (x' + 1) ^ n.toNat → 2 ≤ x' := by
    intro x' h_lt
    rcases Nat.lt_or_ge x' 2 with h | h
    · exfalso
      have h_x_eq : x' + 1 ≤ 2 := by omega
      have h_pow_le : (x' + 1) ^ n.toNat ≤ 2 ^ n.toNat :=
        Nat.pow_le_pow_left h_x_eq _
      omega
    · exact h
  have h_x_ge : 2 ≤ x.toNat := h_x_ge_aux x.toNat h_x_ub
  induction hk : x.toNat using Nat.strongRecOn generalizing x xn with
  | _ k ih =>
    subst hk
    unfold nth_root_u64.nth_root_loop_down
    have h_gt_eqq : (x >? xn : RustM Bool) = pure (decide (x > xn)) := rfl
    rw [h_gt_eqq]
    simp only [pure_bind]
    by_cases h_gt : x > xn
    · simp only [decide_eq_true h_gt, if_true]
      have h_xn_lt_x : xn.toNat < x.toNat := UInt64.lt_iff_toNat_lt.mp h_gt
      have h_a_lt : a.toNat < 2 ^ 64 := a.toNat_lt
      have h_xn_le : xn.toNat ≤ 2 ^ 31 := by omega
      have h_xn_ub : a.toNat < (xn.toNat + 1) ^ n.toNat := by
        have h_n1_ge_1 : 1 ≤ n1.toNat := by omega
        have h_x_pos : 1 ≤ x.toNat := by omega
        have h_lb := nat_nth_root_step_ub_preserved a.toNat x.toNat n1.toNat h_a_lt h_x_pos h_n1_ge_1
        rw [← h_n_eq] at h_lb
        rw [← h_xn_eq] at h_lb
        exact h_lb
      have h_xn_ge : 2 ≤ xn.toNat := h_x_ge_aux xn.toNat h_xn_ub
      -- Apply nth_root_step_correct to compute next xn.
      obtain ⟨new_xn, h_step_eq, h_new_xn_toNat⟩ :=
        nth_root_step_correct a n1 n xn h_n_eq h_n_le h_n1_ge h_xn_ge h_xn_le
      rw [h_step_eq]
      simp only [RustM_ok_bind]
      -- Apply IH on (xn, new_xn). The IH preconditions are (in order):
      -- h_x_le, h_x_ub, h_xn_eq, h_x_ge, hk : x.toNat = m
      exact ih xn.toNat h_xn_lt_x xn new_xn h_xn_le h_xn_ub h_new_xn_toNat h_xn_ge rfl
    · simp only [decide_eq_false h_gt, Bool.false_eq_true, if_false]
      refine ⟨x, rfl, ?_, h_x_ub⟩
      have h_not_gt : ¬ x > xn := h_gt
      have h_x_le_xn : x.toNat ≤ xn.toNat :=
        Nat.le_of_not_lt (fun h => h_not_gt (UInt64.lt_iff_toNat_lt.mpr h))
      have h_x_le_step : x.toNat ≤ (((if x.toNat ^ n1.toNat < 2 ^ 64
                                       then a.toNat / x.toNat ^ n1.toNat else 0)
                                      + x.toNat * n1.toNat) / n.toNat) := by
        rw [← h_xn_eq]; exact h_x_le_xn
      have h_n1_ge_1 : 1 ≤ n1.toNat := by omega
      have h_x_pos : 1 ≤ x.toNat := by omega
      have h_a_lt : a.toNat < 2 ^ 64 := a.toNat_lt
      have h_lb := nat_nth_root_step_exit_implies_lb a.toNat x.toNat n1.toNat h_x_pos h_n1_ge_1 h_a_lt
        (by rw [h_n_eq] at h_x_le_step; exact h_x_le_step)
      rw [← h_n_eq] at h_lb
      exact h_lb

/-- `nth_root_guess` partial spec: returns `g = 2^k` for
    `k = (log2 a + n - 1) / n ∈ [1, 16]`, so `2 ≤ g ≤ 2^16`.
    Does NOT claim `g^n ≥ a` (which is false in general — for
    `a = 17, n = 4`, `g = 2` and `g^4 = 16 < 17`). The full
    Newton-arm proof would instead need `nth_root_loop_up_spec`
    to handle the underestimate case, which I have not developed. -/
private theorem nth_root_guess_spec
    (a : u64) (n : u32) (h_a_ge_2n : a.toNat ≥ 2 ^ n.toNat)
    (h_n_ge : 4 ≤ n.toNat) (h_n_lt : n.toNat < 64) :
    ∃ g : u64, nth_root_u64.nth_root_guess a n = RustM.ok g ∧
      2 ≤ g.toNat ∧
      g.toNat ≤ 2 ^ 16 ∧
      a.toNat ≤ 2 * g.toNat ^ n.toNat := by
  unfold nth_root_u64.nth_root_guess
  have h_a_pos : 0 < a.toNat := by
    have h_pow_pos : 0 < (2 : Nat) ^ n.toNat := Nat.pow_pos (by decide)
    omega
  have h_a_lt : a.toNat < 2 ^ 64 := a.toNat_lt
  have h_log2_le : Nat.log2 a.toNat ≤ 63 := nat_log2_le_63 a.toNat h_a_pos h_a_lt
  -- log2 a ≥ n (since a ≥ 2^n).
  have h_log2_ge : Nat.log2 a.toNat ≥ n.toNat := by
    rcases Nat.lt_or_ge (Nat.log2 a.toNat) n.toNat with h | h
    · exfalso
      have h_a_lt_pow_succ : a.toNat < 2 ^ (Nat.log2 a.toNat + 1) :=
        nat_lt_pow_succ_log2 a.toNat h_a_pos
      have h_pow_le : 2 ^ (Nat.log2 a.toNat + 1) ≤ 2 ^ n.toNat :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · exact h
  -- Reduce log2_u64.
  have h_log2_u64_eq : nth_root_u64.log2_u64 a = RustM.ok (UInt32.ofNat (Nat.log2 a.toNat)) := by
    show nth_root_u64.log2_rec a (0 : UInt32) = _
    have h := log2_rec_correct a (0 : UInt32) (by
      show (0 : UInt32).toNat + Nat.log2 a.toNat < 2 ^ 32
      have h0 : (0 : UInt32).toNat = 0 := rfl
      rw [h0]; omega)
    rw [h]
    have h0 : (0 : UInt32).toNat = 0 := rfl
    rw [h0, Nat.zero_add]
  rw [h_log2_u64_eq]
  simp only [RustM_ok_bind]
  have h_log2_toNat : (UInt32.ofNat (Nat.log2 a.toNat)).toNat = Nat.log2 a.toNat :=
    UInt32.toNat_ofNat_of_lt' (by omega : Nat.log2 a.toNat < 2 ^ 32)
  -- (log2 a) +? n.
  have h_add_n : ((UInt32.ofNat (Nat.log2 a.toNat)) +? n : RustM u32) =
                 pure (UInt32.ofNat (Nat.log2 a.toNat) + n) := by
    show (rust_primitives.ops.arith.Add.add (UInt32.ofNat (Nat.log2 a.toNat)) n : RustM u32) = _
    show (if BitVec.uaddOverflow (UInt32.ofNat (Nat.log2 a.toNat)).toBitVec n.toBitVec then
            (.fail .integerOverflow : RustM u32) else _) = _
    have h_no_ovf : BitVec.uaddOverflow (UInt32.ofNat (Nat.log2 a.toNat)).toBitVec n.toBitVec = false := by
      cases h_eq : BitVec.uaddOverflow (UInt32.ofNat (Nat.log2 a.toNat)).toBitVec n.toBitVec with
      | false => rfl
      | true =>
        exfalso
        have : UInt32.addOverflow (UInt32.ofNat (Nat.log2 a.toNat)) n = true := h_eq
        rw [UInt32.addOverflow_iff, h_log2_toNat] at this
        omega
    rw [h_no_ovf]; rfl
  rw [h_add_n]
  simp only [pure_bind]
  have h_log2_n_toNat : (UInt32.ofNat (Nat.log2 a.toNat) + n).toNat =
                         Nat.log2 a.toNat + n.toNat := by
    rw [UInt32.toNat_add_of_lt]
    · rw [h_log2_toNat]
    rw [h_log2_toNat]; omega
  -- (log2 a + n) -? 1.
  have h_sub_1 : ((UInt32.ofNat (Nat.log2 a.toNat) + n) -? (1 : u32) : RustM u32) =
                 pure ((UInt32.ofNat (Nat.log2 a.toNat) + n) - 1) := by
    show (rust_primitives.ops.arith.Sub.sub (UInt32.ofNat (Nat.log2 a.toNat) + n) (1 : u32) : RustM u32) = _
    show (if BitVec.usubOverflow (UInt32.ofNat (Nat.log2 a.toNat) + n).toBitVec (1 : u32).toBitVec then
            (.fail .integerOverflow : RustM u32) else _) = _
    have h_no_ovf : BitVec.usubOverflow (UInt32.ofNat (Nat.log2 a.toNat) + n).toBitVec ((1 : u32).toBitVec) = false := by
      cases h_eq : BitVec.usubOverflow (UInt32.ofNat (Nat.log2 a.toNat) + n).toBitVec ((1 : u32).toBitVec) with
      | false => rfl
      | true =>
        exfalso
        have : UInt32.subOverflow (UInt32.ofNat (Nat.log2 a.toNat) + n) (1 : u32) = true := h_eq
        rw [UInt32.subOverflow_iff, h_log2_n_toNat] at this
        have h_one : (1 : UInt32).toNat = 1 := rfl
        rw [h_one] at this
        omega
    rw [h_no_ovf]; rfl
  rw [h_sub_1]
  simp only [pure_bind]
  have h_log2_n_minus_toNat : ((UInt32.ofNat (Nat.log2 a.toNat) + n) - 1).toNat =
                               Nat.log2 a.toNat + n.toNat - 1 := by
    rw [UInt32.toNat_sub_of_le' (by
      show ((1 : u32)).toNat ≤ (UInt32.ofNat (Nat.log2 a.toNat) + n).toNat
      have h_one : (1 : UInt32).toNat = 1 := rfl
      rw [h_one, h_log2_n_toNat]; omega)]
    rw [h_log2_n_toNat]; rfl
  -- /? n.
  have h_n_ne_zero : n ≠ 0 := by
    intro h_eq
    have h : n.toNat = 0 := by rw [h_eq]; rfl
    omega
  have h_div_n : (((UInt32.ofNat (Nat.log2 a.toNat) + n) - 1) /? n : RustM u32) =
                 pure (((UInt32.ofNat (Nat.log2 a.toNat) + n) - 1) / n) := by
    show (rust_primitives.ops.arith.Div.div ((UInt32.ofNat (Nat.log2 a.toNat) + n) - 1) n : RustM u32) = _
    show (if n = 0 then (.fail .divisionByZero : RustM u32) else _) = _
    rw [if_neg h_n_ne_zero]
  rw [h_div_n]
  simp only [pure_bind]
  have h_k_toNat : (((UInt32.ofNat (Nat.log2 a.toNat) + n) - 1) / n).toNat =
                    (Nat.log2 a.toNat + n.toNat - 1) / n.toNat := by
    rw [UInt32.toNat_div, h_log2_n_minus_toNat]
  -- k = (log2 a + n - 1) / n.
  -- For our case: 1 ≤ k ≤ (62 + n)/n = 62/n + 1 ≤ 16.
  have h_k_lower : 1 ≤ (Nat.log2 a.toNat + n.toNat - 1) / n.toNat := by
    have h_ge_n : n.toNat ≤ Nat.log2 a.toNat + n.toNat - 1 := by omega
    have h_div : n.toNat / n.toNat ≤ (Nat.log2 a.toNat + n.toNat - 1) / n.toNat :=
      Nat.div_le_div_right h_ge_n
    have h_self : n.toNat / n.toNat = 1 := Nat.div_self (by omega)
    omega
  have h_k_upper : (Nat.log2 a.toNat + n.toNat - 1) / n.toNat ≤ 16 := by
    have h_le : Nat.log2 a.toNat + n.toNat - 1 ≤ 63 + n.toNat - 1 := by omega
    -- For n ≥ 4: (63 + n - 1) / n = (62 + n) / n = (62 + n) / n.
    -- We want ≤ 16. For n = 4: (62 + 4)/4 = 66/4 = 16. ✓
    -- For n = 5: 67/5 = 13. For n ≥ 4: 62/n ≤ 15, so total ≤ 16.
    have h_n_ge_4 : n.toNat ≥ 4 := h_n_ge
    rcases Nat.lt_or_ge n.toNat 65 with _ | _
    · -- n < 65 (always true since n < 64).
      -- The maximum value of (Nat.log2 a.toNat + n.toNat - 1) / n.toNat occurs at log2 a = 63 (max).
      -- (63 + n - 1) / n = (62 + n) / n
      -- For n = 4: 66/4 = 16 (max)
      -- For n = 5: 67/5 = 13
      -- For n ≥ 5: ≤ 13 ≤ 16
      -- So we need to bound this.
      have h_num_le : Nat.log2 a.toNat + n.toNat - 1 ≤ 62 + n.toNat := by omega
      have h_div_le : (Nat.log2 a.toNat + n.toNat - 1) / n.toNat ≤ (62 + n.toNat) / n.toNat :=
        Nat.div_le_div_right h_num_le
      -- (62 + n) / n = 62/n + 1 (since n | n)
      have h_split : (62 + n.toNat) / n.toNat = 62 / n.toNat + 1 := by
        rw [show 62 + n.toNat = 62 + 1 * n.toNat from by rw [Nat.one_mul],
            Nat.add_mul_div_right _ _ (by omega : 0 < n.toNat)]
      rw [h_split] at h_div_le
      have h_62_n_le : 62 / n.toNat ≤ 15 := by
        have h_div : (62 : Nat) / n.toNat ≤ 62 / 4 := Nat.div_le_div_left h_n_ge_4 (by omega)
        have h_c : (62 : Nat) / 4 = 15 := by decide
        omega
      omega
    · -- n ≥ 65, impossible.
      omega
  have h_k_le_63 : (((UInt32.ofNat (Nat.log2 a.toNat) + n) - 1) / n).toNat ≤ 63 := by
    rw [h_k_toNat]; omega
  have h_0_le_k : ((0 : u32)).toNat ≤ (((UInt32.ofNat (Nat.log2 a.toNat) + n) - 1) / n).toNat := by
    have h_0 : ((0 : u32)).toNat = 0 := rfl
    rw [h_0]; omega
  have h_no_ovf : (1 : u64).toNat * 2 ^ ((((UInt32.ofNat (Nat.log2 a.toNat) + n) - 1) / n).toNat - (0 : u32).toNat) < 2 ^ 64 := by
    have h_0 : ((0 : u32)).toNat = 0 := rfl
    have h_1 : ((1 : u64)).toNat = 1 := rfl
    rw [h_1, h_0, h_k_toNat, Nat.sub_zero, Nat.one_mul]
    have h_pow_le : (2 : Nat) ^ ((Nat.log2 a.toNat + n.toNat - 1) / n.toNat) ≤ 2 ^ 16 :=
      Nat.pow_le_pow_right (by decide) h_k_upper
    have h_2_16 : (2 : Nat) ^ 16 < 2 ^ 64 := by decide
    omega
  obtain ⟨g, hg_eq, hg_toNat⟩ :=
    pow2_loop_correct (((UInt32.ofNat (Nat.log2 a.toNat) + n) - 1) / n) (0 : u32) (1 : u64)
      h_0_le_k h_k_le_63 h_no_ovf
  rw [hg_eq]
  have h_g_eq : g.toNat = 2 ^ ((Nat.log2 a.toNat + n.toNat - 1) / n.toNat) := by
    have h_0 : ((0 : u32)).toNat = 0 := rfl
    have h_1 : ((1 : u64)).toNat = 1 := rfl
    rw [hg_toNat, h_1, h_0, h_k_toNat, Nat.sub_zero, Nat.one_mul]
  refine ⟨g, rfl, ?_, ?_, ?_⟩
  · rw [h_g_eq]
    have h_pow_ge : (2 : Nat) ^ 1 ≤ 2 ^ ((Nat.log2 a.toNat + n.toNat - 1) / n.toNat) :=
      Nat.pow_le_pow_right (by decide) h_k_lower
    have : (2 : Nat) ^ 1 = 2 := by decide
    omega
  · rw [h_g_eq]; exact Nat.pow_le_pow_right (by decide) h_k_upper
  · -- a ≤ 2 * g^n, the initial-guess invariant.
    -- g = 2^k where k = (log2 a + n - 1) / n. So g^n = 2^(k*n).
    -- k*n ≥ log2 a (from Nat.div_add_mod and Nat.mod_lt).
    -- Then 2 * 2^(k*n) ≥ 2 * 2^(log2 a) = 2^(log2 a + 1) > a.
    rw [h_g_eq]
    have h_pow_mul : (2 ^ ((Nat.log2 a.toNat + n.toNat - 1) / n.toNat)) ^ n.toNat =
                      2 ^ (((Nat.log2 a.toNat + n.toNat - 1) / n.toNat) * n.toNat) := by
      rw [← Nat.pow_mul]
    rw [h_pow_mul]
    have h_kn_ge : ((Nat.log2 a.toNat + n.toNat - 1) / n.toNat) * n.toNat ≥ Nat.log2 a.toNat := by
      have h_div_mod := Nat.div_add_mod (Nat.log2 a.toNat + n.toNat - 1) n.toNat
      have h_mod_lt : (Nat.log2 a.toNat + n.toNat - 1) % n.toNat < n.toNat :=
        Nat.mod_lt _ (by omega)
      have h_comm : n.toNat * ((Nat.log2 a.toNat + n.toNat - 1) / n.toNat) =
                     ((Nat.log2 a.toNat + n.toNat - 1) / n.toNat) * n.toNat := Nat.mul_comm _ _
      omega
    have h_pow_le : (2 : Nat) ^ Nat.log2 a.toNat ≤
                     2 ^ (((Nat.log2 a.toNat + n.toNat - 1) / n.toNat) * n.toNat) :=
      Nat.pow_le_pow_right (by decide) h_kn_ge
    have h_a_lt_pow : a.toNat < 2 ^ (Nat.log2 a.toNat + 1) :=
      nat_lt_pow_succ_log2 a.toNat h_a_pos
    have h_pow_succ_eq : 2 ^ (Nat.log2 a.toNat + 1) = 2 * 2 ^ Nat.log2 a.toNat := by
      rw [Nat.pow_succ, Nat.mul_comm]
    omega
/-- Master existential for `nth_root` (precondition `n ≥ 1`):
    returns some `r` simultaneously satisfying the lower and
    upper `n`-th-root bounds.

    ADMISSION (first-person): I tried to close this proof and could
    not. The `n = 1, 2, 3` early-return arms and the `n ≥ 64` /
    `a < 2^n` fast paths are fully proved here. The Newton arm
    (`n ∈ [4, 63]` with `a ≥ 2^n`) reduces, via `nth_root_guess_spec`
    + `nth_root_step_correct` + `nth_root_loop_up_spec` +
    `nth_root_loop_down_spec`, to the private helper
    `nth_root_loop_up_spec`, which carries a `sorry` for the bound
    `xn.toNat ≤ 2^31` on the loop_up iterate. See that helper's
    docstring for the detailed first-person admission, the three
    approaches I attempted, and the structural unblock
    (`nat_newton_nth_root_iter_bounded`) that would close it. -/
theorem nth_root_postcondition (self_val : u64) (n : u32) (hn : 1 ≤ n.toNat) :
    ∃ r : u64, nth_root_u64.nth_root self_val n = RustM.ok r ∧
      r.toNat ^ n.toNat ≤ self_val.toNat ∧
      self_val.toNat < (r.toNat + 1) ^ n.toNat := by
  unfold nth_root_u64.nth_root
  dsimp only
  rw [show (n ==? (1 : u32) : RustM Bool) = pure (decide (n = 1)) from rfl]
  simp only [pure_bind]
  by_cases h_n1 : n = 1
  · -- Case n = 1.
    rw [decide_eq_true h_n1]
    simp only [if_true]
    have h_n_toNat : n.toNat = 1 := by rw [h_n1]; rfl
    refine ⟨self_val, rfl, ?_, ?_⟩
    · rw [h_n_toNat, Nat.pow_one]; omega
    · rw [h_n_toNat, Nat.pow_one]; omega
  · rw [decide_eq_false h_n1]
    simp only [Bool.false_eq_true, if_false]
    rw [show (n ==? (2 : u32) : RustM Bool) = pure (decide (n = 2)) from rfl]
    simp only [pure_bind]
    by_cases h_n2 : n = 2
    · -- Case n = 2: use sqrt_u64_postcondition.
      rw [decide_eq_true h_n2]
      simp only [if_true]
      have h_n_toNat : n.toNat = 2 := by rw [h_n2]; rfl
      obtain ⟨r, hr_eq, hlb, hub⟩ := sqrt_u64_postcondition self_val
      refine ⟨r, hr_eq, ?_, ?_⟩
      · rw [h_n_toNat]
        show r.toNat ^ 2 ≤ self_val.toNat
        rw [show r.toNat ^ 2 = r.toNat * r.toNat from by
          rw [show (2 : Nat) = 1 + 1 from rfl, Nat.pow_succ, Nat.pow_one]]
        exact hlb
      · rw [h_n_toNat]
        show self_val.toNat < (r.toNat + 1) ^ 2
        rw [show (r.toNat + 1) ^ 2 = (r.toNat + 1) * (r.toNat + 1) from by
          rw [show (2 : Nat) = 1 + 1 from rfl, Nat.pow_succ, Nat.pow_one]]
        exact hub
    · rw [decide_eq_false h_n2]
      simp only [Bool.false_eq_true, if_false]
      rw [show (n ==? (3 : u32) : RustM Bool) = pure (decide (n = 3)) from rfl]
      simp only [pure_bind]
      by_cases h_n3 : n = 3
      · -- Case n = 3: use cbrt_u64_postcondition.
        rw [decide_eq_true h_n3]
        simp only [if_true]
        have h_n_toNat : n.toNat = 3 := by rw [h_n3]; rfl
        obtain ⟨r, hr_eq, hlb, hub⟩ := cbrt_u64_postcondition self_val
        refine ⟨r, hr_eq, ?_, ?_⟩
        · rw [h_n_toNat]
          show r.toNat ^ 3 ≤ self_val.toNat
          rw [show r.toNat ^ 3 = r.toNat * r.toNat * r.toNat from by
            rw [show (3 : Nat) = 1 + 1 + 1 from rfl, Nat.pow_succ, Nat.pow_succ, Nat.pow_one]]
          exact hlb
        · rw [h_n_toNat]
          show self_val.toNat < (r.toNat + 1) ^ 3
          rw [show (r.toNat + 1) ^ 3 = (r.toNat + 1) * (r.toNat + 1) * (r.toNat + 1) from by
            rw [show (3 : Nat) = 1 + 1 + 1 from rfl, Nat.pow_succ, Nat.pow_succ, Nat.pow_one]]
          exact hub
      · -- n ∉ {1, 2, 3}. Compute n - 1.
        rw [decide_eq_false h_n3]
        simp only [Bool.false_eq_true, if_false]
        -- For n ≥ 1 and n ≠ 1, 2, 3, we have n ≥ 4.
        have h_n_ge_4 : n.toNat ≥ 4 := by
          have h_n_ne_1 : n.toNat ≠ 1 := fun h => h_n1 (UInt32.toNat_inj.mp (by rw [h]; rfl))
          have h_n_ne_2 : n.toNat ≠ 2 := fun h => h_n2 (UInt32.toNat_inj.mp (by rw [h]; rfl))
          have h_n_ne_3 : n.toNat ≠ 3 := fun h => h_n3 (UInt32.toNat_inj.mp (by rw [h]; rfl))
          omega
        -- n - 1 reduces without overflow.
        have h_n_lt : n.toNat < 2 ^ 32 := n.toNat_lt
        have h_sub_n1 : (n -? (1 : u32) : RustM u32) = pure (n - 1) := by
          show (rust_primitives.ops.arith.Sub.sub n (1 : u32) : RustM u32) = pure (n - 1)
          show (if BitVec.usubOverflow n.toBitVec (1 : u32).toBitVec then
                  (.fail .integerOverflow : RustM u32)
                else pure (n - 1)) = _
          have h_no_ovf : BitVec.usubOverflow n.toBitVec ((1 : u32).toBitVec) = false := by
            cases h_eq : BitVec.usubOverflow n.toBitVec ((1 : u32).toBitVec) with
            | false => rfl
            | true =>
              exfalso
              have : UInt32.subOverflow n (1 : u32) = true := h_eq
              rw [UInt32.subOverflow_iff] at this
              have h1 : (1 : UInt32).toNat = 1 := rfl
              rw [h1] at this
              omega
          rw [h_no_ovf]; rfl
        rw [h_sub_n1]
        simp only [pure_bind]
        -- Now n >=? 64.
        rw [show (n >=? (64 : u32) : RustM Bool) = pure (decide (n ≥ 64)) from rfl]
        simp only [pure_bind]
        by_cases h_n_ge_64 : n ≥ 64
        · -- Case n ≥ 64. Fast path: a > 0 → 1, else 0.
          rw [decide_eq_true h_n_ge_64]
          simp only [if_true]
          rw [show (self_val >? (0 : u64) : RustM Bool) = pure (decide (self_val > 0)) from rfl]
          simp only [pure_bind]
          have h_n_toNat_ge : n.toNat ≥ 64 := UInt32.le_iff_toNat_le.mp h_n_ge_64
          have h_a_lt : self_val.toNat < 2 ^ 64 := self_val.toNat_lt
          by_cases h_pos : self_val > 0
          · rw [decide_eq_true h_pos]
            simp only [if_true]
            have h_a_pos : 0 < self_val.toNat := UInt64.lt_iff_toNat_lt.mp h_pos
            refine ⟨1, rfl, ?_, ?_⟩
            · -- 1^n.toNat = 1 ≤ self_val.toNat
              rw [show (1 : u64).toNat = 1 from rfl, Nat.one_pow]; omega
            · -- self_val.toNat < 2^n.toNat
              rw [show (1 : u64).toNat + 1 = 2 from rfl]
              have h_pow_ge : (2 : Nat) ^ 64 ≤ 2 ^ n.toNat :=
                Nat.pow_le_pow_right (by decide) h_n_toNat_ge
              omega
          · rw [decide_eq_false h_pos]
            simp only [Bool.false_eq_true, if_false]
            have h_a_zero : self_val.toNat = 0 := by
              have h_not_pos : ¬ (0 < self_val.toNat) := fun h => h_pos (UInt64.lt_iff_toNat_lt.mpr h)
              omega
            refine ⟨0, rfl, ?_, ?_⟩
            · rw [show (0 : u64).toNat = 0 from rfl, h_a_zero, Nat.zero_pow (by omega : 0 < n.toNat)]
              omega
            · rw [show (0 : u64).toNat + 1 = 1 from rfl, Nat.one_pow, h_a_zero]
              omega
        · -- n < 64.
          rw [decide_eq_false h_n_ge_64]
          simp only [Bool.false_eq_true, if_false]
          have h_n_lt_64 : n.toNat < 64 := by
            have h_not : ¬ n.toNat ≥ 64 := fun h => h_n_ge_64 (UInt32.le_iff_toNat_le.mpr h)
            omega
          -- Reduce (1 : u64) <<<? n. Since n < 64, this is 2^n.
          have h_shl_1 : ((1 : u64) <<<? n : RustM u64) = pure ((1 : UInt64) <<< n.toNat.toUInt64) := by
            show (rust_primitives.ops.bit.Shl.shl (1 : u64) n : RustM u64) =
                 pure ((1 : UInt64) <<< n.toNat.toUInt64)
            show (if (decide ((0 : UInt32) ≤ n) && decide (n < (64 : UInt32))) = true then
                    pure ((1 : UInt64) <<< n.toNat.toUInt64)
                  else RustM.fail Error.integerOverflow) = pure ((1 : UInt64) <<< n.toNat.toUInt64)
            have h_0_le : (0 : UInt32) ≤ n := by
              rw [UInt32.le_iff_toNat_le]; exact Nat.zero_le _
            have h_lt_64 : n < (64 : UInt32) := by
              rw [UInt32.lt_iff_toNat_lt]
              show n.toNat < (64 : UInt32).toNat
              have : (64 : UInt32).toNat = 64 := rfl
              rw [this]; exact h_n_lt_64
            rw [show (decide ((0 : UInt32) ≤ n) && decide (n < (64 : UInt32))) = true from by
              rw [decide_eq_true h_0_le, decide_eq_true h_lt_64]; rfl]
            simp only [if_true]
          rw [h_shl_1]
          simp only [pure_bind]
          have h_shl_val : ((1 : UInt64) <<< n.toNat.toUInt64).toNat = 2 ^ n.toNat := by
            rw [UInt64.toNat_shiftLeft]
            show UInt64.toNat 1 <<< (n.toNat.toUInt64.toNat % 64) % 2 ^ 64 = 2 ^ n.toNat
            have h1 : UInt64.toNat 1 = 1 := rfl
            have h_n_toUInt64 : n.toNat.toUInt64.toNat = n.toNat := by
              show UInt64.toNat (UInt64.ofNat n.toNat) = n.toNat
              exact UInt64.toNat_ofNat_of_lt' (by omega : n.toNat < 2 ^ 64)
            have h_mod : n.toNat.toUInt64.toNat % 64 = n.toNat := by
              rw [h_n_toUInt64]; exact Nat.mod_eq_of_lt h_n_lt_64
            rw [h1, h_mod, Nat.shiftLeft_eq, Nat.one_mul]
            have h_pow_lt : 2 ^ n.toNat < 2 ^ 64 :=
              Nat.pow_lt_pow_right (by decide : 1 < 2) h_n_lt_64
            exact Nat.mod_eq_of_lt h_pow_lt
          -- self_val <? (2^n)
          rw [show (self_val <? ((1 : UInt64) <<< n.toNat.toUInt64) : RustM Bool) =
                pure (decide (self_val < ((1 : UInt64) <<< n.toNat.toUInt64))) from rfl]
          simp only [pure_bind]
          by_cases h_a_lt_pow : self_val < ((1 : UInt64) <<< n.toNat.toUInt64)
          · -- Case a < 2^n.
            rw [decide_eq_true h_a_lt_pow]
            simp only [if_true]
            rw [show (self_val >? (0 : u64) : RustM Bool) = pure (decide (self_val > 0)) from rfl]
            simp only [pure_bind]
            have h_a_lt_2n : self_val.toNat < 2 ^ n.toNat := by
              have h := UInt64.lt_iff_toNat_lt.mp h_a_lt_pow
              rw [h_shl_val] at h
              exact h
            by_cases h_pos : self_val > 0
            · rw [decide_eq_true h_pos]
              simp only [if_true]
              have h_a_pos : 0 < self_val.toNat := UInt64.lt_iff_toNat_lt.mp h_pos
              refine ⟨1, rfl, ?_, ?_⟩
              · rw [show (1 : u64).toNat = 1 from rfl, Nat.one_pow]; omega
              · rw [show (1 : u64).toNat + 1 = 2 from rfl]; exact h_a_lt_2n
            · rw [decide_eq_false h_pos]
              simp only [Bool.false_eq_true, if_false]
              have h_a_zero : self_val.toNat = 0 := by
                have h_not_pos : ¬ (0 < self_val.toNat) := fun h => h_pos (UInt64.lt_iff_toNat_lt.mpr h)
                omega
              refine ⟨0, rfl, ?_, ?_⟩
              · rw [show (0 : u64).toNat = 0 from rfl, h_a_zero,
                    Nat.zero_pow (by omega : 0 < n.toNat)]
                omega
              · rw [show (0 : u64).toNat + 1 = 1 from rfl, Nat.one_pow, h_a_zero]
                omega
          · -- Newton iteration case: 4 ≤ n < 64 and self_val ≥ 2^n.
            -- Dispatch the outer if (we're in the ¬ a < 2^n branch).
            rw [decide_eq_false h_a_lt_pow]
            simp only [Bool.false_eq_true, if_false]
            have h_a_ge_2n : self_val.toNat ≥ 2 ^ n.toNat := by
              rcases Nat.lt_or_ge self_val.toNat (2 ^ n.toNat) with h | h
              · exfalso
                apply h_a_lt_pow
                exact UInt64.lt_iff_toNat_lt.mpr (by rw [h_shl_val]; exact h)
              · exact h
            have h_n_ge_4' : 4 ≤ n.toNat := h_n_ge_4
            have h_n_lt_64' : n.toNat < 64 := h_n_lt_64
            -- Apply nth_root_guess_spec to extract g with 2 ≤ g ≤ 2^16
            -- and the initial-guess invariant `a ≤ 2*g^n`.
            obtain ⟨g, hg_eq, hg_ge_2, hg_le_2_16, hg_inv⟩ :=
              nth_root_guess_spec self_val n h_a_ge_2n h_n_ge_4' h_n_lt_64'
            rw [hg_eq]
            simp only [RustM_ok_bind]
            -- Apply nth_root_step_correct to compute xn0.
            have h_n_eq : n.toNat = (n - 1).toNat + 1 := by
              have h_n1_toNat : (n - 1).toNat = n.toNat - 1 := by
                apply UInt32.toNat_sub_of_le'
                have h_one : (1 : UInt32).toNat = 1 := rfl
                rw [h_one]; omega
              rw [h_n1_toNat]; omega
            have h_n_le_63 : n.toNat ≤ 63 := by omega
            have h_n1_ge_3 : 3 ≤ (n - 1).toNat := by
              have h_n1_toNat : (n - 1).toNat = n.toNat - 1 := by
                apply UInt32.toNat_sub_of_le'
                have h_one : (1 : UInt32).toNat = 1 := rfl
                rw [h_one]; omega
              rw [h_n1_toNat]; omega
            have hg_le_2_31 : g.toNat ≤ 2 ^ 31 := by
              have h_c : (2 : Nat) ^ 16 ≤ 2 ^ 31 := by decide
              omega
            obtain ⟨xn0, h_step_eq, h_xn0_toNat⟩ :=
              nth_root_step_correct self_val (n - 1) n g h_n_eq h_n_le_63 h_n1_ge_3 hg_ge_2 hg_le_2_31
            rw [h_step_eq]
            simp only [RustM_ok_bind]
            -- Apply nth_root_loop_up_spec carrying the g-bracket invariant.
            -- The initial iterate is x = g, so g ≤ x ≤ 2g holds trivially.
            have h_g_le_g : g.toNat ≤ g.toNat := Nat.le_refl _
            have h_g_le_2g : g.toNat ≤ 2 * g.toNat := by omega
            obtain ⟨x1, xn1, h_up_eq, h_xn1_le_x1, h_x1_ge_g, h_x1_le_2g,
                    h_x1_ub, h_xn1_toNat⟩ :=
              nth_root_loop_up_spec self_val (n - 1) n g xn0 g h_n_eq h_n_le_63
                h_n1_ge_3 h_a_ge_2n hg_ge_2 hg_le_2_16 hg_inv h_g_le_g h_g_le_2g h_xn0_toNat
            rw [h_up_eq]
            simp only [RustM_ok_bind]
            -- Derive x1 ≤ 2^31 from x1 ≤ 2*g and g ≤ 2^16 (for nth_root_loop_down_spec).
            have h_x1_le_31 : x1.toNat ≤ 2 ^ 31 := by
              have h_c : 2 * (2 : Nat) ^ 16 ≤ 2 ^ 31 := by decide
              have h_2g_le : 2 * g.toNat ≤ 2 * 2 ^ 16 := Nat.mul_le_mul_left 2 hg_le_2_16
              omega
            -- Apply nth_root_loop_down_spec.
            exact nth_root_loop_down_spec self_val (n - 1) n x1 xn1 h_n_eq
              h_n_le_63 h_n1_ge_3 h_a_ge_2n h_x1_le_31 h_x1_ub h_xn1_toNat

/-- Totality / no-panic for `nth_root` in the valid range `n ≥ 1`.
    Outside this range the function panics; see `nth_root_zero_panics`.

    ADMISSION: this corollary projects out of `nth_root_postcondition`
    and therefore transitively depends on the `sorry` inside the
    private helper `nth_root_loop_up_spec`; see that helper for the
    first-person admission and the structural unblock. -/
theorem nth_root_total (self_val : u64) (n : u32) (hn : 1 ≤ n.toNat) :
    ∃ r : u64, nth_root_u64.nth_root self_val n = RustM.ok r := by
  obtain ⟨r, hr, _, _⟩ := nth_root_postcondition self_val n hn
  exact ⟨r, hr⟩

/-- Lower bound (independent clause) for `nth_root`: `r^n ≤ a` for any
    `n ≥ 1`. Captures `prop_nth_root_lower_bound`.

    ADMISSION: this corollary projects out of `nth_root_postcondition`
    and therefore transitively depends on the `sorry` inside the
    private helper `nth_root_loop_up_spec`; see that helper for the
    first-person admission and the structural unblock. -/
theorem nth_root_lower_bound (self_val : u64) (n : u32) (hn : 1 ≤ n.toNat) :
    ∃ r : u64, nth_root_u64.nth_root self_val n = RustM.ok r ∧
      r.toNat ^ n.toNat ≤ self_val.toNat := by
  obtain ⟨r, hr, hlb, _⟩ := nth_root_postcondition self_val n hn
  exact ⟨r, hr, hlb⟩

/-- Upper bound (independent clause) for `nth_root`: `a < (r+1)^n`,
    stated at `Nat`-level so the Rust test's vacuous overflow case
    becomes a genuine inequality. Captures `prop_nth_root_upper_bound`.
    Independent from the lower bound (an always-`0` implementation
    would pass the lower bound and fail this one).

    ADMISSION: this corollary projects out of `nth_root_postcondition`
    and therefore transitively depends on the `sorry` inside the
    private helper `nth_root_loop_up_spec`; see that helper for the
    first-person admission and the structural unblock. -/
theorem nth_root_upper_bound (self_val : u64) (n : u32) (hn : 1 ≤ n.toNat) :
    ∃ r : u64, nth_root_u64.nth_root self_val n = RustM.ok r ∧
      self_val.toNat < (r.toNat + 1) ^ n.toNat := by
  obtain ⟨r, hr, _, hub⟩ := nth_root_postcondition self_val n hn
  exact ⟨r, hr, hub⟩

/-! ## Failure condition: panic on `n = 0` -/

/-- `nth_root(a, 0)` panics for any `a` via u32 underflow in the
    `n - 1` subtraction. Hax models this as
    `RustM.fail .integerOverflow`, matching the observable effect of
    the original `panic!("…")` in `num-integer-0.1.46`. Captures the
    `#[should_panic] zeroth_root` test, which exercises this on the
    specific input `nth_root(123u64, 0)`. Stated universally because
    the panic depends only on `n = 0`, not on the value of `a`. -/
theorem nth_root_zero_panics (self_val : u64) :
    nth_root_u64.nth_root self_val 0 = RustM.fail .integerOverflow := by
  unfold nth_root_u64.nth_root
  rfl

/-! ## Boundary cases (specific values pinned by the `bit_size` test)

The `bit_size` integration test pins two specific outputs at the
extreme corner of the input domain. They are derivable from the
master postcondition plus arithmetic, but the test exists as a
spot-check and they correspond to distinct code paths (`n ≥ 64`
fast-return arm vs. Newton arm at the maximal practical `n`). -/

/-- `nth_root(u64::MAX, 63) = 2`. Captures the first assertion of the
    `bit_size` test. Exercises the Newton arm at the largest exponent
    that still triggers iteration (`n = 63 < 64`, `a ≥ (1 << 63)`). -/
theorem nth_root_max_63 :
    nth_root_u64.nth_root 18446744073709551615 63 = RustM.ok 2 := by
  native_decide

/-- `nth_root(u64::MAX, 64) = 1`. Captures the second assertion of the
    `bit_size` test. Exercises the `n ≥ 64` fast-path arm, which
    returns `1` immediately when `a > 0` without invoking the
    Newton iteration. -/
theorem nth_root_max_64 :
    nth_root_u64.nth_root 18446744073709551615 64 = RustM.ok 1 := by
  unfold nth_root_u64.nth_root
  rfl

end Nth_root_u64Obligations
