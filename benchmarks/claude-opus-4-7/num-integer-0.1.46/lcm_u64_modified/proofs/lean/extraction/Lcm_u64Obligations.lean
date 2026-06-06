-- Companion obligations file for the `lcm_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import lcm_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Lcm_u64Obligations

open rust_primitives.hax (Tuple2)

/-! ## Nat-bridge helpers -/

/-- `RustM.ok`-headed bind reduction (`RustM.ok` is `pure` for `RustM`). -/
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

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

/-! ## Nat-level Stein identities -/

private theorem nat_gcd_double_both (m n : Nat) :
    Nat.gcd (2 * m) (2 * n) = 2 * Nat.gcd m n :=
  Nat.gcd_mul_left 2 m n

private theorem odd_dvd_two_mul {d m : Nat} (hd : d % 2 = 1) (h : d ∣ 2 * m) :
    d ∣ m := by
  obtain ⟨k, hk⟩ := h
  have hk_even : k % 2 = 0 := by
    have h_zero : (2 * m) % 2 = 0 := Nat.mul_mod_right 2 m
    rw [hk, Nat.mul_mod, hd, Nat.one_mul, Nat.mod_mod] at h_zero
    exact h_zero
  obtain ⟨k', hk'⟩ : 2 ∣ k := Nat.dvd_of_mod_eq_zero hk_even
  refine ⟨k', ?_⟩
  have h1 : 2 * m = d * (2 * k') := by rw [hk, hk']
  have h2 : 2 * m = 2 * (d * k') := by
    rw [h1, ← Nat.mul_assoc, Nat.mul_comm d 2, Nat.mul_assoc]
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h2

private theorem nat_gcd_two_left_odd_right (m n : Nat) (hn : n % 2 = 1) :
    Nat.gcd (2 * m) n = Nat.gcd m n := by
  refine Nat.dvd_antisymm ?_ ?_
  · apply Nat.dvd_gcd
    · have h_dvd_2m : Nat.gcd (2 * m) n ∣ 2 * m := Nat.gcd_dvd_left _ _
      have h_dvd_n : Nat.gcd (2 * m) n ∣ n := Nat.gcd_dvd_right _ _
      have h_g_odd : Nat.gcd (2 * m) n % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one (Nat.gcd (2 * m) n) with hg | hg
        · exfalso
          have h_2_dvd_g : 2 ∣ Nat.gcd (2 * m) n := Nat.dvd_of_mod_eq_zero hg
          have h_2_dvd_n : 2 ∣ n := Nat.dvd_trans h_2_dvd_g h_dvd_n
          have h_n_mod : n % 2 = 0 := Nat.mod_eq_zero_of_dvd h_2_dvd_n
          omega
        · exact hg
      exact odd_dvd_two_mul h_g_odd h_dvd_2m
    · exact Nat.gcd_dvd_right _ _
  · apply Nat.dvd_gcd
    · exact Nat.dvd_trans (Nat.gcd_dvd_left _ _) ⟨2, by rw [Nat.mul_comm]⟩
    · exact Nat.gcd_dvd_right _ _

private theorem nat_gcd_sub_right (m n : Nat) (h : n ≤ m) :
    Nat.gcd m n = Nat.gcd (m - n) n := by
  have h_eq : Nat.gcd m n = Nat.gcd ((m - n) + n) n := by
    rw [Nat.sub_add_cancel h]
  rw [h_eq, Nat.gcd_add_self_left]

/-! ## Trailing-zeros infrastructure -/

private def tzInv (x₀ : u64) (s : Tuple2 u32 u64) : Prop :=
  x₀.toNat = s._1.toNat * 2 ^ s._0.toNat ∧ 0 < s._1.toNat ∧ s._0.toNat < 64

private def tzTerm (s : Tuple2 u32 u64) : Nat := s._1.toNat

private abbrev tzCond : Tuple2 u32 u64 → Bool :=
  fun b => UInt64.toNat (b._1 &&& 1) == UInt64.toNat 0

private abbrev tzBody : Tuple2 u32 u64 → RustM (Tuple2 u32 u64) :=
  fun x =>
    match x with
    | ⟨count, y⟩ =>
      (do
        let y : u64 ← (y >>>? (1 : i32))
        let count : u32 ← (count +? (1 : u32))
        pure (rust_primitives.hax.Tuple2.mk count y) :
        RustM (rust_primitives.hax.Tuple2 u32 u64))

private abbrev tzLoop (x : u64) : RustM (Tuple2 u32 u64) :=
  Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk tzCond
    (rust_primitives.hax.Tuple2.mk (0 : u32) x) tzBody

private theorem tz_body_step_nat (x₀ : u64) (c : u32) (y : u64)
    (hinv : tzInv x₀ ⟨c, y⟩) (hcond : tzCond ⟨c, y⟩ = true) :
    c.toNat + 1 < 2 ^ 32 ∧
    (y >>> (1 : UInt64)).toNat < y.toNat ∧
    tzInv x₀ ⟨c + 1, y >>> (1 : UInt64)⟩ := by
  unfold tzInv at hinv
  simp only at hinv
  obtain ⟨hx, hy_pos, hc_lt⟩ := hinv
  have h_y_and : (y &&& 1).toNat = 0 := by
    have hb : (UInt64.toNat (y &&& 1) == UInt64.toNat 0) = true := hcond
    have : UInt64.toNat (y &&& 1) = UInt64.toNat 0 := beq_iff_eq.mp hb
    simpa using this
  have h_y_even : y.toNat % 2 = 0 := by
    have : y.toNat &&& 1 = 0 := by
      have := h_y_and
      rw [UInt64.toNat_and] at this
      rw [UInt64.toNat_one] at this
      exact this
    rw [← Nat.and_one_is_mod]; exact this
  have h_y_ge_2 : y.toNat ≥ 2 := by omega
  refine ⟨by omega, ?_, ?_⟩
  · rw [UInt64.toNat_shiftRight, UInt64.toNat_one]
    show y.toNat >>> (1 % 64) < y.toNat
    rw [show (1 % 64 : Nat) = 1 from rfl, Nat.shiftRight_eq_div_pow,
        show (2 ^ 1 : Nat) = 2 from rfl]
    exact Nat.div_lt_self (by omega) (by decide)
  · have h_cplus : (c + (1 : u32)).toNat = c.toNat + 1 := by
      apply UInt32.toNat_add_of_lt
      have h1 : (1 : UInt32).toNat = 1 := rfl
      rw [h1]; omega
    have h_yshr : (y >>> (1 : UInt64)).toNat = y.toNat / 2 := by
      rw [UInt64.toNat_shiftRight, UInt64.toNat_one]
      show y.toNat >>> (1 % 64) = _
      rw [show (1 % 64 : Nat) = 1 from rfl, Nat.shiftRight_eq_div_pow,
          show (2 ^ 1 : Nat) = 2 from rfl]
    have h_new_y_pos : 0 < y.toNat / 2 := Nat.div_pos h_y_ge_2 (by decide)
    have h_y_div_mul : y.toNat / 2 * 2 = y.toNat := by
      have := Nat.div_add_mod y.toNat 2
      omega
    have h_x_eq : x₀.toNat = y.toNat / 2 * 2 ^ (c.toNat + 1) := by
      have key : y.toNat * 2 ^ c.toNat = y.toNat / 2 * 2 ^ (c.toNat + 1) := by
        rw [Nat.pow_succ,
            show 2 ^ c.toNat * 2 = 2 * 2 ^ c.toNat from Nat.mul_comm _ _,
            ← Nat.mul_assoc, h_y_div_mul]
      rw [← key]; exact hx
    have h_cplus_lt_64 : c.toNat + 1 < 64 := by
      have h_x_lt : x₀.toNat < 2 ^ 64 := UInt64.toNat_lt x₀
      have h_pow_le : 2 ^ (c.toNat + 1) ≤ x₀.toNat := by
        rw [h_x_eq]; exact Nat.le_mul_of_pos_left _ h_new_y_pos
      have h_pow_lt : 2 ^ (c.toNat + 1) < 2 ^ 64 :=
        Nat.lt_of_le_of_lt h_pow_le h_x_lt
      exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h_pow_lt
    refine ⟨?_, ?_, ?_⟩
    · show x₀.toNat = (y >>> (1 : UInt64)).toNat * 2 ^ (c + (1 : u32)).toNat
      rw [h_yshr, h_cplus]; exact h_x_eq
    · show 0 < (y >>> (1 : UInt64)).toNat
      rw [h_yshr]; exact h_new_y_pos
    · show (c + (1 : u32)).toNat < 64
      rw [h_cplus]; exact h_cplus_lt_64

private theorem tz_loop_triple (x₀ : u64) :
    ⦃⌜ tzInv x₀ ⟨(0 : u32), x₀⟩ ⌝⦄
      tzLoop x₀
    ⦃⇓ r => ⌜ tzInv x₀ r ∧ ¬ tzCond r = true ⌝⦄ := by
  apply Std.Do.Spec.MonoLoopCombinator.while_loop
    (rust_primitives.hax.Tuple2.mk (0 : u32) x₀) Lean.Loop.mk
    tzCond tzBody (tzInv x₀) tzTerm
  intro s hcond hinv
  cases s with
  | mk c y =>
    have hstep := tz_body_step_nat x₀ c y hinv hcond
    obtain ⟨h_no_add_ovf, h_term_dec, h_inv'⟩ := hstep
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
    have h_add : (c +? (1 : u32) : RustM u32) = pure (c + 1) := by
      show (rust_primitives.ops.arith.Add.add c (1 : u32) : RustM u32) =
           pure (c + 1)
      show (if BitVec.uaddOverflow c.toBitVec (1 : u32).toBitVec then
              (.fail .integerOverflow : RustM u32)
            else pure (c + 1)) = pure (c + 1)
      have h_no_ovf : BitVec.uaddOverflow c.toBitVec ((1 : u32).toBitVec) = false := by
        cases h_eq : BitVec.uaddOverflow c.toBitVec ((1 : u32).toBitVec) with
        | false => rfl
        | true =>
          exfalso
          have : UInt32.addOverflow c (1 : u32) = true := h_eq
          rw [UInt32.addOverflow_iff] at this
          have h1 : (1 : UInt32).toNat = 1 := rfl
          rw [h1] at this; omega
      rw [h_no_ovf]; rfl
    dsimp only [tzBody]
    rw [h_shr]
    simp only [pure_bind]
    rw [h_add]
    simp only [pure_bind]
    refine ⟨?_, h_inv'⟩
    show tzTerm ⟨c + 1, y >>> 1⟩ < tzTerm ⟨c, y⟩
    show (y >>> (1 : UInt64)).toNat < y.toNat
    exact h_term_dec

private theorem tz_function_nonzero_triple (x : u64) (hx : x ≠ 0) :
    ⦃⌜ True ⌝⦄
      lcm_u64.trailing_zeros_u64 x
    ⦃⇓ r => ⌜ r.toNat < 64 ∧ 2 ^ r.toNat ∣ x.toNat ∧
              (x.toNat >>> r.toNat) &&& 1 = 1 ⌝⦄ := by
  have h_loop := tz_loop_triple x
  have h_loop' :
      ⦃⌜ tzInv x ⟨(0 : u32), x⟩ ⌝⦄
        tzLoop x
      ⦃⇓ r => ⌜ r._0.toNat < 64 ∧ 2 ^ r._0.toNat ∣ x.toNat ∧
                (x.toNat >>> r._0.toNat) &&& 1 = 1 ⌝⦄ := by
    apply Triple.of_entails_right _ _ _ _ h_loop
    apply PostCond.entails.of_left_entails
    intro r ⟨hinv, hncond⟩
    unfold tzInv at hinv
    obtain ⟨hx_eq, hy_pos, hc_lt⟩ := hinv
    have h_y_odd : r._1.toNat % 2 = 1 := by
      have h_ne_zero : ¬ ((UInt64.toNat (r._1 &&& 1)) == UInt64.toNat 0) = true := hncond
      rw [beq_iff_eq] at h_ne_zero
      have h_neq : UInt64.toNat (r._1 &&& 1) ≠ UInt64.toNat 0 := h_ne_zero
      rw [UInt64.toNat_and, UInt64.toNat_one] at h_neq
      have h0 : (UInt64.toNat 0 : Nat) = 0 := rfl
      rw [h0] at h_neq
      rw [← Nat.and_one_is_mod]
      have h_bound : r._1.toNat &&& 1 ≤ 1 := Nat.and_le_right
      omega
    refine ⟨hc_lt, ?_, ?_⟩
    · rw [hx_eq]
      exact ⟨r._1.toNat, by rw [Nat.mul_comm]⟩
    · rw [hx_eq]
      have h_div : (r._1.toNat * 2 ^ r._0.toNat) >>> r._0.toNat = r._1.toNat := by
        rw [Nat.shiftRight_eq_div_pow]
        have hpos : 0 < 2 ^ r._0.toNat := Nat.two_pow_pos r._0.toNat
        exact Nat.mul_div_cancel _ hpos
      rw [h_div, Nat.and_one_is_mod]
      exact h_y_odd
  have h_loop'' :
      ⦃⌜ True ⌝⦄
        tzLoop x
      ⦃⇓ r => ⌜ r._0.toNat < 64 ∧ 2 ^ r._0.toNat ∣ x.toNat ∧
                (x.toNat >>> r._0.toNat) &&& 1 = 1 ⌝⦄ := by
    apply Triple.of_entails_left _ _ _ _ h_loop'
    intro _
    show tzInv x ⟨(0 : u32), x⟩
    refine ⟨?_, ?_, ?_⟩
    · show x.toNat = x.toNat * 2 ^ ((0 : u32).toNat)
      rw [show ((0 : u32).toNat) = 0 from rfl, Nat.pow_zero, Nat.mul_one]
    · show 0 < x.toNat
      rcases Nat.eq_zero_or_pos x.toNat with h | h
      · exfalso; apply hx; apply UInt64.toNat_inj.mp; rw [h]; rfl
      · exact h
    · show (0 : u32).toNat < 64; decide
  unfold lcm_u64.trailing_zeros_u64
  unfold rust_primitives.hax.while_loop
  show ⦃⌜True⌝⦄
        ((x ==? (0 : u64)) >>= fun b =>
          if b = true then pure (64 : u32)
          else (tzLoop x >>= fun __discr =>
                  match __discr with | ⟨c, _⟩ => pure c))
        ⦃⇓ r => ⌜r.toNat < 64 ∧ 2 ^ r.toNat ∣ x.toNat ∧ (x.toNat >>> r.toNat) &&& 1 = 1⌝⦄
  show ⦃⌜True⌝⦄
        ((pure (x == (0 : u64)) : RustM Bool) >>= fun b =>
          if b = true then pure (64 : u32)
          else (tzLoop x >>= fun __discr =>
                  match __discr with | ⟨c, _⟩ => pure c))
        ⦃⇓ r => ⌜r.toNat < 64 ∧ 2 ^ r.toNat ∣ x.toNat ∧ (x.toNat >>> r.toNat) &&& 1 = 1⌝⦄
  simp only [pure_bind]
  have h_eq_false : (x == (0 : u64)) = false := by
    rw [beq_eq_false_iff_ne]; exact hx
  rw [h_eq_false]
  simp only [if_false, Bool.false_eq_true]
  apply Triple.bind _ _ h_loop''
  intro s
  cases s with
  | mk c y =>
    refine Triple.pure c ?_
    intro h
    exact h

private theorem tz_nonzero_spec (x : u64) (hx : x ≠ 0) :
    ∃ r : u32, lcm_u64.trailing_zeros_u64 x = RustM.ok r ∧
                r.toNat < 64 ∧
                2 ^ r.toNat ∣ x.toNat ∧
                (x.toNat >>> r.toNat) &&& 1 = 1 := by
  have h := tz_function_nonzero_triple x hx
  rw [RustM.Triple_iff_BitVec] at h
  simp only [decide_true, Bool.not_true, Bool.false_or,
             Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hok, hpost⟩ := h
  cases hf : lcm_u64.trailing_zeros_u64 x with
  | none => rw [hf] at hok; simp [RustM.toBVRustM] at hok
  | some result =>
    cases result with
    | ok v =>
      rw [hf] at hpost
      simp only [RustM.toBVRustM] at hpost
      exact ⟨v, rfl, hpost.1, hpost.2.1, hpost.2.2⟩
    | error e =>
      rw [hf] at hok
      cases e <;> simp [RustM.toBVRustM] at hok

private theorem tz_zero :
    lcm_u64.trailing_zeros_u64 (0 : u64) = RustM.ok (64 : u32) := by
  unfold lcm_u64.trailing_zeros_u64
  rfl

private theorem nat_gcd_mul_pow_two_left_odd_right (a n : Nat) (hn : n % 2 = 1) :
    ∀ k, Nat.gcd (a * 2 ^ k) n = Nat.gcd a n
  | 0 => by rw [Nat.pow_zero, Nat.mul_one]
  | k + 1 => by
    have ih := nat_gcd_mul_pow_two_left_odd_right a n hn k
    have h_eq : a * 2 ^ (k + 1) = 2 * (a * 2 ^ k) := by
      rw [Nat.pow_succ]
      rw [← Nat.mul_assoc, Nat.mul_comm (a * 2 ^ k) 2]
    rw [h_eq, nat_gcd_two_left_odd_right _ _ hn, ih]

/-! ## Stein loop spec on odd, nonzero inputs -/

private theorem gcd_stein_loop_spec (m n : u64)
    (hm_odd : m.toNat % 2 = 1) (hn_odd : n.toNat % 2 = 1) :
    lcm_u64.gcd_stein_loop m n
      = RustM.ok (UInt64.ofNat (Nat.gcd m.toNat n.toNat)) := by
  have hm_pos : 0 < m.toNat := by omega
  have hn_pos : 0 < n.toNat := by omega
  induction hk : (m.toNat + n.toNat) using Nat.strongRecOn generalizing m n with
  | _ k ih =>
    unfold lcm_u64.gcd_stein_loop
    have h_mn_eqq : (m ==? n : RustM Bool) = pure (m == n) := rfl
    rw [h_mn_eqq]
    simp only [pure_bind]
    by_cases hmn : m = n
    · subst hmn
      have h_dec : (m == m) = true := beq_self_eq_true m
      rw [h_dec]
      simp only [if_true]
      show RustM.ok m = RustM.ok (UInt64.ofNat (Nat.gcd m.toNat m.toNat))
      congr 1
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_ofNat_of_lt' (by rw [Nat.gcd_self]; exact m.toNat_lt),
          Nat.gcd_self]
    · have h_mn_false : (m == n) = false := by
        rw [beq_eq_false_iff_ne]; exact hmn
      rw [h_mn_false]
      simp only [Bool.false_eq_true, if_false]
      have h_gt_eqq : (m >? n : RustM Bool) = pure (decide (m > n)) := rfl
      rw [h_gt_eqq]
      simp only [pure_bind]
      by_cases hgt : m > n
      · rw [decide_eq_true hgt]
        simp only [if_true]
        have hnm : n.toNat < m.toNat := UInt64.lt_iff_toNat_lt.mp hgt
        have h_sub : (m -? n : RustM u64) = pure (m - n) := by
          have h_no_underflow : UInt64.subOverflow m n = false := by
            generalize hbo : UInt64.subOverflow m n = bo
            cases bo with
            | false => rfl
            | true => exfalso; rw [UInt64.subOverflow_iff] at hbo; omega
          show (rust_primitives.ops.arith.Sub.sub m n : RustM u64) = pure (m - n)
          show (if BitVec.usubOverflow m.toBitVec n.toBitVec then
                  (.fail .integerOverflow : RustM u64) else pure (m - n)) = pure (m - n)
          rw [show BitVec.usubOverflow m.toBitVec n.toBitVec = false from h_no_underflow]
          rfl
        rw [h_sub]
        simp only [pure_bind]
        have hd_toNat : (m - n).toNat = m.toNat - n.toNat :=
          UInt64.toNat_sub_of_le' (Nat.le_of_lt hnm)
        have hd_ne : (m - n) ≠ 0 := by
          intro h
          have hz : (m - n).toNat = 0 := by rw [h]; rfl
          omega
        obtain ⟨r, h_tz, hr_lt, hr_dvd, hr_bit⟩ := tz_nonzero_spec (m - n) hd_ne
        rw [h_tz]
        simp only [RustM_ok_bind]
        have hr_lt_2_64 : r.toNat < 2 ^ 64 := by
          have h32 : r.toNat < 2 ^ 32 := UInt32.toNat_lt r
          omega
        have hr_uint64_toNat : (r.toNat.toUInt64).toNat = r.toNat :=
          UInt64.toNat_ofNat_of_lt' hr_lt_2_64
        have h_0_le : (0 : UInt32) ≤ r := by
          rw [UInt32.le_iff_toNat_le]
          show (0 : UInt32).toNat ≤ r.toNat
          have h0 : (0 : UInt32).toNat = 0 := rfl
          omega
        have h_lt_64 : r < (64 : UInt32) := by
          rw [UInt32.lt_iff_toNat_lt]
          show r.toNat < (64 : UInt32).toNat
          have h64 : (64 : UInt32).toNat = 64 := rfl
          omega
        have h_shr : ((m - n) >>>? r : RustM u64)
            = RustM.ok ((m - n) >>> r.toNat.toUInt64) := by
          show (rust_primitives.ops.bit.Shr.shr (m - n) r : RustM u64)
              = RustM.ok ((m - n) >>> r.toNat.toUInt64)
          show (if ((0 : UInt32) ≤ r && r < (64 : UInt32)) then
                  pure ((m - n) >>> r.toNat.toUInt64)
                else .fail .integerOverflow) = RustM.ok ((m - n) >>> r.toNat.toUInt64)
          have h_cond_eq : ((0 : UInt32) ≤ r && r < (64 : UInt32)) = true := by
            simp [h_0_le, h_lt_64]
          rw [h_cond_eq]; rfl
        rw [h_shr]
        simp only [RustM_ok_bind]
        have h_m'_toNat : ((m - n) >>> r.toNat.toUInt64).toNat
            = (m - n).toNat >>> r.toNat := by
          rw [UInt64.toNat_shiftRight, hr_uint64_toNat, Nat.mod_eq_of_lt hr_lt]
        have h_m'_div : ((m - n) >>> r.toNat.toUInt64).toNat
            = (m - n).toNat / 2 ^ r.toNat := by
          rw [h_m'_toNat, Nat.shiftRight_eq_div_pow]
        have h_m'_mul : ((m - n) >>> r.toNat.toUInt64).toNat * 2 ^ r.toNat
            = (m - n).toNat := by
          rw [h_m'_div]; exact Nat.div_mul_cancel hr_dvd
        have h_m'_odd : ((m - n) >>> r.toNat.toUInt64).toNat % 2 = 1 := by
          rw [h_m'_toNat, ← Nat.and_one_is_mod]; exact hr_bit
        have h_m'_pos : 0 < ((m - n) >>> r.toNat.toUInt64).toNat := by omega
        have h_meas : ((m - n) >>> r.toNat.toUInt64).toNat + n.toNat < k := by
          have h_le : ((m - n) >>> r.toNat.toUInt64).toNat ≤ (m - n).toNat := by
            rw [h_m'_div]; exact Nat.div_le_self _ _
          omega
        rw [ih (((m - n) >>> r.toNat.toUInt64).toNat + n.toNat) h_meas
              ((m - n) >>> r.toNat.toUInt64) n h_m'_odd hn_odd h_m'_pos hn_pos rfl]
        apply congrArg RustM.ok
        apply congrArg UInt64.ofNat
        rw [nat_gcd_sub_right m.toNat n.toNat (Nat.le_of_lt hnm), ← hd_toNat,
            ← h_m'_mul, nat_gcd_mul_pow_two_left_odd_right _ _ hn_odd]
      · rw [decide_eq_false hgt]
        simp only [Bool.false_eq_true, if_false]
        have hnm : m.toNat < n.toNat := by
          rcases Nat.lt_trichotomy m.toNat n.toNat with h | h | h
          · exact h
          · exfalso; exact hmn (UInt64.toNat_inj.mp h)
          · exfalso; exact hgt (UInt64.lt_iff_toNat_lt.mpr h)
        have h_sub : (n -? m : RustM u64) = pure (n - m) := by
          have h_no_underflow : UInt64.subOverflow n m = false := by
            generalize hbo : UInt64.subOverflow n m = bo
            cases bo with
            | false => rfl
            | true => exfalso; rw [UInt64.subOverflow_iff] at hbo; omega
          show (rust_primitives.ops.arith.Sub.sub n m : RustM u64) = pure (n - m)
          show (if BitVec.usubOverflow n.toBitVec m.toBitVec then
                  (.fail .integerOverflow : RustM u64) else pure (n - m)) = pure (n - m)
          rw [show BitVec.usubOverflow n.toBitVec m.toBitVec = false from h_no_underflow]
          rfl
        rw [h_sub]
        simp only [pure_bind]
        have hd_toNat : (n - m).toNat = n.toNat - m.toNat :=
          UInt64.toNat_sub_of_le' (Nat.le_of_lt hnm)
        have hd_ne : (n - m) ≠ 0 := by
          intro h
          have hz : (n - m).toNat = 0 := by rw [h]; rfl
          omega
        obtain ⟨r, h_tz, hr_lt, hr_dvd, hr_bit⟩ := tz_nonzero_spec (n - m) hd_ne
        rw [h_tz]
        simp only [RustM_ok_bind]
        have hr_lt_2_64 : r.toNat < 2 ^ 64 := by
          have h32 : r.toNat < 2 ^ 32 := UInt32.toNat_lt r
          omega
        have hr_uint64_toNat : (r.toNat.toUInt64).toNat = r.toNat :=
          UInt64.toNat_ofNat_of_lt' hr_lt_2_64
        have h_0_le : (0 : UInt32) ≤ r := by
          rw [UInt32.le_iff_toNat_le]
          show (0 : UInt32).toNat ≤ r.toNat
          have h0 : (0 : UInt32).toNat = 0 := rfl
          omega
        have h_lt_64 : r < (64 : UInt32) := by
          rw [UInt32.lt_iff_toNat_lt]
          show r.toNat < (64 : UInt32).toNat
          have h64 : (64 : UInt32).toNat = 64 := rfl
          omega
        have h_shr : ((n - m) >>>? r : RustM u64)
            = RustM.ok ((n - m) >>> r.toNat.toUInt64) := by
          show (rust_primitives.ops.bit.Shr.shr (n - m) r : RustM u64)
              = RustM.ok ((n - m) >>> r.toNat.toUInt64)
          show (if ((0 : UInt32) ≤ r && r < (64 : UInt32)) then
                  pure ((n - m) >>> r.toNat.toUInt64)
                else .fail .integerOverflow) = RustM.ok ((n - m) >>> r.toNat.toUInt64)
          have h_cond_eq : ((0 : UInt32) ≤ r && r < (64 : UInt32)) = true := by
            simp [h_0_le, h_lt_64]
          rw [h_cond_eq]; rfl
        rw [h_shr]
        simp only [RustM_ok_bind]
        have h_n'_toNat : ((n - m) >>> r.toNat.toUInt64).toNat
            = (n - m).toNat >>> r.toNat := by
          rw [UInt64.toNat_shiftRight, hr_uint64_toNat, Nat.mod_eq_of_lt hr_lt]
        have h_n'_div : ((n - m) >>> r.toNat.toUInt64).toNat
            = (n - m).toNat / 2 ^ r.toNat := by
          rw [h_n'_toNat, Nat.shiftRight_eq_div_pow]
        have h_n'_mul : ((n - m) >>> r.toNat.toUInt64).toNat * 2 ^ r.toNat
            = (n - m).toNat := by
          rw [h_n'_div]; exact Nat.div_mul_cancel hr_dvd
        have h_n'_odd : ((n - m) >>> r.toNat.toUInt64).toNat % 2 = 1 := by
          rw [h_n'_toNat, ← Nat.and_one_is_mod]; exact hr_bit
        have h_n'_pos : 0 < ((n - m) >>> r.toNat.toUInt64).toNat := by omega
        have h_meas : m.toNat + ((n - m) >>> r.toNat.toUInt64).toNat < k := by
          have h_le : ((n - m) >>> r.toNat.toUInt64).toNat ≤ (n - m).toNat := by
            rw [h_n'_div]; exact Nat.div_le_self _ _
          omega
        rw [ih (m.toNat + ((n - m) >>> r.toNat.toUInt64).toNat) h_meas
              m ((n - m) >>> r.toNat.toUInt64) hm_odd h_n'_odd hm_pos h_n'_pos rfl]
        apply congrArg RustM.ok
        apply congrArg UInt64.ofNat
        rw [Nat.gcd_comm m.toNat n.toNat,
            nat_gcd_sub_right n.toNat m.toNat (Nat.le_of_lt hnm), ← hd_toNat,
            ← h_n'_mul, nat_gcd_mul_pow_two_left_odd_right _ _ hm_odd]
        exact Nat.gcd_comm m.toNat _

/-! ## Outer-wrapper Nat helpers -/

private theorem gcd_two_pow_combine (m n p q : Nat)
    (hm : m % 2 = 1) (hn : n % 2 = 1) :
    Nat.gcd (m * 2 ^ p) (n * 2 ^ q) = 2 ^ (min p q) * Nat.gcd m n := by
  rcases Nat.le_total p q with hpq | hqp
  · rw [Nat.min_eq_left hpq]
    have h2q : (2 : Nat) ^ q = 2 ^ (q - p) * 2 ^ p := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [h2q, ← Nat.mul_assoc, Nat.gcd_mul_right]
    have h_strip : Nat.gcd m (n * 2 ^ (q - p)) = Nat.gcd m n := by
      rw [Nat.gcd_comm m (n * 2 ^ (q - p)),
          nat_gcd_mul_pow_two_left_odd_right n m hm (q - p),
          Nat.gcd_comm n m]
    rw [h_strip, Nat.mul_comm]
  · rw [Nat.min_eq_right hqp]
    have h2p : (2 : Nat) ^ p = 2 ^ (p - q) * 2 ^ q := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [h2p, ← Nat.mul_assoc, Nat.gcd_mul_right,
        nat_gcd_mul_pow_two_left_odd_right m n hn (p - q), Nat.mul_comm]

private theorem pow_two_dvd_odd_mul (s m t : Nat)
    (hdvd : 2 ^ s ∣ m * 2 ^ t) (hm : m % 2 = 1) : s ≤ t := by
  by_cases hcon : s ≤ t
  · exact hcon
  · exfalso
    have hts : t + 1 ≤ s := by omega
    have h_dvd' : 2 ^ (t + 1) ∣ m * 2 ^ t := Nat.dvd_trans (Nat.pow_dvd_pow 2 hts) hdvd
    rw [Nat.pow_succ, Nat.mul_comm m (2 ^ t)] at h_dvd'
    have h2m : 2 ∣ m := (Nat.mul_dvd_mul_iff_left (Nat.two_pow_pos t)).mp h_dvd'
    omega

private theorem two_pow_dvd_iff_testBit (k z : Nat) :
    2 ^ k ∣ z ↔ ∀ i, i < k → Nat.testBit z i = false := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    have h2split : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
    constructor
    · intro hdvd i hik
      obtain ⟨c, hc⟩ := hdvd
      have hz_half : z / 2 = 2 ^ k * c := by
        rw [hc, h2split, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
      have hbits_half : ∀ j, j < k → Nat.testBit (z / 2) j = false :=
        (ih (z / 2)).mp ⟨c, hz_half⟩
      rcases Nat.eq_zero_or_pos i with hi0 | hipos
      · subst hi0
        have hz_even : z % 2 = 0 := by
          have hzc : z = 2 * (2 ^ k * c) := by rw [hc, h2split, Nat.mul_assoc]
          omega
        exact Nat.mod_two_eq_zero_iff_testBit_zero.mp hz_even
      · obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        subst hj
        rw [Nat.testBit_succ]
        exact hbits_half j (by omega)
    · intro hbits
      have hz_even : z % 2 = 0 :=
        Nat.mod_two_eq_zero_iff_testBit_zero.mpr (hbits 0 (by omega))
      have hbits_half : ∀ j, j < k → Nat.testBit (z / 2) j = false := by
        intro j hjk
        rw [← Nat.testBit_succ]
        exact hbits (j + 1) (by omega)
      obtain ⟨c, hc⟩ := (ih (z / 2)).mpr hbits_half
      refine ⟨c, ?_⟩
      have hz2 : z = 2 * (z / 2) := by omega
      rw [hz2, hc, h2split, Nat.mul_assoc]

private theorem two_pow_dvd_or (k x y : Nat) :
    2 ^ k ∣ (x ||| y) ↔ 2 ^ k ∣ x ∧ 2 ^ k ∣ y := by
  rw [two_pow_dvd_iff_testBit, two_pow_dvd_iff_testBit, two_pow_dvd_iff_testBit]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have hi' := h i hi
      rw [Nat.testBit_or] at hi'
      exact (Bool.or_eq_false_iff.mp hi').1
    · have hi' := h i hi
      rw [Nat.testBit_or] at hi'
      exact (Bool.or_eq_false_iff.mp hi').2
  · intro ⟨hx, hy⟩ i hi
    rw [Nat.testBit_or, hx i hi, hy i hi]
    rfl

/-! ## Master closed-form postcondition for `lcm_u64.gcd_u64` -/

private theorem gcd_u64_spec (a b : u64) :
    lcm_u64.gcd_u64 a b
      = RustM.ok (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) := by
  unfold lcm_u64.gcd_u64
  simp only []
  have h_a_eqq : (a ==? (0 : u64) : RustM Bool) = pure (a == (0 : u64)) := rfl
  have h_b_eqq : (b ==? (0 : u64) : RustM Bool) = pure (b == (0 : u64)) := rfl
  have h_or_def : ∀ (x y : Bool),
      (x ||? y : RustM Bool) = pure (x || y) := fun _ _ => rfl
  rw [h_a_eqq, h_b_eqq]
  simp only [pure_bind, h_or_def]
  by_cases ha : a = 0
  · subst ha
    have h_dec : ((0 : u64) == (0 : u64)) = true := rfl
    rw [h_dec]
    simp only [Bool.true_or, if_true]
    show RustM.ok (0 ||| b) = RustM.ok (UInt64.ofNat (Nat.gcd 0 b.toNat))
    congr 1
    rw [Nat.gcd_zero_left]
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_ofNat_of_lt' b.toNat_lt]
    show (0 ||| b).toNat = b.toNat
    rw [UInt64.toNat_or]
    show (0 : u64).toNat ||| b.toNat = b.toNat
    show 0 ||| b.toNat = b.toNat
    exact Nat.zero_or _
  · by_cases hb : b = 0
    · subst hb
      have h_a_dec : (a == (0 : u64)) = false := beq_eq_false_iff_ne.mpr ha
      have h_b_dec : ((0 : u64) == (0 : u64)) = true := rfl
      rw [h_a_dec, h_b_dec]
      simp only [Bool.false_or, if_true]
      show RustM.ok (a ||| 0) = RustM.ok (UInt64.ofNat (Nat.gcd a.toNat 0))
      congr 1
      rw [Nat.gcd_zero_right]
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_ofNat_of_lt' a.toNat_lt]
      show (a ||| 0).toNat = a.toNat
      rw [UInt64.toNat_or]
      show a.toNat ||| (0 : u64).toNat = a.toNat
      show a.toNat ||| 0 = a.toNat
      exact Nat.or_zero _
    · have h_a_dec : (a == (0 : u64)) = false := beq_eq_false_iff_ne.mpr ha
      have h_b_dec : (b == (0 : u64)) = false := beq_eq_false_iff_ne.mpr hb
      rw [h_a_dec, h_b_dec]
      simp only [Bool.false_or, Bool.false_eq_true, if_false]
      have h_ab_or : (a ||| b).toNat = a.toNat ||| b.toNat := UInt64.toNat_or a b
      have h_ab_ne : a ||| b ≠ 0 := by
        intro hcon
        apply ha
        apply UInt64.toNat_inj.mp
        show a.toNat = (0 : u64).toNat
        have h_or0 : a.toNat ||| b.toNat = 0 := by
          have h1 : (a ||| b).toNat = 0 := by rw [hcon]; rfl
          rwa [h_ab_or] at h1
        have h_dvd : (2 : Nat) ^ 64 ∣ (a.toNat ||| b.toNat) := by
          rw [h_or0]; exact Nat.dvd_zero _
        have h_a_dvd := ((two_pow_dvd_or 64 a.toNat b.toNat).mp h_dvd).1
        have h_a0 : a.toNat = 0 := Nat.eq_zero_of_dvd_of_lt h_a_dvd (UInt64.toNat_lt a)
        rw [h_a0]; rfl
      obtain ⟨shift, h_tz_ab, hsh_lt, hsh_dvd, hsh_bit⟩ :=
        tz_nonzero_spec (a ||| b) h_ab_ne
      obtain ⟨mTz, h_tz_a, hmTz_lt, hmTz_dvd, hmTz_bit⟩ := tz_nonzero_spec a ha
      obtain ⟨nTz, h_tz_b, hnTz_lt, hnTz_dvd, hnTz_bit⟩ := tz_nonzero_spec b hb
      have h_shr_a : (a >>>? mTz : RustM u64) = RustM.ok (a >>> mTz.toNat.toUInt64) := by
        show (rust_primitives.ops.bit.Shr.shr a mTz : RustM u64)
            = RustM.ok (a >>> mTz.toNat.toUInt64)
        show (if ((0 : UInt32) ≤ mTz && mTz < (64 : UInt32)) then
                pure (a >>> mTz.toNat.toUInt64)
              else .fail .integerOverflow) = RustM.ok (a >>> mTz.toNat.toUInt64)
        have h_c : ((0 : UInt32) ≤ mTz && mTz < (64 : UInt32)) = true := by
          have h_0le : (0 : UInt32) ≤ mTz := by
            rw [UInt32.le_iff_toNat_le]; show (0 : UInt32).toNat ≤ mTz.toNat
            have h0 : (0 : UInt32).toNat = 0 := rfl
            omega
          have h_lt : mTz < (64 : UInt32) := by
            rw [UInt32.lt_iff_toNat_lt]; show mTz.toNat < (64 : UInt32).toNat
            have h64 : (64 : UInt32).toNat = 64 := rfl
            omega
          simp [h_0le, h_lt]
        rw [h_c]; rfl
      have h_shr_b : (b >>>? nTz : RustM u64) = RustM.ok (b >>> nTz.toNat.toUInt64) := by
        show (rust_primitives.ops.bit.Shr.shr b nTz : RustM u64)
            = RustM.ok (b >>> nTz.toNat.toUInt64)
        show (if ((0 : UInt32) ≤ nTz && nTz < (64 : UInt32)) then
                pure (b >>> nTz.toNat.toUInt64)
              else .fail .integerOverflow) = RustM.ok (b >>> nTz.toNat.toUInt64)
        have h_c : ((0 : UInt32) ≤ nTz && nTz < (64 : UInt32)) = true := by
          have h_0le : (0 : UInt32) ≤ nTz := by
            rw [UInt32.le_iff_toNat_le]; show (0 : UInt32).toNat ≤ nTz.toNat
            have h0 : (0 : UInt32).toNat = 0 := rfl
            omega
          have h_lt : nTz < (64 : UInt32) := by
            rw [UInt32.lt_iff_toNat_lt]; show nTz.toNat < (64 : UInt32).toNat
            have h64 : (64 : UInt32).toNat = 64 := rfl
            omega
          simp [h_0le, h_lt]
        rw [h_c]; rfl
      have hmTz_lt64 : mTz.toNat < 2 ^ 64 := by omega
      have hmTz_u : mTz.toNat.toUInt64.toNat = mTz.toNat :=
        UInt64.toNat_ofNat_of_lt' hmTz_lt64
      have hnTz_lt64 : nTz.toNat < 2 ^ 64 := by omega
      have hnTz_u : nTz.toNat.toUInt64.toNat = nTz.toNat :=
        UInt64.toNat_ofNat_of_lt' hnTz_lt64
      have h_m_toNat : (a >>> mTz.toNat.toUInt64).toNat = a.toNat / 2 ^ mTz.toNat := by
        rw [UInt64.toNat_shiftRight, hmTz_u, Nat.mod_eq_of_lt hmTz_lt,
            Nat.shiftRight_eq_div_pow]
      have h_n_toNat : (b >>> nTz.toNat.toUInt64).toNat = b.toNat / 2 ^ nTz.toNat := by
        rw [UInt64.toNat_shiftRight, hnTz_u, Nat.mod_eq_of_lt hnTz_lt,
            Nat.shiftRight_eq_div_pow]
      have h_m_odd : (a >>> mTz.toNat.toUInt64).toNat % 2 = 1 := by
        rw [← Nat.and_one_is_mod, UInt64.toNat_shiftRight, hmTz_u,
            Nat.mod_eq_of_lt hmTz_lt]
        exact hmTz_bit
      have h_n_odd : (b >>> nTz.toNat.toUInt64).toNat % 2 = 1 := by
        rw [← Nat.and_one_is_mod, UInt64.toNat_shiftRight, hnTz_u,
            Nat.mod_eq_of_lt hnTz_lt]
        exact hnTz_bit
      have h_a_eq : a.toNat = (a >>> mTz.toNat.toUInt64).toNat * 2 ^ mTz.toNat := by
        rw [h_m_toNat]; exact (Nat.div_mul_cancel hmTz_dvd).symm
      have h_b_eq : b.toNat = (b >>> nTz.toNat.toUInt64).toNat * 2 ^ nTz.toNat := by
        rw [h_n_toNat]; exact (Nat.div_mul_cancel hnTz_dvd).symm
      have hsh_a : 2 ^ shift.toNat ∣ a.toNat := by
        have h := hsh_dvd; rw [h_ab_or] at h
        exact ((two_pow_dvd_or shift.toNat a.toNat b.toNat).mp h).1
      have hsh_b : 2 ^ shift.toNat ∣ b.toNat := by
        have h := hsh_dvd; rw [h_ab_or] at h
        exact ((two_pow_dvd_or shift.toNat a.toNat b.toNat).mp h).2
      have hsh_le_mTz : shift.toNat ≤ mTz.toNat := by
        rw [h_a_eq] at hsh_a
        exact pow_two_dvd_odd_mul shift.toNat _ mTz.toNat hsh_a h_m_odd
      have hsh_le_nTz : shift.toNat ≤ nTz.toNat := by
        rw [h_b_eq] at hsh_b
        exact pow_two_dvd_odd_mul shift.toNat _ nTz.toNat hsh_b h_n_odd
      have h_shift_eq : shift.toNat = min mTz.toNat nTz.toNat := by
        rcases Nat.lt_or_ge shift.toNat (min mTz.toNat nTz.toNat) with hlt | hge
        · exfalso
          have hd_a : 2 ^ (shift.toNat + 1) ∣ a.toNat :=
            Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hmTz_dvd
          have hd_b : 2 ^ (shift.toNat + 1) ∣ b.toNat :=
            Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hnTz_dvd
          have hd_ab : 2 ^ (shift.toNat + 1) ∣ (a.toNat ||| b.toNat) :=
            (two_pow_dvd_or (shift.toNat + 1) a.toNat b.toNat).mpr ⟨hd_a, hd_b⟩
          rw [← h_ab_or] at hd_ab
          obtain ⟨c, hc⟩ := hd_ab
          have hbit0 : ((a ||| b).toNat >>> shift.toNat) &&& 1 = 0 := by
            rw [hc, Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.mul_assoc,
                Nat.mul_div_cancel_left _ (Nat.two_pow_pos shift.toNat),
                Nat.and_one_is_mod]
            exact Nat.mul_mod_right 2 c
          rw [hbit0] at hsh_bit
          exact absurd hsh_bit (by decide)
        · omega
      rw [h_tz_ab]
      simp only [RustM_ok_bind]
      rw [h_tz_a]
      simp only [RustM_ok_bind]
      rw [h_shr_a]
      simp only [RustM_ok_bind]
      rw [h_tz_b]
      simp only [RustM_ok_bind]
      rw [h_shr_b]
      simp only [RustM_ok_bind]
      rw [gcd_stein_loop_spec (a >>> mTz.toNat.toUInt64) (b >>> nTz.toNat.toUInt64)
            h_m_odd h_n_odd]
      simp only [RustM_ok_bind]
      have h_combine : Nat.gcd a.toNat b.toNat
            = 2 ^ shift.toNat * Nat.gcd (a >>> mTz.toNat.toUInt64).toNat
                (b >>> nTz.toNat.toUInt64).toNat := by
        rw [h_a_eq, h_b_eq, gcd_two_pow_combine _ _ _ _ h_m_odd h_n_odd, h_shift_eq]
      have hsh_lt64 : shift.toNat < 2 ^ 64 := by omega
      have hsh_u : shift.toNat.toUInt64.toNat = shift.toNat :=
        UInt64.toNat_ofNat_of_lt' hsh_lt64
      have h_shl : ((UInt64.ofNat (Nat.gcd (a >>> mTz.toNat.toUInt64).toNat
            (b >>> nTz.toNat.toUInt64).toNat)) <<<? shift : RustM u64)
          = RustM.ok ((UInt64.ofNat (Nat.gcd (a >>> mTz.toNat.toUInt64).toNat
              (b >>> nTz.toNat.toUInt64).toNat)) <<< shift.toNat.toUInt64) := by
        show (rust_primitives.ops.bit.Shl.shl _ shift : RustM u64) = RustM.ok _
        show (if ((0 : UInt32) ≤ shift && shift < (64 : UInt32)) then
                pure (_ <<< shift.toNat.toUInt64)
              else .fail .integerOverflow) = RustM.ok _
        have h_c : ((0 : UInt32) ≤ shift && shift < (64 : UInt32)) = true := by
          have h_0le : (0 : UInt32) ≤ shift := by
            rw [UInt32.le_iff_toNat_le]; show (0 : UInt32).toNat ≤ shift.toNat
            have h0 : (0 : UInt32).toNat = 0 := rfl
            omega
          have h_lt : shift < (64 : UInt32) := by
            rw [UInt32.lt_iff_toNat_lt]; show shift.toNat < (64 : UInt32).toNat
            have h64 : (64 : UInt32).toNat = 64 := rfl
            omega
          simp [h_0le, h_lt]
        rw [h_c]; rfl
      rw [h_shl]
      apply congrArg RustM.ok
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_ofNat_of_lt' (gcd_lt_2_64 a b), UInt64.toNat_shiftLeft,
          UInt64.toNat_ofNat_of_lt' (gcd_lt_2_64 _ _), hsh_u,
          Nat.mod_eq_of_lt (show shift.toNat < 64 by omega), Nat.shiftLeft_eq,
          Nat.mul_comm, ← h_combine]
      exact Nat.mod_eq_of_lt (gcd_lt_2_64 a b)

/-! ## Multiplication helpers -/

/-- `0 * t : u64` doesn't overflow and equals `0`. -/
private theorem mul_zero_left_pure (t : u64) :
    ((0 : u64) *? t : RustM u64) = pure 0 := by
  show (rust_primitives.ops.arith.Mul.mul (0 : u64) t : RustM u64) = pure 0
  show (if BitVec.umulOverflow (0 : u64).toBitVec t.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure ((0 : u64) * t)) = pure 0
  have h_no_mul_ovf : BitVec.umulOverflow (0 : u64).toBitVec t.toBitVec = false := by
    have : ¬ UInt64.mulOverflow (0 : u64) t := by
      rw [UInt64.mulOverflow_iff]
      have h0 : (0 : u64).toNat = 0 := rfl
      rw [h0, Nat.zero_mul]
      exact fun h => absurd h (by simp [Nat.two_pow_pos])
    simpa [UInt64.mulOverflow] using this
  rw [h_no_mul_ovf]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have h0u : (0 : u64) * t = 0 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_mul]
    have h0 : (0 : u64).toNat = 0 := rfl
    rw [h0, Nat.zero_mul]
  rw [h0u]

/-- `t * 0 : u64` doesn't overflow and equals `0`. -/
private theorem mul_zero_right_pure (t : u64) :
    (t *? (0 : u64) : RustM u64) = pure 0 := by
  show (rust_primitives.ops.arith.Mul.mul t (0 : u64) : RustM u64) = pure 0
  show (if BitVec.umulOverflow t.toBitVec (0 : u64).toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (t * (0 : u64))) = pure 0
  have h_no_mul_ovf : BitVec.umulOverflow t.toBitVec (0 : u64).toBitVec = false := by
    have : ¬ UInt64.mulOverflow t (0 : u64) := by
      rw [UInt64.mulOverflow_iff]
      have h0 : (0 : u64).toNat = 0 := rfl
      rw [h0, Nat.mul_zero]
      exact fun h => absurd h (by simp [Nat.two_pow_pos])
    simpa [UInt64.mulOverflow] using this
  rw [h_no_mul_ovf]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have h0u : t * (0 : u64) = 0 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_mul]
    have h0 : (0 : u64).toNat = 0 := rfl
    rw [h0, Nat.mul_zero]
  rw [h0u]

/-! ## Master closed-form for `lcm`

The `lcm` function returns `0` in the explicit `(0, 0)` branch, and otherwise
computes `x * (y / gcd(x, y))`. The unified closed form, valid under
`x.toNat * y.toNat < 2 ^ 64`, is:

  `lcm x y = ofNat (x.toNat * y.toNat / Nat.gcd x.toNat y.toNat)`

In the `(0, 0)` case this reduces to `0 * 0 / 0 = 0` (Nat convention).
In the `(0, y)` case to `0 * y / y = 0`. In the `(x, 0)` case to
`x * 0 / x = 0`. -/

/-- Master closed-form for `lcm_u64.lcm`. -/
private theorem lcm_spec (x y : u64) (h_no_ovf : x.toNat * y.toNat < 2 ^ 64) :
    lcm_u64.lcm x y
      = RustM.ok (UInt64.ofNat (x.toNat * y.toNat / Nat.gcd x.toNat y.toNat)) := by
  unfold lcm_u64.lcm
  have h_x_eqq : (x ==? (0 : u64) : RustM Bool) = pure (x == (0 : u64)) := rfl
  have h_y_eqq : (y ==? (0 : u64) : RustM Bool) = pure (y == (0 : u64)) := rfl
  have h_and_def : ∀ (x y : Bool),
      (x &&? y : RustM Bool) = pure (x && y) := fun _ _ => rfl
  rw [h_x_eqq, h_y_eqq]
  simp only [pure_bind, h_and_def]
  by_cases hx_zero : x = 0
  · subst hx_zero
    by_cases hy_zero : y = 0
    · subst hy_zero
      -- Both zero: function takes the short-circuit branch and returns 0.
      have h_dec : ((0 : u64) == (0 : u64)) = true := rfl
      rw [h_dec]
      simp only [Bool.and_self, if_true]
      rfl
    · -- x = 0, y ≠ 0: fall through, gcd_u64 0 y = y, then 0 * (y / y) = 0.
      have h_x_dec : ((0 : u64) == (0 : u64)) = true := rfl
      have h_y_dec : (y == (0 : u64)) = false := beq_eq_false_iff_ne.mpr hy_zero
      rw [h_x_dec, h_y_dec]
      simp only [Bool.true_and, Bool.false_eq_true, if_false]
      rw [gcd_u64_spec 0 y]
      simp only [RustM_ok_bind]
      have h_gcd_y : Nat.gcd (0 : u64).toNat y.toNat = y.toNat := by
        show Nat.gcd 0 y.toNat = y.toNat
        rw [Nat.gcd_zero_left]
      have h_gcd_eq_y : UInt64.ofNat (Nat.gcd (0 : u64).toNat y.toNat) = y := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_ofNat_of_lt' (gcd_lt_2_64 0 y), h_gcd_y]
      rw [h_gcd_eq_y]
      have h_div : (y /? y : RustM u64) = pure (y / y) := by
        show (rust_primitives.ops.arith.Div.div y y : RustM u64) = pure (y / y)
        show (if y = 0 then (.fail .divisionByZero : RustM u64) else pure (y / y)) = _
        rw [if_neg hy_zero]
      rw [h_div]
      simp only [pure_bind]
      rw [mul_zero_left_pure (y / y)]
      show RustM.ok 0 = RustM.ok (UInt64.ofNat
        ((0 : u64).toNat * y.toNat / Nat.gcd (0 : u64).toNat y.toNat))
      congr 1
      have h0 : (0 : u64).toNat = 0 := rfl
      rw [h0, Nat.zero_mul, Nat.zero_div]
      rfl
  · by_cases hy_zero : y = 0
    · subst hy_zero
      -- x ≠ 0, y = 0: fall through, gcd_u64 x 0 = x, then x * (0 / x) = 0.
      have h_x_dec : (x == (0 : u64)) = false := beq_eq_false_iff_ne.mpr hx_zero
      have h_y_dec : ((0 : u64) == (0 : u64)) = true := rfl
      rw [h_x_dec, h_y_dec]
      simp only [Bool.false_and, Bool.false_eq_true, if_false]
      rw [gcd_u64_spec x 0]
      simp only [RustM_ok_bind]
      have h_gcd_x : Nat.gcd x.toNat (0 : u64).toNat = x.toNat := by
        show Nat.gcd x.toNat 0 = x.toNat
        rw [Nat.gcd_zero_right]
      have h_gcd_eq_x : UInt64.ofNat (Nat.gcd x.toNat (0 : u64).toNat) = x := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_ofNat_of_lt' (gcd_lt_2_64 x 0), h_gcd_x]
      rw [h_gcd_eq_x]
      have h_div : ((0 : u64) /? x : RustM u64) = pure ((0 : u64) / x) := by
        show (rust_primitives.ops.arith.Div.div (0 : u64) x : RustM u64) = pure ((0 : u64) / x)
        show (if x = 0 then (.fail .divisionByZero : RustM u64) else pure ((0 : u64) / x)) = _
        rw [if_neg hx_zero]
      rw [h_div]
      simp only [pure_bind]
      have h_0div_x : (0 : u64) / x = 0 := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_div]
        have : (0 : u64).toNat = 0 := rfl
        rw [this, Nat.zero_div]
      rw [h_0div_x]
      rw [mul_zero_right_pure x]
      show RustM.ok 0 = RustM.ok (UInt64.ofNat
        (x.toNat * (0 : u64).toNat / Nat.gcd x.toNat (0 : u64).toNat))
      congr 1
      have h0 : (0 : u64).toNat = 0 := rfl
      rw [h0, Nat.mul_zero, Nat.zero_div]
      rfl
    · -- Both nonzero. Use gcd_u64_spec and reason about the multiplication.
      have h_x_dec : (x == (0 : u64)) = false := beq_eq_false_iff_ne.mpr hx_zero
      have h_y_dec : (y == (0 : u64)) = false := beq_eq_false_iff_ne.mpr hy_zero
      rw [h_x_dec, h_y_dec]
      simp only [Bool.false_and, Bool.false_eq_true, if_false]
      rw [gcd_u64_spec x y]
      simp only [RustM_ok_bind]
      have hx_pos : 0 < x.toNat := by
        rcases Nat.eq_zero_or_pos x.toNat with h | h
        · exfalso; apply hx_zero; apply UInt64.toNat_inj.mp; rw [h]; rfl
        · exact h
      have hy_pos : 0 < y.toNat := by
        rcases Nat.eq_zero_or_pos y.toNat with h | h
        · exfalso; apply hy_zero; apply UInt64.toNat_inj.mp; rw [h]; rfl
        · exact h
      have hg_natpos : 0 < Nat.gcd x.toNat y.toNat :=
        Nat.gcd_pos_of_pos_right x.toNat hy_pos
      have hg_natlt : Nat.gcd x.toNat y.toNat < 2 ^ 64 := gcd_lt_2_64 x y
      have hg_toNat : (UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toNat =
                      Nat.gcd x.toNat y.toNat :=
        UInt64.toNat_ofNat_of_lt' hg_natlt
      have hg_pos : 0 < (UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toNat := by
        rw [hg_toNat]; exact hg_natpos
      have hg_ne : UInt64.ofNat (Nat.gcd x.toNat y.toNat) ≠ 0 := by
        intro h
        have : (UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toNat = 0 := by rw [h]; rfl
        omega
      have h_div : (y /? UInt64.ofNat (Nat.gcd x.toNat y.toNat) : RustM u64) =
                   pure (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)) := by
        show (rust_primitives.ops.arith.Div.div y
                (UInt64.ofNat (Nat.gcd x.toNat y.toNat)) : RustM u64) = _
        show (if UInt64.ofNat (Nat.gcd x.toNat y.toNat) = 0 then
                (.fail .divisionByZero : RustM u64)
              else pure (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat))) = _
        rw [if_neg hg_ne]
      rw [h_div]
      simp only [pure_bind]
      have h_g_dvd_y : (UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toNat ∣ y.toNat := by
        rw [hg_toNat]; exact Nat.gcd_dvd_right _ _
      have h_yg_toNat : (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toNat =
                        y.toNat / Nat.gcd x.toNat y.toNat := by
        rw [UInt64.toNat_div, hg_toNat]
      have h_yg_le_y : y.toNat / Nat.gcd x.toNat y.toNat ≤ y.toNat :=
        Nat.div_le_self _ _
      have h_prod_le : x.toNat * (y.toNat / Nat.gcd x.toNat y.toNat) ≤
                       x.toNat * y.toNat :=
        Nat.mul_le_mul_left x.toNat h_yg_le_y
      have h_prod_lt : x.toNat * (y.toNat / Nat.gcd x.toNat y.toNat) < 2 ^ 64 :=
        Nat.lt_of_le_of_lt h_prod_le h_no_ovf
      have h_xy_div : x.toNat * y.toNat / Nat.gcd x.toNat y.toNat
            = x.toNat * (y.toNat / Nat.gcd x.toNat y.toNat) :=
        Nat.mul_div_assoc x.toNat (Nat.gcd_dvd_right _ _)
      have h_mul : (x *? (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)) : RustM u64)
            = pure (UInt64.ofNat (x.toNat * y.toNat / Nat.gcd x.toNat y.toNat)) := by
        show (rust_primitives.ops.arith.Mul.mul
                x (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)) : RustM u64) = _
        show (if BitVec.umulOverflow x.toBitVec
                  (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toBitVec then
                (.fail .integerOverflow : RustM u64)
              else pure (x * (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)))) = _
        have h_no_mul_ovf :
            BitVec.umulOverflow x.toBitVec
              (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)).toBitVec = false := by
          have : ¬ UInt64.mulOverflow x (y / UInt64.ofNat (Nat.gcd x.toNat y.toNat)) := by
            rw [UInt64.mulOverflow_iff, h_yg_toNat]
            omega
          simpa [UInt64.mulOverflow] using this
        rw [h_no_mul_ovf]
        simp only [Bool.false_eq_true, ↓reduceIte]
        congr 1
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_mul, h_yg_toNat,
            UInt64.toNat_ofNat_of_lt' (by rw [h_xy_div]; exact h_prod_lt)]
        rw [h_xy_div]
        exact Nat.mod_eq_of_lt h_prod_lt
      rw [h_mul]
      rfl

/-! ## Specialised closed-form for the overflow case

The `test_lcm_overflow` cases need a special form because `x * y = 2^64`
overflows. We prove `lcm(2^63, 2) = 2^63` by direct unfolding and computation
on the specific numeric values; the loop unwinds to two iterations. -/

/-- A specialised closed-form: when `x` is divisible by `y` (both positive),
`gcd(x, y) = y`, so `lcm x y = x * (y / y) = x`. -/
private theorem lcm_dvd_left (x y : u64) (hx : x ≠ 0) (hy : y ≠ 0)
    (hdvd : y.toNat ∣ x.toNat) :
    lcm_u64.lcm x y = RustM.ok x := by
  -- Compute gcd: it's y.
  have hx_pos : 0 < x.toNat := by
    rcases Nat.eq_zero_or_pos x.toNat with h | h
    · exfalso; apply hx; apply UInt64.toNat_inj.mp; rw [h]; rfl
    · exact h
  have hy_pos : 0 < y.toNat := by
    rcases Nat.eq_zero_or_pos y.toNat with h | h
    · exfalso; apply hy; apply UInt64.toNat_inj.mp; rw [h]; rfl
    · exact h
  have h_gcd_eq : Nat.gcd x.toNat y.toNat = y.toNat := by
    exact Nat.gcd_eq_right hdvd
  -- We compute lcm via direct unfolding.
  unfold lcm_u64.lcm
  have h_x_eqq : (x ==? (0 : u64) : RustM Bool) = pure (x == (0 : u64)) := rfl
  have h_y_eqq : (y ==? (0 : u64) : RustM Bool) = pure (y == (0 : u64)) := rfl
  have h_and_def : ∀ (x y : Bool),
      (x &&? y : RustM Bool) = pure (x && y) := fun _ _ => rfl
  rw [h_x_eqq, h_y_eqq]
  simp only [pure_bind, h_and_def]
  have h_x_dec : (x == (0 : u64)) = false := beq_eq_false_iff_ne.mpr hx
  have h_y_dec : (y == (0 : u64)) = false := beq_eq_false_iff_ne.mpr hy
  rw [h_x_dec, h_y_dec]
  simp only [Bool.false_and, Bool.false_eq_true, if_false]
  rw [gcd_u64_spec x y]
  simp only [RustM_ok_bind]
  have hg_eq_y : UInt64.ofNat (Nat.gcd x.toNat y.toNat) = y := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_ofNat_of_lt' (gcd_lt_2_64 x y), h_gcd_eq]
  rw [hg_eq_y]
  have h_div : (y /? y : RustM u64) = pure (y / y) := by
    show (rust_primitives.ops.arith.Div.div y y : RustM u64) = pure (y / y)
    show (if y = 0 then (.fail .divisionByZero : RustM u64) else pure (y / y)) = _
    rw [if_neg hy]
  rw [h_div]
  simp only [pure_bind]
  -- y / y = 1
  have h_y_div_y : y / y = 1 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_div, Nat.div_self hy_pos]
    have h1 : (1 : u64).toNat = 1 := by decide
    rw [h1]
  rw [h_y_div_y]
  -- x * 1 = x; no overflow.
  have h_mul : (x *? (1 : u64) : RustM u64) = pure x := by
    show (rust_primitives.ops.arith.Mul.mul x (1 : u64) : RustM u64) = pure x
    show (if BitVec.umulOverflow x.toBitVec (1 : u64).toBitVec then
            (.fail .integerOverflow : RustM u64)
          else pure (x * (1 : u64))) = pure x
    have h_no_mul_ovf : BitVec.umulOverflow x.toBitVec (1 : u64).toBitVec = false := by
      have : ¬ UInt64.mulOverflow x (1 : u64) := by
        rw [UInt64.mulOverflow_iff]
        have h1 : (1 : u64).toNat = 1 := by decide
        rw [h1, Nat.mul_one]
        intro h
        exact absurd (UInt64.toNat_lt x) (Nat.not_lt.mpr h)
      simpa [UInt64.mulOverflow] using this
    rw [h_no_mul_ovf]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have h_x_mul_one : x * (1 : u64) = x := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_mul]
      have h1 : (1 : u64).toNat = 1 := by decide
      rw [h1, Nat.mul_one, Nat.mod_eq_of_lt (UInt64.toNat_lt x)]
    rw [h_x_mul_one]
  rw [h_mul]
  rfl

/-- Symmetric: if `x ∣ y` (both positive), `lcm x y = y`. -/
private theorem lcm_dvd_right (x y : u64) (hx : x ≠ 0) (hy : y ≠ 0)
    (hdvd : x.toNat ∣ y.toNat) :
    lcm_u64.lcm x y = RustM.ok y := by
  have hx_pos : 0 < x.toNat := by
    rcases Nat.eq_zero_or_pos x.toNat with h | h
    · exfalso; apply hx; apply UInt64.toNat_inj.mp; rw [h]; rfl
    · exact h
  have hy_pos : 0 < y.toNat := by
    rcases Nat.eq_zero_or_pos y.toNat with h | h
    · exfalso; apply hy; apply UInt64.toNat_inj.mp; rw [h]; rfl
    · exact h
  have h_gcd_eq : Nat.gcd x.toNat y.toNat = x.toNat := by
    exact Nat.gcd_eq_left hdvd
  unfold lcm_u64.lcm
  have h_x_eqq : (x ==? (0 : u64) : RustM Bool) = pure (x == (0 : u64)) := rfl
  have h_y_eqq : (y ==? (0 : u64) : RustM Bool) = pure (y == (0 : u64)) := rfl
  have h_and_def : ∀ (x y : Bool),
      (x &&? y : RustM Bool) = pure (x && y) := fun _ _ => rfl
  rw [h_x_eqq, h_y_eqq]
  simp only [pure_bind, h_and_def]
  have h_x_dec : (x == (0 : u64)) = false := beq_eq_false_iff_ne.mpr hx
  have h_y_dec : (y == (0 : u64)) = false := beq_eq_false_iff_ne.mpr hy
  rw [h_x_dec, h_y_dec]
  simp only [Bool.false_and, Bool.false_eq_true, if_false]
  rw [gcd_u64_spec x y]
  simp only [RustM_ok_bind]
  have hg_eq_x : UInt64.ofNat (Nat.gcd x.toNat y.toNat) = x := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_ofNat_of_lt' (gcd_lt_2_64 x y), h_gcd_eq]
  rw [hg_eq_x]
  have h_div : (y /? x : RustM u64) = pure (y / x) := by
    show (rust_primitives.ops.arith.Div.div y x : RustM u64) = pure (y / x)
    show (if x = 0 then (.fail .divisionByZero : RustM u64) else pure (y / x)) = _
    rw [if_neg hx]
  rw [h_div]
  simp only [pure_bind]
  -- x * (y / x) = y when x ∣ y; no overflow because result is y < 2^64.
  have h_yx_toNat : (y / x).toNat = y.toNat / x.toNat := UInt64.toNat_div y x
  have h_mul : (x *? (y / x) : RustM u64) = pure y := by
    show (rust_primitives.ops.arith.Mul.mul x (y / x) : RustM u64) = pure y
    show (if BitVec.umulOverflow x.toBitVec (y / x).toBitVec then
            (.fail .integerOverflow : RustM u64)
          else pure (x * (y / x))) = pure y
    have h_no_mul_ovf : BitVec.umulOverflow x.toBitVec (y / x).toBitVec = false := by
      have : ¬ UInt64.mulOverflow x (y / x) := by
        rw [UInt64.mulOverflow_iff, h_yx_toNat]
        rw [Nat.mul_div_cancel' hdvd]
        intro h
        exact absurd (UInt64.toNat_lt y) (Nat.not_lt.mpr h)
      simpa [UInt64.mulOverflow] using this
    rw [h_no_mul_ovf]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have h_x_mul_div_eq_y : x * (y / x) = y := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_mul, h_yx_toNat, Nat.mul_div_cancel' hdvd,
          Nat.mod_eq_of_lt (UInt64.toNat_lt y)]
    rw [h_x_mul_div_eq_y]
  rw [h_mul]
  rfl

/-! ## Obligation theorems -/

/-- `test_lcm` case 1: `lcm(1, 0) = 0`. -/
theorem lcm_1_0 : lcm_u64.lcm 1 0 = RustM.ok 0 := by
  have h_no_ovf : (1 : u64).toNat * (0 : u64).toNat < 2 ^ 64 := by
    show 1 * 0 < 2 ^ 64
    decide
  rw [lcm_spec 1 0 h_no_ovf]
  apply congrArg RustM.ok
  apply UInt64.toNat_inj.mp
  have h_lt : (1 : u64).toNat * (0 : u64).toNat / Nat.gcd (1 : u64).toNat (0 : u64).toNat
              < 2 ^ 64 := by
    show 1 * 0 / Nat.gcd 1 0 < 2 ^ 64
    decide
  rw [UInt64.toNat_ofNat_of_lt' h_lt]
  decide

/-- `test_lcm` case 2: `lcm(0, 1) = 0`. -/
theorem lcm_0_1 : lcm_u64.lcm 0 1 = RustM.ok 0 := by
  have h_no_ovf : (0 : u64).toNat * (1 : u64).toNat < 2 ^ 64 := by
    show 0 * 1 < 2 ^ 64
    decide
  rw [lcm_spec 0 1 h_no_ovf]
  apply congrArg RustM.ok
  apply UInt64.toNat_inj.mp
  have h_lt : (0 : u64).toNat * (1 : u64).toNat / Nat.gcd (0 : u64).toNat (1 : u64).toNat
              < 2 ^ 64 := by
    show 0 * 1 / Nat.gcd 0 1 < 2 ^ 64
    decide
  rw [UInt64.toNat_ofNat_of_lt' h_lt]
  decide

/-- `test_lcm` case 3: `lcm(1, 1) = 1`. -/
theorem lcm_1_1 : lcm_u64.lcm 1 1 = RustM.ok 1 := by
  have h_no_ovf : (1 : u64).toNat * (1 : u64).toNat < 2 ^ 64 := by
    show 1 * 1 < 2 ^ 64
    decide
  rw [lcm_spec 1 1 h_no_ovf]
  apply congrArg RustM.ok
  apply UInt64.toNat_inj.mp
  have h_lt : (1 : u64).toNat * (1 : u64).toNat / Nat.gcd (1 : u64).toNat (1 : u64).toNat
              < 2 ^ 64 := by
    show 1 * 1 / Nat.gcd 1 1 < 2 ^ 64
    decide
  rw [UInt64.toNat_ofNat_of_lt' h_lt]
  decide

/-- `test_lcm` case 4: `lcm(8, 9) = 72`. -/
theorem lcm_8_9 : lcm_u64.lcm 8 9 = RustM.ok 72 := by
  have h_no_ovf : (8 : u64).toNat * (9 : u64).toNat < 2 ^ 64 := by
    show 8 * 9 < 2 ^ 64
    decide
  rw [lcm_spec 8 9 h_no_ovf]
  apply congrArg RustM.ok
  apply UInt64.toNat_inj.mp
  have h_lt : (8 : u64).toNat * (9 : u64).toNat / Nat.gcd (8 : u64).toNat (9 : u64).toNat
              < 2 ^ 64 := by
    show 8 * 9 / Nat.gcd 8 9 < 2 ^ 64
    decide
  rw [UInt64.toNat_ofNat_of_lt' h_lt]
  decide

/-- `test_lcm` case 5: `lcm(11, 5) = 55`. -/
theorem lcm_11_5 : lcm_u64.lcm 11 5 = RustM.ok 55 := by
  have h_no_ovf : (11 : u64).toNat * (5 : u64).toNat < 2 ^ 64 := by
    show 11 * 5 < 2 ^ 64
    decide
  rw [lcm_spec 11 5 h_no_ovf]
  apply congrArg RustM.ok
  apply UInt64.toNat_inj.mp
  have h_lt : (11 : u64).toNat * (5 : u64).toNat / Nat.gcd (11 : u64).toNat (5 : u64).toNat
              < 2 ^ 64 := by
    show 11 * 5 / Nat.gcd 11 5 < 2 ^ 64
    decide
  rw [UInt64.toNat_ofNat_of_lt' h_lt]
  decide

/-- `test_lcm` case 6: `lcm(15, 17) = 255`. -/
theorem lcm_15_17 : lcm_u64.lcm 15 17 = RustM.ok 255 := by
  have h_no_ovf : (15 : u64).toNat * (17 : u64).toNat < 2 ^ 64 := by
    show 15 * 17 < 2 ^ 64
    decide
  rw [lcm_spec 15 17 h_no_ovf]
  apply congrArg RustM.ok
  apply UInt64.toNat_inj.mp
  have h_lt : (15 : u64).toNat * (17 : u64).toNat / Nat.gcd (15 : u64).toNat (17 : u64).toNat
              < 2 ^ 64 := by
    show 15 * 17 / Nat.gcd 15 17 < 2 ^ 64
    decide
  rw [UInt64.toNat_ofNat_of_lt' h_lt]
  decide

/-- `test_lcm_doc` case 1: `lcm(7, 3) = 21`. -/
theorem lcm_7_3 : lcm_u64.lcm 7 3 = RustM.ok 21 := by
  have h_no_ovf : (7 : u64).toNat * (3 : u64).toNat < 2 ^ 64 := by
    show 7 * 3 < 2 ^ 64
    decide
  rw [lcm_spec 7 3 h_no_ovf]
  apply congrArg RustM.ok
  apply UInt64.toNat_inj.mp
  have h_lt : (7 : u64).toNat * (3 : u64).toNat / Nat.gcd (7 : u64).toNat (3 : u64).toNat
              < 2 ^ 64 := by
    show 7 * 3 / Nat.gcd 7 3 < 2 ^ 64
    decide
  rw [UInt64.toNat_ofNat_of_lt' h_lt]
  decide

/-- `test_lcm_doc` case 2: `lcm(2, 4) = 4`. -/
theorem lcm_2_4 : lcm_u64.lcm 2 4 = RustM.ok 4 := by
  have h_no_ovf : (2 : u64).toNat * (4 : u64).toNat < 2 ^ 64 := by
    show 2 * 4 < 2 ^ 64
    decide
  rw [lcm_spec 2 4 h_no_ovf]
  apply congrArg RustM.ok
  apply UInt64.toNat_inj.mp
  have h_lt : (2 : u64).toNat * (4 : u64).toNat / Nat.gcd (2 : u64).toNat (4 : u64).toNat
              < 2 ^ 64 := by
    show 2 * 4 / Nat.gcd 2 4 < 2 ^ 64
    decide
  rw [UInt64.toNat_ofNat_of_lt' h_lt]
  decide

/-- `test_lcm_doc` case 3: `lcm(0, 0) = 0`. Boundary case — the function
short-circuits via `if x == 0 && y == 0 { return 0 }`. -/
theorem lcm_0_0 : lcm_u64.lcm 0 0 = RustM.ok 0 := by
  have h_no_ovf : (0 : u64).toNat * (0 : u64).toNat < 2 ^ 64 := by
    show 0 * 0 < 2 ^ 64
    decide
  rw [lcm_spec 0 0 h_no_ovf]
  apply congrArg RustM.ok
  apply UInt64.toNat_inj.mp
  have h_lt : (0 : u64).toNat * (0 : u64).toNat / Nat.gcd (0 : u64).toNat (0 : u64).toNat
              < 2 ^ 64 := by
    show 0 * 0 / Nat.gcd 0 0 < 2 ^ 64
    decide
  rw [UInt64.toNat_ofNat_of_lt' h_lt]
  decide

/-- `test_lcm_overflow` first assertion: `lcm(2^63, 2) = 2^63`.
Here `x * y = 2^64` overflows, but `x * (y / gcd) = 2^63 * 1 = 2^63` fits. -/
theorem lcm_overflow_xy :
    lcm_u64.lcm 0x8000000000000000 2 = RustM.ok 0x8000000000000000 := by
  -- 2 divides 0x8000000000000000.
  apply lcm_dvd_left
  · decide
  · decide
  · show (2 : u64).toNat ∣ (0x8000000000000000 : u64).toNat
    decide

/-- `test_lcm_overflow` symmetric assertion: `lcm(2, 2^63) = 2^63`. -/
theorem lcm_overflow_yx :
    lcm_u64.lcm 2 0x8000000000000000 = RustM.ok 0x8000000000000000 := by
  apply lcm_dvd_right
  · decide
  · decide
  · show (2 : u64).toNat ∣ (0x8000000000000000 : u64).toNat
    decide

/-- `prop_zero_is_absorbing`, left absorption: `lcm(0, y) = 0` for every `y`. -/
theorem lcm_zero_left (y : u64) : lcm_u64.lcm 0 y = RustM.ok 0 := by
  have h_no_ovf : (0 : u64).toNat * y.toNat < 2 ^ 64 := by
    have : (0 : u64).toNat = 0 := rfl
    rw [this, Nat.zero_mul]
    exact Nat.two_pow_pos _
  rw [lcm_spec 0 y h_no_ovf]
  apply congrArg RustM.ok
  apply UInt64.toNat_inj.mp
  have h_eq : (0 : u64).toNat * y.toNat / Nat.gcd (0 : u64).toNat y.toNat = 0 := by
    have h0 : (0 : u64).toNat = 0 := rfl
    rw [h0, Nat.zero_mul, Nat.zero_div]
  rw [UInt64.toNat_ofNat_of_lt' (by rw [h_eq]; decide), h_eq]
  rfl

/-- `prop_zero_is_absorbing`, right absorption: `lcm(x, 0) = 0` for every `x`. -/
theorem lcm_zero_right (x : u64) : lcm_u64.lcm x 0 = RustM.ok 0 := by
  have h_no_ovf : x.toNat * (0 : u64).toNat < 2 ^ 64 := by
    have : (0 : u64).toNat = 0 := rfl
    rw [this, Nat.mul_zero]
    exact Nat.two_pow_pos _
  rw [lcm_spec x 0 h_no_ovf]
  apply congrArg RustM.ok
  apply UInt64.toNat_inj.mp
  have h_eq : x.toNat * (0 : u64).toNat / Nat.gcd x.toNat (0 : u64).toNat = 0 := by
    have h0 : (0 : u64).toNat = 0 := rfl
    rw [h0, Nat.mul_zero, Nat.zero_div]
  rw [UInt64.toNat_ofNat_of_lt' (by rw [h_eq]; decide), h_eq]
  rfl

/-- Totality: under no-overflow, `lcm x y` returns an `ok` value. -/
theorem lcm_total (x y : u64) (h_no_ovf : x.toNat * y.toNat < 2 ^ 64) :
    ∃ l : u64, lcm_u64.lcm x y = RustM.ok l :=
  ⟨_, lcm_spec x y h_no_ovf⟩

/-- `prop_result_is_multiple_of_x`: the result is a multiple of `x`. -/
theorem lcm_multiple_of_x (x y : u64) (h_no_ovf : x.toNat * y.toNat < 2 ^ 64) :
    ∃ l : u64, lcm_u64.lcm x y = RustM.ok l ∧ x.toNat ∣ l.toNat := by
  refine ⟨_, lcm_spec x y h_no_ovf, ?_⟩
  -- l = ofNat (x.toNat * y.toNat / gcd). gcd ∣ y, so y = gcd * k, so
  -- x * y / gcd = x * k = x * (y/gcd), which is a multiple of x.
  have hg_dvd_y : Nat.gcd x.toNat y.toNat ∣ y.toNat := Nat.gcd_dvd_right _ _
  have h_xy_div : x.toNat * y.toNat / Nat.gcd x.toNat y.toNat
        = x.toNat * (y.toNat / Nat.gcd x.toNat y.toNat) :=
    Nat.mul_div_assoc x.toNat hg_dvd_y
  have h_yg_le_y : y.toNat / Nat.gcd x.toNat y.toNat ≤ y.toNat :=
    Nat.div_le_self _ _
  have h_prod_lt : x.toNat * (y.toNat / Nat.gcd x.toNat y.toNat) < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left x.toNat h_yg_le_y) h_no_ovf
  have h_lt : x.toNat * y.toNat / Nat.gcd x.toNat y.toNat < 2 ^ 64 := by
    rw [h_xy_div]; exact h_prod_lt
  rw [UInt64.toNat_ofNat_of_lt' h_lt, h_xy_div]
  exact Nat.dvd_mul_right _ _

/-- `prop_result_is_multiple_of_y`: the result is a multiple of `y`. -/
theorem lcm_multiple_of_y (x y : u64) (h_no_ovf : x.toNat * y.toNat < 2 ^ 64) :
    ∃ l : u64, lcm_u64.lcm x y = RustM.ok l ∧ y.toNat ∣ l.toNat := by
  refine ⟨_, lcm_spec x y h_no_ovf, ?_⟩
  -- l.toNat = x.toNat * y.toNat / gcd. gcd ∣ x, so x = gcd * j, so
  -- x * y / gcd = j * y, which is a multiple of y.
  have hg_dvd_x : Nat.gcd x.toNat y.toNat ∣ x.toNat := Nat.gcd_dvd_left _ _
  -- Rewrite x * y / gcd as (x/gcd) * y.
  have h_xy_div_y : x.toNat * y.toNat / Nat.gcd x.toNat y.toNat
        = (x.toNat / Nat.gcd x.toNat y.toNat) * y.toNat := by
    rw [Nat.mul_comm x.toNat y.toNat]
    rw [Nat.mul_div_assoc y.toNat hg_dvd_x]
    rw [Nat.mul_comm]
  have h_xg_le_x : x.toNat / Nat.gcd x.toNat y.toNat ≤ x.toNat :=
    Nat.div_le_self _ _
  have h_prod_lt : (x.toNat / Nat.gcd x.toNat y.toNat) * y.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right y.toNat h_xg_le_x) h_no_ovf
  have h_lt : x.toNat * y.toNat / Nat.gcd x.toNat y.toNat < 2 ^ 64 := by
    rw [h_xy_div_y]; exact h_prod_lt
  rw [UInt64.toNat_ofNat_of_lt' h_lt, h_xy_div_y]
  exact Nat.dvd_mul_left _ _

/-- `prop_result_is_least_common_multiple`: when both inputs are positive,
the result is the *least* positive common multiple — no smaller positive
integer is divisible by both `x` and `y`. -/
theorem lcm_least (x y : u64) (hx : 0 < x.toNat) (hy : 0 < y.toNat)
    (h_no_ovf : x.toNat * y.toNat < 2 ^ 64) :
    ∃ l : u64, lcm_u64.lcm x y = RustM.ok l ∧
      ∀ z : Nat, 0 < z → z < l.toNat → ¬ (x.toNat ∣ z ∧ y.toNat ∣ z) := by
  refine ⟨_, lcm_spec x y h_no_ovf, ?_⟩
  intro z hz_pos hz_lt ⟨hzx, hzy⟩
  -- l.toNat = x.toNat * y.toNat / Nat.gcd x.toNat y.toNat = Nat.lcm x.toNat y.toNat.
  -- z is a positive common multiple smaller than the standard Nat.lcm — contradiction.
  have hg_dvd_y : Nat.gcd x.toNat y.toNat ∣ y.toNat := Nat.gcd_dvd_right _ _
  have h_xy_div : x.toNat * y.toNat / Nat.gcd x.toNat y.toNat
        = x.toNat * (y.toNat / Nat.gcd x.toNat y.toNat) :=
    Nat.mul_div_assoc x.toNat hg_dvd_y
  have h_yg_le_y : y.toNat / Nat.gcd x.toNat y.toNat ≤ y.toNat :=
    Nat.div_le_self _ _
  have h_prod_lt : x.toNat * (y.toNat / Nat.gcd x.toNat y.toNat) < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left x.toNat h_yg_le_y) h_no_ovf
  have h_lt : x.toNat * y.toNat / Nat.gcd x.toNat y.toNat < 2 ^ 64 := by
    rw [h_xy_div]; exact h_prod_lt
  have h_l_eq : (UInt64.ofNat (x.toNat * y.toNat / Nat.gcd x.toNat y.toNat)).toNat
                = x.toNat * y.toNat / Nat.gcd x.toNat y.toNat :=
    UInt64.toNat_ofNat_of_lt' h_lt
  rw [h_l_eq] at hz_lt
  -- Now show x.toNat * y.toNat / gcd = Nat.lcm x.toNat y.toNat.
  have h_l_eq_lcm : x.toNat * y.toNat / Nat.gcd x.toNat y.toNat
                    = Nat.lcm x.toNat y.toNat := by
    unfold Nat.lcm
    rfl
  rw [h_l_eq_lcm] at hz_lt
  -- The minimality of Nat.lcm: any positive common multiple of x and y is ≥ Nat.lcm x y.
  have hlcm_le : Nat.lcm x.toNat y.toNat ∣ z := Nat.lcm_dvd hzx hzy
  have hlcm_pos : 0 < Nat.lcm x.toNat y.toNat := by
    have := Nat.lcm_pos hx hy
    exact this
  have h_ge : Nat.lcm x.toNat y.toNat ≤ z := Nat.le_of_dvd hz_pos hlcm_le
  omega

end Lcm_u64Obligations
