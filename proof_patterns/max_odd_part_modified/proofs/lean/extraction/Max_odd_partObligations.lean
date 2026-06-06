-- Companion obligations file for the `max_odd_part` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import max_odd_part

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Max_odd_partObligations

open rust_primitives.hax (Tuple2)

/-! ## Helpers. -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

/-! ## Trailing zeros: invariant + body step (mirrors `trailing_zeros_u64_modified`). -/

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

private theorem tz_function_zero :
    max_odd_part.trailing_zeros_u64 (0 : u64) = RustM.ok (64 : u32) := by
  unfold max_odd_part.trailing_zeros_u64
  rfl

private theorem tz_function_nonzero_triple (x : u64) (hx : x ≠ 0) :
    ⦃⌜ True ⌝⦄
      max_odd_part.trailing_zeros_u64 x
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
  unfold max_odd_part.trailing_zeros_u64
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

/-- Existential closed-form for `trailing_zeros_u64` on nonzero input. -/
private theorem tz_nonzero_spec (x : u64) (hx : x ≠ 0) :
    ∃ r : u32, max_odd_part.trailing_zeros_u64 x = RustM.ok r ∧
                r.toNat < 64 ∧
                2 ^ r.toNat ∣ x.toNat ∧
                (x.toNat >>> r.toNat) &&& 1 = 1 := by
  have h := tz_function_nonzero_triple x hx
  rw [RustM.Triple_iff_BitVec] at h
  simp only [decide_true, Bool.not_true, Bool.false_or,
             Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hok, hpost⟩ := h
  cases hf : max_odd_part.trailing_zeros_u64 x with
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

/-! ## Outer loop: `max_odd_part` infrastructure. -/

/-- Invariant for the outer loop on state `⟨best, i⟩`. Carries the full
    contract surface: range of `i`, bound on `best`, an existence disjunct
    (initial state with `best = 0` or witnessed by a previous index `j < i`
    whose odd-part equals `best`), and an upper bound. -/
private def moInv (n : u64) (s : Tuple2 u64 u64) : Prop :=
  1 ≤ s._1.toNat ∧
  s._1.toNat ≤ n.toNat + 1 ∧
  s._0.toNat ≤ n.toNat ∧
  ((s._1.toNat = 1 ∧ s._0.toNat = 0) ∨
   (s._0.toNat % 2 = 1 ∧
    ∃ (j : u64) (k : u32),
      1 ≤ j.toNat ∧ j.toNat < s._1.toNat ∧
      max_odd_part.trailing_zeros_u64 j = RustM.ok k ∧
      s._0.toNat = j.toNat >>> k.toNat)) ∧
  (∀ (j : u64) (k : u32),
    1 ≤ j.toNat → j.toNat < s._1.toNat →
    max_odd_part.trailing_zeros_u64 j = RustM.ok k →
    j.toNat >>> k.toNat ≤ s._0.toNat)

private def moTerm (n : u64) (s : Tuple2 u64 u64) : Nat :=
  n.toNat + 1 - s._1.toNat

private abbrev moCond (n : u64) : Tuple2 u64 u64 → Bool :=
  fun b => decide (UInt64.toNat b._1 ≤ UInt64.toNat n)

private abbrev moBody : Tuple2 u64 u64 → RustM (Tuple2 u64 u64) :=
  fun x =>
    match x with
    | ⟨best, i⟩ =>
      (do
        let r : u32 ← (max_odd_part.trailing_zeros_u64 i)
        let odd : u64 ← (i >>>? r)
        let best : u64 ←
          if (← (odd >? best)) then do
            let best : u64 := odd
            (pure best)
          else do
            (pure best)
        let i : u64 ← (i +? (1 : u64))
        (pure (rust_primitives.hax.Tuple2.mk best i)) :
        RustM (rust_primitives.hax.Tuple2 u64 u64))

private abbrev moLoop (n : u64) : RustM (Tuple2 u64 u64) :=
  Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk (moCond n)
    (rust_primitives.hax.Tuple2.mk (0 : u64) (1 : u64)) moBody

/-! ## Body computation: equational form via the trailing-zeros spec. -/

/-- For `1 ≤ i` and `i + 1` not overflowing `u64`, the body of `max_odd_part`
    computes to `RustM.ok ⟨new_best, i + 1⟩`, where `new_best` is the max of
    `best` and the odd part of `i`. Carries the trailing-zeros postcondition
    as witness so the body step can use it. -/
private theorem mo_body_eq (best i : u64) (hi_ge_1 : 1 ≤ i.toNat)
    (h_i_add_ok : i.toNat + 1 < 2 ^ 64) :
    ∃ (r : u32),
      max_odd_part.trailing_zeros_u64 i = RustM.ok r ∧
      r.toNat < 64 ∧
      2 ^ r.toNat ∣ i.toNat ∧
      (i.toNat >>> r.toNat) &&& 1 = 1 ∧
      moBody ⟨best, i⟩ = (pure
        ⟨(if (i >>> r.toNat.toUInt64) > best then i >>> r.toNat.toUInt64 else best),
         i + 1⟩ : RustM (Tuple2 u64 u64)) := by
  have hi_ne_0 : i ≠ 0 := fun h => by
    have : i.toNat = 0 := by rw [h]; rfl
    omega
  obtain ⟨r, h_tz_ok, h_r_lt_64, h_dvd, h_odd_bit⟩ := tz_nonzero_spec i hi_ne_0
  -- The shift evaluates to pure (i >>> r.toNat.toUInt64).
  have h_0_le_r : ((0 : UInt32) ≤ r) := by
    rw [UInt32.le_iff_toNat_le]
    show (0 : UInt32).toNat ≤ r.toNat
    rw [show ((0 : UInt32).toNat) = 0 from rfl]
    exact Nat.zero_le _
  have h_r_lt_64_b : r < (64 : UInt32) := by
    rw [UInt32.lt_iff_toNat_lt]
    show r.toNat < (64 : UInt32).toNat
    have h64 : (64 : UInt32).toNat = 64 := rfl
    omega
  have h_shr : (i >>>? r : RustM u64) = RustM.ok (i >>> r.toNat.toUInt64) := by
    show (rust_primitives.ops.bit.Shr.shr i r : RustM u64) =
         RustM.ok (i >>> r.toNat.toUInt64)
    show (if ((0 : UInt32) ≤ r && r < (64 : UInt32)) then
            pure (i >>> r.toNat.toUInt64)
          else .fail .integerOverflow) = RustM.ok (i >>> r.toNat.toUInt64)
    have h_cond_eq : ((0 : UInt32) ≤ r && r < (64 : UInt32)) = true := by
      simp [h_0_le_r, h_r_lt_64_b]
    rw [h_cond_eq]; rfl
  -- The increment evaluates to pure (i + 1).
  have h_add : (i +? (1 : u64) : RustM u64) = RustM.ok (i + 1) := by
    show (rust_primitives.ops.arith.Add.add i (1 : u64) : RustM u64) = RustM.ok (i + 1)
    show (if BitVec.uaddOverflow i.toBitVec (1 : u64).toBitVec then
            (.fail .integerOverflow : RustM u64)
          else pure (i + 1)) = RustM.ok (i + 1)
    have h_no_ovf : BitVec.uaddOverflow i.toBitVec ((1 : u64).toBitVec) = false := by
      cases hb : BitVec.uaddOverflow i.toBitVec ((1 : u64).toBitVec) with
      | false => rfl
      | true =>
        exfalso
        have h : UInt64.addOverflow i (1 : u64) = true := hb
        rw [UInt64.addOverflow_iff] at h
        have h1 : (1 : UInt64).toNat = 1 := rfl
        rw [h1] at h; omega
    rw [h_no_ovf]; rfl
  refine ⟨r, h_tz_ok, h_r_lt_64, h_dvd, h_odd_bit, ?_⟩
  -- Compute the body
  dsimp only [moBody]
  rw [h_tz_ok]
  simp only [RustM_ok_bind]
  rw [h_shr]
  simp only [RustM_ok_bind]
  -- After the rewrites the goal has the form:
  --   (do let b ← (odd >? best);
  --       if b = true then (do let y ← pure odd; let i ← i+?1; pure ⟨y, i⟩)
  --                    else (do let y ← pure best; let i ← i+?1; pure ⟨y, i⟩))
  --   = RustM.ok ⟨(if odd > best then odd else best), i + 1⟩
  -- The cmp.gt unfolds to `pure (decide (odd > best))`.
  have h_cmp : ((i >>> r.toNat.toUInt64) >? best : RustM Bool) =
               pure (decide ((i >>> r.toNat.toUInt64) > best)) := rfl
  rw [h_cmp]
  simp only [pure_bind]
  by_cases hgt : (i >>> r.toNat.toUInt64) > best
  · have h_dec_true : decide ((i >>> r.toNat.toUInt64) > best) = true := decide_eq_true hgt
    rw [h_dec_true]
    simp only [if_true]
    rw [h_add]
    simp only [RustM_ok_bind]
    rw [if_pos hgt]
  · have h_dec_false : decide ((i >>> r.toNat.toUInt64) > best) = false := decide_eq_false hgt
    rw [h_dec_false]
    simp only [Bool.false_eq_true, if_false]
    rw [h_add]
    simp only [RustM_ok_bind]
    rw [if_neg hgt]

/-! ## Outer loop: Hoare triple. -/

private theorem mo_loop_triple (n : u64) (hn_max : n.toNat < 2 ^ 64 - 1) :
    ⦃⌜ moInv n ⟨(0 : u64), (1 : u64)⟩ ⌝⦄
      moLoop n
    ⦃⇓ r => ⌜ moInv n r ∧ ¬ moCond n r = true ⌝⦄ := by
  apply Std.Do.Spec.MonoLoopCombinator.while_loop
    (rust_primitives.hax.Tuple2.mk (0 : u64) (1 : u64)) Lean.Loop.mk
    (moCond n) moBody (moInv n) (moTerm n)
  intro s hcond hinv
  cases s with
  | mk best i =>
    have hinv' := hinv
    unfold moInv at hinv'
    simp only at hinv'
    obtain ⟨hi_ge_1, hi_le_n1, hbest_le_n, hexist, hub⟩ := hinv'
    have hi_le_n : i.toNat ≤ n.toNat := by
      have h : decide (UInt64.toNat i ≤ UInt64.toNat n) = true := hcond
      exact decide_eq_true_iff.mp h
    have h_i_add : i.toNat + 1 < 2 ^ 64 := by omega
    obtain ⟨r, h_tz_ok, h_r_lt_64, h_dvd, h_odd_bit, h_body_eq⟩ :=
      mo_body_eq best i hi_ge_1 h_i_add
    have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := by
      apply UInt64.toNat_add_of_lt
      show i.toNat + (1 : UInt64).toNat < 2 ^ 64
      have : (1 : UInt64).toNat = 1 := rfl
      omega
    have h_r_lt_2_64 : r.toNat < 2 ^ 64 := by
      have h32 : r.toNat < 2 ^ 32 := UInt32.toNat_lt r
      omega
    have h_r_uint64_toNat : (r.toNat.toUInt64).toNat = r.toNat :=
      UInt64.toNat_ofNat_of_lt' h_r_lt_2_64
    have h_odd_toNat : (i >>> r.toNat.toUInt64).toNat = i.toNat >>> r.toNat := by
      rw [UInt64.toNat_shiftRight, h_r_uint64_toNat, Nat.mod_eq_of_lt h_r_lt_64]
    -- odd ≥ 1 (since i ≥ 1 and 2^r ∣ i implies i ≥ 2^r, so i / 2^r ≥ 1)
    have h_odd_ge_1 : 1 ≤ (i >>> r.toNat.toUInt64).toNat := by
      rw [h_odd_toNat, Nat.shiftRight_eq_div_pow]
      have h_pow_pos : 0 < 2 ^ r.toNat := Nat.two_pow_pos r.toNat
      rcases h_dvd with ⟨c, hc⟩
      have h_c_pos : 1 ≤ c := by
        rcases Nat.eq_zero_or_pos c with h | h
        · exfalso; rw [h, Nat.mul_zero] at hc; omega
        · exact h
      rw [hc, Nat.mul_div_cancel_left _ h_pow_pos]
      exact h_c_pos
    have h_odd_le_n : (i >>> r.toNat.toUInt64).toNat ≤ n.toNat := by
      rw [h_odd_toNat, Nat.shiftRight_eq_div_pow]
      exact Nat.le_trans (Nat.div_le_self _ _) hi_le_n
    have h_odd_isodd : (i >>> r.toNat.toUInt64).toNat % 2 = 1 := by
      rw [h_odd_toNat]
      rw [← Nat.and_one_is_mod]
      exact h_odd_bit
    -- Apply body equation, case on `odd > best`
    rw [h_body_eq]
    by_cases hgt : (i >>> r.toNat.toUInt64) > best
    · -- Case 1: odd > best; new_best = odd
      rw [if_pos hgt]
      refine ⟨?_, ?_⟩
      · -- term decreases
        show n.toNat + 1 - (i + 1).toNat < n.toNat + 1 - i.toNat
        rw [h_i1_toNat]; omega
      · -- inv preserved
        refine ⟨?_, ?_, h_odd_le_n, ?_, ?_⟩
        · show 1 ≤ (i + 1).toNat
          rw [h_i1_toNat]; omega
        · show (i + 1).toNat ≤ n.toNat + 1
          rw [h_i1_toNat]; omega
        · -- right disjunct
          right
          refine ⟨h_odd_isodd, i, r, hi_ge_1, ?_, h_tz_ok, h_odd_toNat⟩
          rw [h_i1_toNat]; omega
        · -- upper bound
          intro j k hj_ge hj_lt h_tz_j
          rw [h_i1_toNat] at hj_lt
          show j.toNat >>> k.toNat ≤ (i >>> r.toNat.toUInt64).toNat
          rcases Nat.lt_or_ge j.toNat i.toNat with h_jlt | h_jge
          · -- j.toNat < i.toNat: use old upper bound, then ≤ best < odd
            have h_le_old := hub j k hj_ge h_jlt h_tz_j
            have h_lt : best.toNat < (i >>> r.toNat.toUInt64).toNat :=
              UInt64.lt_iff_toNat_lt.mp hgt
            omega
          · -- j.toNat = i.toNat
            have h_jeq : j.toNat = i.toNat := by omega
            have h_j_eq_i : j = i := UInt64.toNat_inj.mp h_jeq
            subst h_j_eq_i
            have h_eq : RustM.ok k = (RustM.ok r : RustM u32) := by
              rw [← h_tz_j, h_tz_ok]
            have h_k_eq_r : k = r := by
              have h1 : (Except.ok k : Except Error u32) = Except.ok r :=
                Option.some.inj h_eq
              exact Except.ok.inj h1
            subst h_k_eq_r
            -- After substs, all r's became k's, i's became j's
            rw [h_odd_toNat]
            exact Nat.le_refl _
    · -- Case 2: odd ≤ best; new_best = best
      rw [if_neg hgt]
      refine ⟨?_, ?_⟩
      · show n.toNat + 1 - (i + 1).toNat < n.toNat + 1 - i.toNat
        rw [h_i1_toNat]; omega
      · refine ⟨?_, ?_, hbest_le_n, ?_, ?_⟩
        · show 1 ≤ (i + 1).toNat
          rw [h_i1_toNat]; omega
        · show (i + 1).toNat ≤ n.toNat + 1
          rw [h_i1_toNat]; omega
        · -- right disjunct (since i+1 ≥ 2)
          rcases hexist with ⟨_, hbest_eq_0⟩ | ⟨hbest_odd, j, k, hj_ge, hj_lt, h_tz_j, hbest_eq⟩
          · -- initial state ⟨0, 1⟩. odd ≥ 1, best = 0, so odd > best — contradicts hgt.
            exfalso
            apply hgt
            show best < (i >>> r.toNat.toUInt64)
            rw [UInt64.lt_iff_toNat_lt]
            show best.toNat < (i >>> r.toNat.toUInt64).toNat
            omega
          · right
            refine ⟨hbest_odd, j, k, hj_ge, ?_, h_tz_j, hbest_eq⟩
            rw [h_i1_toNat]; omega
        · -- upper bound
          intro j k hj_ge hj_lt h_tz_j
          rw [h_i1_toNat] at hj_lt
          show j.toNat >>> k.toNat ≤ best.toNat
          rcases Nat.lt_or_ge j.toNat i.toNat with h_jlt | h_jge
          · exact hub j k hj_ge h_jlt h_tz_j
          · have h_jeq : j.toNat = i.toNat := by omega
            have h_j_eq_i : j = i := UInt64.toNat_inj.mp h_jeq
            subst h_j_eq_i
            have h_eq : RustM.ok k = (RustM.ok r : RustM u32) := by
              rw [← h_tz_j, h_tz_ok]
            have h_k_eq_r : k = r := by
              have h1 : (Except.ok k : Except Error u32) = Except.ok r :=
                Option.some.inj h_eq
              exact Except.ok.inj h1
            subst h_k_eq_r
            -- Now r is gone; everything uses k. h_odd_toNat is on k.
            have h_not_lt : ¬ best.toNat < (j >>> k.toNat.toUInt64).toNat := by
              intro h_lt
              apply hgt
              show best < (j >>> k.toNat.toUInt64)
              rw [UInt64.lt_iff_toNat_lt]
              exact h_lt
            have h_odd_le_best : (j >>> k.toNat.toUInt64).toNat ≤ best.toNat :=
              Nat.le_of_not_lt h_not_lt
            rw [h_odd_toNat] at h_odd_le_best
            exact h_odd_le_best

/-! ## Function-level triple and master existential. -/

private theorem mo_function_triple (n : u64) (hn_max : n.toNat < 2 ^ 64 - 1) :
    ⦃⌜ True ⌝⦄
      max_odd_part.max_odd_part n
    ⦃⇓ r => ⌜
      r.toNat ≤ n.toNat ∧
      ((n.toNat = 0 ∧ r.toNat = 0) ∨
       (r.toNat % 2 = 1 ∧
        ∃ (j : u64) (k : u32),
          1 ≤ j.toNat ∧ j.toNat ≤ n.toNat ∧
          max_odd_part.trailing_zeros_u64 j = RustM.ok k ∧
          r.toNat = j.toNat >>> k.toNat)) ∧
      (∀ (j : u64) (k : u32),
        1 ≤ j.toNat → j.toNat ≤ n.toNat →
        max_odd_part.trailing_zeros_u64 j = RustM.ok k →
        j.toNat >>> k.toNat ≤ r.toNat)
    ⌝⦄ := by
  have h_loop := mo_loop_triple n hn_max
  -- Project the loop's postcondition to the desired form on best (= s._0)
  have h_loop' :
      ⦃⌜ moInv n ⟨(0 : u64), (1 : u64)⟩ ⌝⦄
        moLoop n
      ⦃⇓ r => ⌜
        r._0.toNat ≤ n.toNat ∧
        ((n.toNat = 0 ∧ r._0.toNat = 0) ∨
         (r._0.toNat % 2 = 1 ∧
          ∃ (j : u64) (k : u32),
            1 ≤ j.toNat ∧ j.toNat ≤ n.toNat ∧
            max_odd_part.trailing_zeros_u64 j = RustM.ok k ∧
            r._0.toNat = j.toNat >>> k.toNat)) ∧
        (∀ (j : u64) (k : u32),
          1 ≤ j.toNat → j.toNat ≤ n.toNat →
          max_odd_part.trailing_zeros_u64 j = RustM.ok k →
          j.toNat >>> k.toNat ≤ r._0.toNat)
      ⌝⦄ := by
    apply Triple.of_entails_right _ _ _ _ h_loop
    apply PostCond.entails.of_left_entails
    intro r ⟨hinv, hncond⟩
    have hi_gt_n : n.toNat < r._1.toNat := by
      have h : ¬ decide (UInt64.toNat r._1 ≤ UInt64.toNat n) = true := hncond
      rw [decide_eq_true_iff] at h
      omega
    unfold moInv at hinv
    obtain ⟨hi_ge_1, hi_le_n1, hbest_le_n, hexist, hub⟩ := hinv
    have hi_eq : r._1.toNat = n.toNat + 1 := by omega
    refine ⟨hbest_le_n, ?_, ?_⟩
    · rcases hexist with ⟨hi_eq_1, hbest_eq_0⟩ | ⟨hbest_odd, j, k, hj_ge, hj_lt, h_tz_j, hbest_eq⟩
      · -- initial state, i = 1 = n + 1, so n = 0
        left
        refine ⟨?_, hbest_eq_0⟩
        omega
      · right
        refine ⟨hbest_odd, j, k, hj_ge, ?_, h_tz_j, hbest_eq⟩
        omega
    · intro j k hj_ge hj_le_n h_tz_j
      apply hub j k hj_ge ?_ h_tz_j
      omega
  -- Weaken precond: True → moInv n ⟨0, 1⟩
  have h_loop'' :
      ⦃⌜ True ⌝⦄
        moLoop n
      ⦃⇓ r => ⌜
        r._0.toNat ≤ n.toNat ∧
        ((n.toNat = 0 ∧ r._0.toNat = 0) ∨
         (r._0.toNat % 2 = 1 ∧
          ∃ (j : u64) (k : u32),
            1 ≤ j.toNat ∧ j.toNat ≤ n.toNat ∧
            max_odd_part.trailing_zeros_u64 j = RustM.ok k ∧
            r._0.toNat = j.toNat >>> k.toNat)) ∧
        (∀ (j : u64) (k : u32),
          1 ≤ j.toNat → j.toNat ≤ n.toNat →
          max_odd_part.trailing_zeros_u64 j = RustM.ok k →
          j.toNat >>> k.toNat ≤ r._0.toNat)
      ⌝⦄ := by
    apply Triple.of_entails_left _ _ _ _ h_loop'
    intro _
    show moInv n ⟨(0 : u64), (1 : u64)⟩
    have h0 : (0 : u64).toNat = 0 := rfl
    have h1 : (1 : u64).toNat = 1 := rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show 1 ≤ (1 : u64).toNat
      rw [h1]; omega
    · show (1 : u64).toNat ≤ n.toNat + 1
      rw [h1]; omega
    · show (0 : u64).toNat ≤ n.toNat
      rw [h0]; omega
    · left
      refine ⟨h1, h0⟩
    · intro j k hj_ge hj_lt h_tz_j
      rw [h1] at hj_lt
      omega
  -- Reformulate the function as a bind on moLoop.
  unfold max_odd_part.max_odd_part
  unfold rust_primitives.hax.while_loop
  apply Triple.bind _ _ h_loop''
  intro s
  cases s with
  | mk b i =>
    refine Triple.pure b ?_
    intro h
    exact h

/-- Master existential spec for `max_odd_part`. Uses `Classical.propDecidable`
    to give a `Decidable` instance for the postcondition (which contains
    existentials/universals over `u64`). -/
private theorem mo_master_spec (n : u64) (hn_max : n.toNat < 2 ^ 64 - 1) :
    ∃ r : u64,
      max_odd_part.max_odd_part n = RustM.ok r ∧
      r.toNat ≤ n.toNat ∧
      ((n.toNat = 0 ∧ r.toNat = 0) ∨
       (r.toNat % 2 = 1 ∧
        ∃ (j : u64) (k : u32),
          1 ≤ j.toNat ∧ j.toNat ≤ n.toNat ∧
          max_odd_part.trailing_zeros_u64 j = RustM.ok k ∧
          r.toNat = j.toNat >>> k.toNat)) ∧
      (∀ (j : u64) (k : u32),
        1 ≤ j.toNat → j.toNat ≤ n.toNat →
        max_odd_part.trailing_zeros_u64 j = RustM.ok k →
        j.toNat >>> k.toNat ≤ r.toNat) := by
  classical
  have h := mo_function_triple n hn_max
  rw [RustM.Triple_iff_BitVec] at h
  simp only [decide_true, Bool.not_true, Bool.false_or,
             Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hok, hpost⟩ := h
  cases hf : max_odd_part.max_odd_part n with
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

/-! ## Obligations (proven by projection from the master spec). -/

/-- `max_odd_part(0) = 0`. -/
theorem max_odd_part_zero :
    max_odd_part.max_odd_part 0 = RustM.ok 0 := by
  obtain ⟨r, hres, hbound, _, _⟩ := mo_master_spec 0 (by decide)
  have hr_zero : r = 0 := by
    apply UInt64.toNat_inj.mp
    show r.toNat = (0 : u64).toNat
    have h0 : (0 : u64).toNat = 0 := rfl
    have : r.toNat ≤ (0 : u64).toNat := by rw [h0]; exact hbound
    omega
  rw [hres, hr_zero]

/-- Totality. -/
theorem max_odd_part_total (n : u64) (hn : n.toNat < 2 ^ 64 - 1) :
    ∃ r : u64, max_odd_part.max_odd_part n = RustM.ok r := by
  obtain ⟨r, hres, _, _, _⟩ := mo_master_spec n hn
  exact ⟨r, hres⟩

/-- Bound clause. -/
theorem max_odd_part_bound (n : u64) (hn : n.toNat < 2 ^ 64 - 1) :
    ∃ r : u64,
      max_odd_part.max_odd_part n = RustM.ok r ∧ r.toNat ≤ n.toNat := by
  obtain ⟨r, hres, hbound, _, _⟩ := mo_master_spec n hn
  exact ⟨r, hres, hbound⟩

/-- Oddness clause. -/
theorem max_odd_part_odd (n : u64)
    (hn_pos : 1 ≤ n.toNat) (hn_max : n.toNat < 2 ^ 64 - 1) :
    ∃ r : u64,
      max_odd_part.max_odd_part n = RustM.ok r ∧ r.toNat % 2 = 1 := by
  obtain ⟨r, hres, _, hdisj, _⟩ := mo_master_spec n hn_max
  refine ⟨r, hres, ?_⟩
  rcases hdisj with ⟨hn_eq, _⟩ | ⟨hodd, _⟩
  · -- n = 0 contradicts hn_pos
    omega
  · exact hodd

/-- Maximality existence half. -/
theorem max_odd_part_achievable (n : u64)
    (hn_pos : 1 ≤ n.toNat) (hn_max : n.toNat < 2 ^ 64 - 1) :
    ∃ r : u64,
      max_odd_part.max_odd_part n = RustM.ok r ∧
      ∃ (i : u64) (k : u32),
        1 ≤ i.toNat ∧ i.toNat ≤ n.toNat ∧
        max_odd_part.trailing_zeros_u64 i = RustM.ok k ∧
        r.toNat = i.toNat >>> k.toNat := by
  obtain ⟨r, hres, _, hdisj, _⟩ := mo_master_spec n hn_max
  refine ⟨r, hres, ?_⟩
  rcases hdisj with ⟨hn_eq, _⟩ | ⟨_, j, k, hj_ge, hj_le, h_tz, hr_eq⟩
  · -- n = 0 contradicts hn_pos
    omega
  · exact ⟨j, k, hj_ge, hj_le, h_tz, hr_eq⟩

/-- Maximality upper-bound half. -/
theorem max_odd_part_upper_bound (n : u64) (hn_max : n.toNat < 2 ^ 64 - 1) :
    ∃ r : u64,
      max_odd_part.max_odd_part n = RustM.ok r ∧
      ∀ (i : u64) (k : u32),
        1 ≤ i.toNat → i.toNat ≤ n.toNat →
        max_odd_part.trailing_zeros_u64 i = RustM.ok k →
        i.toNat >>> k.toNat ≤ r.toNat := by
  obtain ⟨r, hres, _, _, hub⟩ := mo_master_spec n hn_max
  exact ⟨r, hres, hub⟩

end Max_odd_partObligations
