-- Companion obligations file for the `trailing_zeros_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import trailing_zeros_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Trailing_zeros_u64Obligations

open rust_primitives.hax (Tuple2)

/-! ## Loop infrastructure

Canonical two-stage proof from `while_example/README.md`: prove a Hoare triple
over the underlying `Loop.MonoLoopCombinator.while_loop`, then convert to an
equation via `RustM.Triple_iff_BitVec`.

The strong invariant is `x₀.toNat = y.toNat * 2 ^ count.toNat ∧ 0 < y.toNat ∧
count.toNat < 64`, preserved by `(count, y) ↦ (count + 1, y >>> 1)` whenever the
condition `y &&& 1 == 0` holds (i.e. `y` is even). -/

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

/-! ## Body step lemma

The body fires when `y &&& 1 = 0` (i.e. `y` is even). Under the invariant
(`x₀ = y * 2 ^ count`, `y > 0`, `count < 64`), the body computes
`pure ⟨count + 1, y >>> 1⟩` (no shift fail, no add overflow), termination
strictly decreases (`(y >>> 1).toNat < y.toNat` since `y ≥ 2`), and the
invariant is preserved. -/

private theorem body_step_nat (x₀ : u64) (c : u32) (y : u64)
    (hinv : tzInv x₀ ⟨c, y⟩) (hcond : tzCond ⟨c, y⟩ = true) :
    -- (1) no add overflow: c + 1 doesn't overflow u32
    c.toNat + 1 < 2 ^ 32 ∧
    -- (2) termination decreases
    (y >>> (1 : UInt64)).toNat < y.toNat ∧
    -- (3) invariant preserved on (c + 1, y >>> 1)
    tzInv x₀ ⟨c + 1, y >>> (1 : UInt64)⟩ := by
  unfold tzInv at hinv
  simp only at hinv
  obtain ⟨hx, hy_pos, hc_lt⟩ := hinv
  -- From hcond: (y &&& 1).toNat == 0, so y is even.
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
    rw [← Nat.and_one_is_mod]
    exact this
  -- y ≥ 2 (since y > 0 and even)
  have h_y_ge_2 : y.toNat ≥ 2 := by omega
  -- (1) no add overflow: c + 1 < 2 ^ 32. We have c < 64 < 2^32.
  refine ⟨by omega, ?_, ?_⟩
  · -- (2) termination strictly decreases:
    -- (y >>> 1).toNat = y.toNat / 2 < y.toNat (since y ≥ 2 > 0)
    rw [UInt64.toNat_shiftRight, UInt64.toNat_one]
    show y.toNat >>> (1 % 64) < y.toNat
    rw [show (1 % 64 : Nat) = 1 from rfl, Nat.shiftRight_eq_div_pow,
        show (2 ^ 1 : Nat) = 2 from rfl]
    exact Nat.div_lt_self (by omega) (by decide)
  · -- (3) invariant preservation
    -- First we'll need (c + 1).toNat = c.toNat + 1.
    have h_cplus : (c + (1 : u32)).toNat = c.toNat + 1 := by
      apply UInt32.toNat_add_of_lt
      have h1 : (1 : UInt32).toNat = 1 := rfl
      rw [h1]
      omega
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
        rw [h_x_eq]
        exact Nat.le_mul_of_pos_left _ h_new_y_pos
      have h_pow_lt : 2 ^ (c.toNat + 1) < 2 ^ 64 :=
        Nat.lt_of_le_of_lt h_pow_le h_x_lt
      exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h_pow_lt
    refine ⟨?_, ?_, ?_⟩
    · -- x₀.toNat = (y >>> 1).toNat * 2 ^ (c + 1).toNat
      show x₀.toNat = (y >>> (1 : UInt64)).toNat * 2 ^ (c + (1 : u32)).toNat
      rw [h_yshr, h_cplus]
      exact h_x_eq
    · show 0 < (y >>> (1 : UInt64)).toNat
      rw [h_yshr]
      exact h_new_y_pos
    · show (c + (1 : u32)).toNat < 64
      rw [h_cplus]
      exact h_cplus_lt_64

/-! ## Stage 1: Hoare triple for the loop -/

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
    -- Pull out body step facts
    have hstep := body_step_nat x₀ c y hinv hcond
    obtain ⟨h_no_add_ovf, h_term_dec, h_inv'⟩ := hstep
    -- Reduce `y >>>? (1 : i32)` to `pure (y >>> 1)`.
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
    -- Reduce `c +? (1 : u32)` to `pure (c + 1)` using no-overflow.
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
          rw [h1] at this
          omega
      rw [h_no_ovf]
      rfl
    -- The body unfolds to: do let y ← y >>>? 1; let c ← c +? 1; pure ⟨c, y⟩.
    dsimp only [tzBody]
    rw [h_shr]
    simp only [pure_bind]
    rw [h_add]
    simp only [pure_bind]
    -- Now the body result is `pure ⟨c + 1, y >>> 1⟩`.
    -- wp ⟦pure ⟨c+1, y >>> 1⟩⟧ Q reduces to Q ⟨c+1, y >>> 1⟩.
    refine ⟨?_, h_inv'⟩
    show tzTerm ⟨c + 1, y >>> 1⟩ < tzTerm ⟨c, y⟩
    show (y >>> (1 : UInt64)).toNat < y.toNat
    exact h_term_dec

/-! ## Zero-input case -/

/-- Zero-input convention: by spec, `trailing_zeros_u64(0) = 64`. This is the
    `known_values` test's first case and the early-return branch of the Rust
    source. Stated equationally because the precondition is `True`. -/
theorem trailing_zeros_u64_zero :
    trailing_zeros_u64.trailing_zeros_u64 (0 : u64) = RustM.ok (64 : u32) := by
  unfold trailing_zeros_u64.trailing_zeros_u64
  rfl

/-! ## Stage 2: Hoare triple for the whole function (non-zero case) -/

private theorem tz_function_nonzero_triple (x : u64) (hx : x ≠ 0) :
    ⦃⌜ True ⌝⦄
      trailing_zeros_u64.trailing_zeros_u64 x
    ⦃⇓ r => ⌜ r.toNat < 64 ∧ 2 ^ r.toNat ∣ x.toNat ∧
              (x.toNat >>> r.toNat) &&& 1 = 1 ⌝⦄ := by
  -- The loop triple gives us the loop's postcondition.
  have h_loop := tz_loop_triple x
  -- Project it: from `tzInv x s ∧ ¬tzCond s`, derive the three postconditions
  -- on `s._0`.
  have h_loop' :
      ⦃⌜ tzInv x ⟨(0 : u32), x⟩ ⌝⦄
        tzLoop x
      ⦃⇓ r => ⌜ r._0.toNat < 64 ∧ 2 ^ r._0.toNat ∣ x.toNat ∧
                (x.toNat >>> r._0.toNat) &&& 1 = 1 ⌝⦄ := by
    apply Triple.of_entails_right _ _ _ _ h_loop
    apply PostCond.entails.of_left_entails
    intro r ⟨hinv, hncond⟩
    -- hinv : tzInv x r
    -- hncond : ¬ tzCond r = true
    unfold tzInv at hinv
    obtain ⟨hx_eq, hy_pos, hc_lt⟩ := hinv
    -- From hncond, the loop exited with y odd: (r._1 &&& 1).toNat ≠ 0,
    -- which means r._1.toNat &&& 1 ≠ 0, i.e. r._1.toNat % 2 = 1.
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
    · -- 2 ^ r._0.toNat ∣ x.toNat
      rw [hx_eq]
      exact ⟨r._1.toNat, by rw [Nat.mul_comm]⟩
    · -- (x.toNat >>> r._0.toNat) &&& 1 = 1
      rw [hx_eq]
      -- (r._1 * 2^r._0).toNat >>> r._0.toNat = r._1.toNat
      have h_div : (r._1.toNat * 2 ^ r._0.toNat) >>> r._0.toNat = r._1.toNat := by
        rw [Nat.shiftRight_eq_div_pow]
        have hpos : 0 < 2 ^ r._0.toNat := Nat.two_pow_pos r._0.toNat
        exact Nat.mul_div_cancel _ hpos
      rw [h_div]
      rw [Nat.and_one_is_mod]
      exact h_y_odd
  -- Weaken precondition: True → tzInv x ⟨0, x⟩.
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
  -- Reformulate the function as a bind.
  unfold trailing_zeros_u64.trailing_zeros_u64
  unfold rust_primitives.hax.while_loop
  -- The function with x ≠ 0 reduces to: tzLoop x >>= fun s => pure s._0
  show ⦃⌜True⌝⦄
        ((x ==? (0 : u64)) >>= fun b =>
          if b = true then pure (64 : u32)
          else (tzLoop x >>= fun __discr =>
                  match __discr with | ⟨c, _⟩ => pure c))
        ⦃⇓ r => ⌜r.toNat < 64 ∧ 2 ^ r.toNat ∣ x.toNat ∧ (x.toNat >>> r.toNat) &&& 1 = 1⌝⦄
  -- x ==? 0 = pure (x == 0)
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
  -- Goal: ⦃⌜True⌝⦄ (tzLoop x >>= ...) ⦃...⦄
  apply Triple.bind _ _ h_loop''
  intro s
  cases s with
  | mk c y =>
    refine Triple.pure c ?_
    intro h
    exact h

/-- Totality / no-panic: for every `u64` input the function returns a value
    (it never overflows, divides by zero, or under/overflows a shift). The
    Rust source has no `panic!`; the `count + 1` increment, `y >> 1` shift,
    and `y & 1` mask are bounded by `count < 64` and `0 < shift < 64`. This
    is the "no failure mode" clause of the contract, independent of the
    value returned. -/
theorem trailing_zeros_u64_total (x : u64) :
    ∃ r : u32, trailing_zeros_u64.trailing_zeros_u64 x = RustM.ok r := by
  by_cases hx : x = 0
  · subst hx; exact ⟨64, trailing_zeros_u64_zero⟩
  · -- Use the function triple, converted via Triple_iff_BitVec.
    have h := tz_function_nonzero_triple x hx
    rw [RustM.Triple_iff_BitVec] at h
    simp only [decide_true, Bool.not_true, Bool.false_or,
               Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hok, hpost⟩ := h
    cases hf : trailing_zeros_u64.trailing_zeros_u64 x with
    | none => rw [hf] at hok; simp [RustM.toBVRustM] at hok
    | some result =>
      cases result with
      | ok v => exact ⟨v, rfl⟩
      | error e =>
        rw [hf] at hok
        cases e <;> simp [RustM.toBVRustM] at hok

/-! ## Master existential lemma derived from the function triple -/

/-- Existential closed-form: for `x ≠ 0`, the function returns some `r` satisfying
    all three postconditions simultaneously. Each individual obligation below is
    a projection of this master lemma. -/
private theorem trailing_zeros_u64_nonzero_spec (x : u64) (hx : x ≠ 0) :
    ∃ r : u32, trailing_zeros_u64.trailing_zeros_u64 x = RustM.ok r ∧
                r.toNat < 64 ∧
                2 ^ r.toNat ∣ x.toNat ∧
                (x.toNat >>> r.toNat) &&& 1 = 1 := by
  have h := tz_function_nonzero_triple x hx
  rw [RustM.Triple_iff_BitVec] at h
  simp only [decide_true, Bool.not_true, Bool.false_or,
             Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hok, hpost⟩ := h
  cases hf : trailing_zeros_u64.trailing_zeros_u64 x with
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

/-! ## Contract clauses derived from the master existential -/

/-- Range clause: for `x ≠ 0`, the result is strictly less than `64`. Captures
    the `result_below_64_when_nonzero` property test (and the `r < 64`
    assertion inside `property_contract_diverse_inputs`). -/
theorem trailing_zeros_u64_range (x : u64) (hx : x ≠ 0) :
    ∃ r : u32, trailing_zeros_u64.trailing_zeros_u64 x = RustM.ok r ∧ r.toNat < 64 := by
  obtain ⟨r, hr, hlt, _, _⟩ := trailing_zeros_u64_nonzero_spec x hx
  exact ⟨r, hr, hlt⟩

/-- Divisibility clause: for `x ≠ 0`, `2 ^ result` divides `x`. Captures the
    `power_of_two_divides` property test (and the divisibility assertion in
    `property_contract_diverse_inputs`). -/
theorem trailing_zeros_u64_divides (x : u64) (hx : x ≠ 0) :
    ∃ r : u32, trailing_zeros_u64.trailing_zeros_u64 x = RustM.ok r ∧
      2 ^ r.toNat ∣ x.toNat := by
  obtain ⟨r, hr, _, hdvd, _⟩ := trailing_zeros_u64_nonzero_spec x hx
  exact ⟨r, hr, hdvd⟩

/-- Exactness clause: for `x ≠ 0`, bit `result` of `x` is set; equivalently,
    `x` is not divisible by `2 ^ (result + 1)`. Captures the
    `lowest_set_bit_is_at_result` property test (and the exactness
    assertion in `property_contract_diverse_inputs`). The form
    `(x.toNat >>> r.toNat) &&& 1 = 1` mirrors the Rust assertion
    `(x >> r) & 1 == 1` lifted to `Nat`. -/
theorem trailing_zeros_u64_exact (x : u64) (hx : x ≠ 0) :
    ∃ r : u32, trailing_zeros_u64.trailing_zeros_u64 x = RustM.ok r ∧
      (x.toNat >>> r.toNat) &&& 1 = 1 := by
  obtain ⟨r, hr, _, _, hexact⟩ := trailing_zeros_u64_nonzero_spec x hx
  exact ⟨r, hr, hexact⟩

/-- Powers-of-two diagonal: for every bit position `k < 64`, the input
    `2 ^ k` has exactly `k` trailing zeros. Captures the
    `property_powers_of_two_exact` test, which sweeps the full `u64` bit
    range — coverage that the small-range loop tests miss. Stated as a
    `u32 → u64 → RustM u32` equation; `2 ^ k.toNat` is the `UInt64`
    encoding of `1u64 << k`.

    Proof: 2 ^ k ≠ 0 (since k < 64 < 2^64), so the existential spec applies.
    The output `r` satisfies `2 ^ r ∣ 2 ^ k` and `(2 ^ k >>> r) &&& 1 = 1`.
    From divisibility we get `r ≤ k`; from exactness we get `r ≥ k` (otherwise
    `2 ^ k >>> r = 2 ^ (k - r)` would be even); together `r = k`. -/
theorem trailing_zeros_u64_power_of_two (k : u32) (hk : k.toNat < 64) :
    trailing_zeros_u64.trailing_zeros_u64 (UInt64.ofNat (2 ^ k.toNat)) = RustM.ok k := by
  -- Let x = UInt64.ofNat (2 ^ k.toNat). Then x.toNat = 2 ^ k.toNat (since k < 64).
  have h_pow_lt : 2 ^ k.toNat < 2 ^ 64 :=
    Nat.pow_lt_pow_right (by decide : 1 < 2) hk
  have h_x_toNat : (UInt64.ofNat (2 ^ k.toNat)).toNat = 2 ^ k.toNat :=
    UInt64.toNat_ofNat_of_lt' h_pow_lt
  have hx_ne : UInt64.ofNat (2 ^ k.toNat) ≠ 0 := by
    intro h
    have h0 : (UInt64.ofNat (2 ^ k.toNat)).toNat = 0 := by rw [h]; rfl
    rw [h_x_toNat] at h0
    have h_pos : 0 < 2 ^ k.toNat := Nat.two_pow_pos k.toNat
    omega
  obtain ⟨r, hr_eq, hr_lt, hr_dvd, hr_exact⟩ :=
    trailing_zeros_u64_nonzero_spec (UInt64.ofNat (2 ^ k.toNat)) hx_ne
  -- From hr_dvd: 2 ^ r.toNat ∣ 2 ^ k.toNat → r.toNat ≤ k.toNat.
  rw [h_x_toNat] at hr_dvd hr_exact
  have h_r_le_k : r.toNat ≤ k.toNat :=
    (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp hr_dvd
  -- (2^k) >>> r.toNat = 2^k / 2^r.toNat = 2^(k - r) (since r ≤ k).
  rw [Nat.shiftRight_eq_div_pow,
      Nat.pow_div h_r_le_k (by decide : 0 < 2)] at hr_exact
  -- Now hr_exact : 2 ^ (k.toNat - r.toNat) &&& 1 = 1.
  rw [Nat.and_one_is_mod] at hr_exact
  -- 2^n % 2 = 0 unless n = 0.
  have h_eq : k.toNat - r.toNat = 0 := by
    rcases Nat.eq_zero_or_pos (k.toNat - r.toNat) with h | h
    · exact h
    · exfalso
      -- Express k - r = m + 1 and use 2^(m+1) = 2 * 2^m, then mod 2 = 0.
      obtain ⟨m, hm⟩ : ∃ m, k.toNat - r.toNat = m + 1 :=
        ⟨k.toNat - r.toNat - 1, by omega⟩
      rw [hm, Nat.pow_succ, Nat.mul_comm] at hr_exact
      -- hr_exact : 2 * 2 ^ m % 2 = 1
      have h_mul_mod : 2 * 2 ^ m % 2 = 0 := Nat.mul_mod_right 2 (2 ^ m)
      omega
  -- So k.toNat = r.toNat.
  have h_kr : k.toNat = r.toNat := by omega
  rw [hr_eq]
  congr 1
  exact UInt32.toNat_inj.mp h_kr.symm

end Trailing_zeros_u64Obligations
