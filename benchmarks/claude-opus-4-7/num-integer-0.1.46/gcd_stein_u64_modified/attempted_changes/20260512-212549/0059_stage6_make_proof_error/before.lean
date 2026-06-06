-- Companion obligations file for the `gcd_stein_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import gcd_stein_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Gcd_stein_u64Obligations

/-! ## Helper lemmas for casting `Nat.gcd` back to `u64`.

Pure-Nat facts about `Nat.gcd a.toNat b.toNat` — copied verbatim from
`Gcd_whileObligations.lean`, where they are also used to bridge between
`Nat.gcd` and `UInt64.ofNat (Nat.gcd …)`. -/

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

/-! ## Contract obligations for `gcd_stein_u64.gcd_stein`

The contract is read off the property tests in `src/lib.rs`:

* `known_values` + `zero_zero_is_zero` — closed-form equation
  `gcd_stein a b = Nat.gcd a b`.  Stating this once as the
  `_postcondition` theorem subsumes every concrete hand-checked value
  (`(10, 2) = 2`, `(0, 3) = 3`, `(3, 3) = 3`, `(56, 42) = 14`, etc.).
* `result_divides_both_inputs` — two independent divisibility clauses
  `gcd | a` and `gcd | b`.
* `result_is_greatest` — every common divisor `d` divides the result.

Stein's binary algorithm has *no documented failure modes*: every
intermediate `u64` operation is provably in range (subtraction is guarded
by `m > n`, the final `m << shift` produces `gcd(a, b) ≤ max(a, b) < 2^64`).
Hence the postcondition is stated equationally as `RustM.ok …` rather
than as a Hoare triple — the no-panic clause is folded into the use of
`RustM.ok` on the right-hand side, and surfaced explicitly as
`gcd_stein_total`.

Shapes mirror `proof_patterns/gcd_while_modified/.../Gcd_whileObligations.lean`. -/

/-! ## Boundary cases (proved directly from the short-circuit).

The Rust source contains an `if m == 0 || n == 0 { return m | n }`
short-circuit, so the three "at least one input zero" cases reduce to
purely-bitwise reasoning — independent of the algorithm body and the
hard correctness proof.  These are proven *first* so the main
`gcd_stein_postcondition` proof can fold them in as boundary cases. -/

/-- **`gcd_stein(0, 0) = 0`.** The explicit boundary from
`zero_zero_is_zero` — the `m | n` short-circuit in the source returns
0 when both inputs are 0. -/
theorem gcd_stein_zero_zero :
    gcd_stein_u64.gcd_stein 0 0 = RustM.ok 0 := by
  simp only [gcd_stein_u64.gcd_stein, rust_primitives.cmp.eq,
             rust_primitives.hax.logical_op.or, pure_bind,
             beq_self_eq_true, Bool.or_self, ↓reduceIte]
  rfl

/-- **`gcd_stein(0, b) = b`.** Pins down the `a = 0` branch of the
`m == 0 || n == 0` short-circuit.  Covers the `(0, 3) = 3` row of
`known_values` (and, together with `gcd_stein_divides_b`, forces
`gcd_stein(0, b) = b` since the gcd must divide `b` and is itself
divisible by `b` via `Nat.gcd_zero_left`). -/
theorem gcd_stein_a_zero (b : u64) :
    gcd_stein_u64.gcd_stein 0 b = RustM.ok b := by
  simp only [gcd_stein_u64.gcd_stein, rust_primitives.cmp.eq,
             rust_primitives.hax.logical_op.or, pure_bind,
             beq_self_eq_true, Bool.true_or, ↓reduceIte]
  -- Goal: pure (0 ||| b) = RustM.ok b
  apply congrArg RustM.ok
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_or]
  show 0 ||| b.toNat = b.toNat
  exact Nat.zero_or b.toNat

/-- **`gcd_stein(a, 0) = a`.** Symmetric to `gcd_stein_a_zero`; pins
down the `b = 0` branch of the short-circuit. -/
theorem gcd_stein_b_zero (a : u64) :
    gcd_stein_u64.gcd_stein a 0 = RustM.ok a := by
  simp only [gcd_stein_u64.gcd_stein, rust_primitives.cmp.eq,
             rust_primitives.hax.logical_op.or, pure_bind,
             beq_self_eq_true, Bool.or_true, ↓reduceIte]
  -- Goal: pure (a ||| 0) = RustM.ok a
  apply congrArg RustM.ok
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_or]
  show a.toNat ||| 0 = a.toNat
  exact Nat.or_zero a.toNat

/-! ## Loop infrastructure for `trailing_zeros_u64`

Mirroring the `gcd_while_modified` two-stage template: define the loop
explicitly as `Loop.MonoLoopCombinator.while_loop`, prove a Hoare triple
with a strong invariant, then peel back to an existence/equation.  The
strong invariant is `y > 0 ∧ count < 64`, the termination measure is
`y.toNat`.  Because `y &&& 1 = 0` (the loop guard) forces `y` to be
even, and `y > 0 ∧ even ⟹ y ≥ 2`, the body's right-shift halves `y`
strictly — giving the strict decrease for the measure. -/

open rust_primitives.hax (Tuple2)

private abbrev tzCond : Tuple2 u32 u64 → Bool :=
  fun s => decide ((s._1 &&& (1 : u64)).toNat = (0 : u64).toNat)

private abbrev tzBody : Tuple2 u32 u64 → RustM (Tuple2 u32 u64) :=
  fun s =>
    match s with
    | ⟨count, y⟩ =>
      (do
        let y : u64 ← (y >>>? (1 : i32))
        let count : u32 ← (count +? (1 : u32))
        pure (rust_primitives.hax.Tuple2.mk count y) :
        RustM (rust_primitives.hax.Tuple2 u32 u64))

private abbrev tzLoop (x : u64) : RustM (Tuple2 u32 u64) :=
  Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk tzCond
    (rust_primitives.hax.Tuple2.mk (0 : u32) x) tzBody

/-- Strong invariant: `y` is positive and `y * 2^count = x`.  The
*equational* form is the natural Stein-trailing-zeros invariant: each
loop iteration halves `y` and increments `count`, preserving the
product `y * 2^count`.  From `y ≥ 1` and the invariant we derive
`2^count ≤ x < 2^64`, hence `count.toNat < 64`, which suffices to
discharge the `count +? 1` no-overflow obligation.  The equational
form also enables the *correctness* theorem (oddness of `x / 2^count`
at termination) — see `trailing_zeros_u64_correctness`. -/
private abbrev tzInv (x : u64) (s : Tuple2 u32 u64) : Prop :=
  s._1.toNat > 0 ∧ s._1.toNat * 2 ^ s._0.toNat = x.toNat

private abbrev tzTerm (s : Tuple2 u32 u64) : Nat := s._1.toNat

private instance : Inhabited (Tuple2 u32 u64) := ⟨⟨0, 0⟩⟩

/-- **Loop Hoare triple for trailing_zeros_u64.**  The shared workhorse:
applies `Spec.MonoLoopCombinator.while_loop` with the equational
invariant `y > 0 ∧ y * 2^count = x` and termination measure `y.toNat`.
Body-step facts derived inside:
  (a) `(y &&& 1).toNat = 0 ⟹ y.toNat % 2 = 0 ⟹ (y ≥ 2 given y > 0)`
  (b) i32-shift `0 ≤ 1 < 64` is `true`, so `y >>>? 1 = pure (y / 2)`
  (c) `2^count ≤ y * 2^count = x < 2^64 ⟹ count < 64 ⟹ count + 1 ≤
       64 < 2^32`, so `count +? 1` doesn't overflow
  (d) Invariant preservation: `(y/2) * 2^(count+1) = (y/2 * 2) * 2^count
       = y * 2^count = x` (uses y even). -/
private theorem tz_loop_triple (x : u64) (h_x_pos : 0 < x.toNat) :
    ⦃⌜ tzInv x ⟨(0 : u32), x⟩ ⌝⦄
      tzLoop x
    ⦃⇓ r => ⌜ tzInv x r ∧ ¬ tzCond r = true ⌝⦄ := by
  apply Std.Do.Spec.MonoLoopCombinator.while_loop
    ⟨(0 : u32), x⟩ Lean.Loop.mk tzCond tzBody (tzInv x) tzTerm
  intro s hcond hinv
  cases s with
  | mk count y =>
    -- Normalize tuple projections in the hypotheses.
    change y.toNat > 0 ∧ y.toNat * 2 ^ count.toNat = x.toNat at hinv
    change tzCond ⟨count, y⟩ = true at hcond
    obtain ⟨hy_pos, hprod_eq⟩ := hinv
    -- Derive count.toNat < 64 from the invariant.
    have hcount_lt : count.toNat < 64 := by
      have h2c_le_x : 2 ^ count.toNat ≤ x.toNat := by
        have h_one_le_y : 1 ≤ y.toNat := hy_pos
        have h_step : 1 * 2 ^ count.toNat ≤ y.toNat * 2 ^ count.toNat :=
          Nat.mul_le_mul_right _ h_one_le_y
        rw [Nat.one_mul] at h_step
        rw [hprod_eq] at h_step
        exact h_step
      have h_x_lt : x.toNat < 2 ^ 64 := x.toNat_lt
      have h_pow_lt : 2 ^ count.toNat < 2 ^ 64 :=
        Nat.lt_of_le_of_lt h2c_le_x h_x_lt
      exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h_pow_lt
    -- Unpack the loop guard: (y &&& 1).toNat = 0.
    have hcond_eq : (y &&& (1 : u64)).toNat = (0 : u64).toNat := by
      have h := hcond
      unfold tzCond at h
      exact of_decide_eq_true h
    have h_one_uint64_toNat : (1 : u64).toNat = 1 := rfl
    have h_zero_uint64_toNat : (0 : u64).toNat = 0 := rfl
    have h_y_mod_2 : y.toNat % 2 = 0 := by
      have h := hcond_eq
      rw [UInt64.toNat_and, h_one_uint64_toNat, h_zero_uint64_toNat,
          Nat.and_one_is_mod] at h
      exact h
    have h_y_ge_2 : 2 ≤ y.toNat := by omega
    have h_y_shr_eq :
        (y >>>? (1 : i32) : RustM u64) =
          pure (y >>> ((1 : i32).toNatClampNeg.toUInt64)) := by
      show (rust_primitives.ops.bit.Shr.shr y (1 : i32) : RustM u64) = _
      show (if (0 : Int32) ≤ (1 : i32) && (1 : i32) < 64
            then pure (y >>> ((1 : i32).toNatClampNeg.toUInt64))
            else (.fail .integerOverflow : RustM u64)) = _
      rw [show ((0 : Int32) ≤ (1 : i32) && (1 : i32) < 64) = true from rfl]
      rfl
    have h_shift_amount : ((1 : i32).toNatClampNeg.toUInt64 : u64) = (1 : u64) := rfl
    have h_shr_toNat :
        (y >>> ((1 : i32).toNatClampNeg.toUInt64)).toNat = y.toNat / 2 := by
      rw [h_shift_amount, UInt64.toNat_shiftRight,
          h_one_uint64_toNat, Nat.shiftRight_eq_div_pow]
    have h_y'_pos_raw :
        0 < (y >>> ((1 : i32).toNatClampNeg.toUInt64)).toNat := by
      rw [h_shr_toNat]; omega
    have h_y'_lt_raw :
        (y >>> ((1 : i32).toNatClampNeg.toUInt64)).toNat < y.toNat := by
      rw [h_shr_toNat]; omega
    have h_count_add_eq :
        (count +? (1 : u32) : RustM u32) = pure (count + 1) := by
      show (rust_primitives.ops.arith.Add.add count (1 : u32) : RustM u32) = _
      show (if BitVec.uaddOverflow count.toBitVec (1 : u32).toBitVec
            then (.fail .integerOverflow : RustM u32)
            else pure (count + 1)) = _
      have h_no_ovf : BitVec.uaddOverflow count.toBitVec (1 : u32).toBitVec = false := by
        cases h_eq : BitVec.uaddOverflow count.toBitVec (1 : u32).toBitVec
        · rfl
        · exfalso
          have h_ovf : UInt32.addOverflow count (1 : u32) = true := h_eq
          rw [UInt32.addOverflow_iff] at h_ovf
          have h1 : (1 : u32).toNat = 1 := rfl
          rw [h1] at h_ovf
          omega
      rw [h_no_ovf]; rfl
    have h_count_succ_nat : (count + 1).toNat = count.toNat + 1 := by
      rw [UInt32.toNat_add_of_lt]
      · rfl
      · have h1 : (1 : u32).toNat = 1 := rfl
        rw [h1]; omega
    dsimp only [tzBody]
    rw [h_y_shr_eq, pure_bind]
    rw [h_count_add_eq, pure_bind]
    refine ⟨?_, ?_, ?_⟩
    · show (y >>> ((1 : i32).toNatClampNeg.toUInt64)).toNat < y.toNat
      exact h_y'_lt_raw
    · show 0 < (y >>> ((1 : i32).toNatClampNeg.toUInt64)).toNat
      exact h_y'_pos_raw
    · show (y >>> ((1 : i32).toNatClampNeg.toUInt64)).toNat *
            2 ^ (count + 1).toNat = x.toNat
      rw [h_shr_toNat, h_count_succ_nat, Nat.pow_succ]
      have h_half_times_two : (y.toNat / 2) * 2 = y.toNat := by
        have h_div_mod := Nat.div_add_mod y.toNat 2
        omega
      have h_assoc : (y.toNat / 2) * (2 ^ count.toNat * 2)
                      = ((y.toNat / 2) * 2) * 2 ^ count.toNat := by
        rw [Nat.mul_comm (2 ^ count.toNat) 2, ← Nat.mul_assoc]
      rw [h_assoc, h_half_times_two]
      exact hprod_eq

/-- **Loop result existence (no failure).** Given x > 0, the inner
trailing-zeros loop returns `RustM.ok ⟨count_final, y_final⟩` for some
final state satisfying the invariant and with `y_final` odd. -/
private theorem tz_loop_ok (x : u64) (h_x_pos : 0 < x.toNat) :
    ∃ r : Tuple2 u32 u64, tzLoop x = RustM.ok r ∧
      tzInv x r ∧ r._1.toNat % 2 = 1 := by
  have h_loop := tz_loop_triple x h_x_pos
  have h_init_inv : tzInv x ⟨(0 : u32), x⟩ := by
    refine ⟨h_x_pos, ?_⟩
    show x.toNat * 2 ^ (0 : u32).toNat = x.toNat
    simp
  -- Weaken precondition to True.
  have h_loop' : ⦃⌜True⌝⦄ tzLoop x
      ⦃⇓ r => ⌜ tzInv x r ∧ ¬ tzCond r = true ⌝⦄ := by
    apply Std.Do.Triple.of_entails_left _ _ _ _ h_loop
    intro _; exact h_init_inv
  rw [RustM.Triple_iff_BitVec] at h_loop'
  simp only [decide_true, Bool.not_true, Bool.false_or,
             Bool.and_eq_true, decide_eq_true_eq] at h_loop'
  obtain ⟨hok, hpost⟩ := h_loop'
  cases hf : tzLoop x with
  | none =>
    rw [hf] at hok; simp [RustM.toBVRustM] at hok
  | some result =>
    cases result with
    | ok v =>
      rw [hf] at hpost
      -- After case analysis, the postcondition has been simplified by simp:
      -- ¬ tzCond v = true got normalized to v._1.toNat % 2 = 1 (since
      -- tzCond expanded to decide ((v._1 &&& 1).toNat = 0), and ¬this
      -- via Nat.and_one_is_mod becomes y.toNat % 2 ≠ 0, i.e. = 1).
      simp [RustM.toBVRustM] at hpost
      exact ⟨v, rfl, hpost⟩
    | error e =>
      rw [hf] at hok
      cases e <;> simp [RustM.toBVRustM] at hok

/-- **Reduce `trailing_zeros_u64 x` to `tzLoop x` extraction.**  Given
the loop returns `RustM.ok r`, the wrapping `if x = 0 then ...` produces
`RustM.ok r._0`. -/
private theorem trailing_zeros_unfold_ne_zero (x : u64) (hx : x ≠ 0)
    (r : Tuple2 u32 u64) (hr : tzLoop x = RustM.ok r) :
    gcd_stein_u64.trailing_zeros_u64 x = RustM.ok r._0 := by
  unfold gcd_stein_u64.trailing_zeros_u64
  simp only [rust_primitives.cmp.eq, pure_bind]
  have h_x_ne_beq : (x == (0 : u64)) = false := by
    cases h : (x == (0 : u64)) with
    | true => exact absurd (beq_iff_eq.mp h) hx
    | false => rfl
  rw [h_x_ne_beq]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold rust_primitives.hax.while_loop
  show (tzLoop x >>= fun s => match s with | ⟨c, _⟩ => pure c) = RustM.ok r._0
  rw [hr]
  cases r with
  | mk c y => rfl

/-- **Trailing-zero counter — totality.** For every `u64`, `trailing_zeros_u64`
returns *some* value in `RustM` (it never panics or diverges).

* When `x = 0` the function short-circuits to `pure 64` (no loop).
* When `x ≠ 0`, derived from `tz_loop_triple` via existence projection. -/
private theorem trailing_zeros_u64_total (x : u64) :
    ∃ k : u32, gcd_stein_u64.trailing_zeros_u64 x = RustM.ok k := by
  by_cases hx : x = 0
  · subst hx
    refine ⟨64, ?_⟩
    simp only [gcd_stein_u64.trailing_zeros_u64, rust_primitives.cmp.eq,
               pure_bind, beq_self_eq_true, ↓reduceIte]
    rfl
  · have h_x_pos : 0 < x.toNat := by
      rcases Nat.eq_zero_or_pos x.toNat with h | h
      · exfalso; apply hx; apply UInt64.toNat_inj.mp; rw [h]; rfl
      · exact h
    obtain ⟨r, hr, _⟩ := tz_loop_ok x h_x_pos
    exact ⟨r._0, trailing_zeros_unfold_ne_zero x hx r hr⟩

/-- **Trailing-zero counter — correctness.** For `x ≠ 0`,
`trailing_zeros_u64 x = RustM.ok k` where `k.toNat < 64`,
`2^k.toNat | x.toNat`, and `(x.toNat / 2^k.toNat)` is odd.

Proven by extracting the final state `⟨k, y_final⟩` from `tz_loop_ok`:
the invariant `y_final * 2^k = x` combined with `y_final` odd (from
the loop's negated guard) implies `x.toNat % 2^k.toNat = 0` (the
factor extracts cleanly) and `(x.toNat / 2^k.toNat) = y_final.toNat`
which is odd. -/
private theorem trailing_zeros_u64_correctness (x : u64) (hx : x ≠ 0) :
    ∃ k : u32, gcd_stein_u64.trailing_zeros_u64 x = RustM.ok k ∧
      k.toNat < 64 ∧
      x.toNat % 2 ^ k.toNat = 0 ∧
      (x.toNat / 2 ^ k.toNat) % 2 = 1 := by
  have h_x_pos : 0 < x.toNat := by
    rcases Nat.eq_zero_or_pos x.toNat with h | h
    · exfalso; apply hx; apply UInt64.toNat_inj.mp; rw [h]; rfl
    · exact h
  obtain ⟨r, hr, ⟨hy_pos, hprod_eq⟩, h_y_odd⟩ := tz_loop_ok x h_x_pos
  refine ⟨r._0, trailing_zeros_unfold_ne_zero x hx r hr, ?_, ?_, ?_⟩
  · -- k.toNat < 64.  Reuse the derivation from tz_loop_triple.
    have h2c_le_x : 2 ^ r._0.toNat ≤ x.toNat := by
      have h_one_le_y : 1 ≤ r._1.toNat := hy_pos
      have h_step : 1 * 2 ^ r._0.toNat ≤ r._1.toNat * 2 ^ r._0.toNat :=
        Nat.mul_le_mul_right _ h_one_le_y
      rw [Nat.one_mul] at h_step
      rw [hprod_eq] at h_step
      exact h_step
    have h_x_lt : x.toNat < 2 ^ 64 := x.toNat_lt
    have h_pow_lt : 2 ^ r._0.toNat < 2 ^ 64 :=
      Nat.lt_of_le_of_lt h2c_le_x h_x_lt
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h_pow_lt
  · -- x.toNat % 2 ^ r._0.toNat = 0
    -- From hprod_eq : r._1.toNat * 2^r._0.toNat = x.toNat, so 2^r._0.toNat | x.toNat.
    rw [← hprod_eq, Nat.mul_mod_left]
  · -- (x.toNat / 2 ^ r._0.toNat) % 2 = 1
    -- x.toNat / 2^r._0.toNat = r._1.toNat by exact division, and r._1.toNat is odd.
    rw [← hprod_eq]
    have h_pow_pos : 0 < 2 ^ r._0.toNat := Nat.pow_pos (by decide : 0 < 2)
    rw [Nat.mul_div_cancel _ h_pow_pos]
    exact h_y_odd

/-! ## Stein-step helper lemmas

These are the algebraic facts the outer Stein-loop invariant
preservation will need.  Provided here (proved locally without
Mathlib) so the next pass can use them as named lemmas. -/

/-- **Stein subtraction step.**  For `a ≤ b`, `Nat.gcd a (b - a) = Nat.gcd a b`.

Proof: by `Nat.dvd_antisymm`.  In one direction, `gcd a (b-a)` divides
both `a` and `b - a`, hence divides `a + (b - a) = b`, hence divides
`gcd a b`.  In the other direction, `gcd a b` divides both `a` and
`b`, hence divides `b - a`, hence divides `gcd a (b-a)`. -/
private theorem nat_gcd_sub_self_left (a b : Nat) (h : a ≤ b) :
    Nat.gcd a (b - a) = Nat.gcd a b := by
  apply Nat.dvd_antisymm
  · -- gcd a (b - a) ∣ gcd a b
    apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    have h1 : Nat.gcd a (b - a) ∣ a := Nat.gcd_dvd_left _ _
    have h2 : Nat.gcd a (b - a) ∣ (b - a) := Nat.gcd_dvd_right _ _
    have h3 : Nat.gcd a (b - a) ∣ (b - a) + a := Nat.dvd_add h2 h1
    have h4 : (b - a) + a = b := by omega
    rw [h4] at h3
    exact h3
  · -- gcd a b ∣ gcd a (b - a)
    apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    have h1 : Nat.gcd a b ∣ a := Nat.gcd_dvd_left _ _
    have h2 : Nat.gcd a b ∣ b := Nat.gcd_dvd_right _ _
    exact Nat.dvd_sub h2 h1

/-- **Halve-by-2 on the even side.** For an even `m` and odd `n`,
`Nat.gcd m n = Nat.gcd (m / 2) n`.  This is the second algebraic
identity Stein's algorithm exploits (after halving the larger of two
equal-bit residues).

Proof: since `n` is odd, `Nat.gcd 2 n = 1` (immediate from
`Nat.gcd_rec` + `h_n_odd : n % 2 = 1` + `Nat.gcd_one_left`), so `2`
is coprime to `n`.  Then by Lean core's
`Nat.gcd_mul_right_left_of_gcd_eq_one`, the factor of 2 can be pulled
out of the gcd: `Nat.gcd (2 * k) n = Nat.gcd k n`.  These lemmas all
live in `Init.Data.Nat.Gcd`, contradicting the prior agent's claim
that "Nat.Coprime reasoning is not in Lean core". -/
private theorem nat_gcd_halve_even (k n : Nat) (h_n_odd : n % 2 = 1) :
    Nat.gcd (2 * k) n = Nat.gcd k n := by
  have h_coprime : Nat.gcd 2 n = 1 := by
    rw [Nat.gcd_rec, h_n_odd, Nat.gcd_one_left]
  exact Nat.gcd_mul_right_left_of_gcd_eq_one h_coprime

/-- **Halve-by-`2^k`-on the even side.** Iterated form of
`nat_gcd_halve_even`: if `n` is odd and `2^k` divides `m`, then
`Nat.gcd (m / 2^k) n = Nat.gcd m n`.

Proof: pulled out via `Nat.mul_div_cancel'` (`m = 2^k * (m / 2^k)`),
then applies `Nat.gcd_pow_left_of_gcd_eq_one` to lift the coprimality
`gcd 2 n = 1` to `gcd (2^k) n = 1`, then
`Nat.gcd_mul_right_left_of_gcd_eq_one` cancels the `2^k` factor.

Used by the outer-Stein-loop body step: when `m - n` is even and the
inner `trailing_zeros_u64` extracts a `2^k` factor, the resulting
`(m - n) / 2^k` has the same gcd with `n` as the original `m - n`. -/
private theorem nat_gcd_halve_even_pow (k m n : Nat) (h_n_odd : n % 2 = 1)
    (h_dvd : 2 ^ k ∣ m) : Nat.gcd (m / 2 ^ k) n = Nat.gcd m n := by
  have h_eq : 2 ^ k * (m / 2 ^ k) = m := Nat.mul_div_cancel' h_dvd
  have h_coprime_2 : Nat.gcd 2 n = 1 := by
    rw [Nat.gcd_rec, h_n_odd, Nat.gcd_one_left]
  have h_coprime_pow : Nat.gcd (2 ^ k) n = 1 :=
    Nat.gcd_pow_left_of_gcd_eq_one h_coprime_2
  have h_lift : Nat.gcd (2 ^ k * (m / 2 ^ k)) n = Nat.gcd (m / 2 ^ k) n :=
    Nat.gcd_mul_right_left_of_gcd_eq_one h_coprime_pow
  rw [h_eq] at h_lift
  exact h_lift.symm

/-! ## Stein body-step Nat-level lemmas

These are the algebraic facts needed to prove invariant preservation in
the outer Stein loop's body.  Provided as standalone Nat-level lemmas
so a future pass building the outer-loop Hoare triple can apply them
without reproof. -/

/-- **Difference of two positive odd numbers is positive and even.** When
`m > n` and both are odd, `m - n > 0` and `(m - n) % 2 = 0`. This is the
key fact Stein's algorithm exploits: the difference of two odd numbers
always has trailing-zero count `≥ 1`, so the inner `trailing_zeros_u64`
call extracts at least one factor of 2 each iteration. -/
private theorem stein_diff_even_pos (m n : Nat)
    (hmn : n < m) (hm_odd : m % 2 = 1) (hn_odd : n % 2 = 1) :
    0 < m - n ∧ (m - n) % 2 = 0 := by
  refine ⟨by omega, ?_⟩
  omega

/-- **Stein body left-branch gcd preservation.** When `m ≥ n > 0` with
`n` odd and `2^k ∣ (m - n)`, the body-step replacement
`m ↦ (m - n) / 2^k` preserves the gcd:
  `Nat.gcd ((m - n) / 2^k) n = Nat.gcd m n`.

Combines `nat_gcd_halve_even_pow` (the `2^k` factor commutes out of gcd
when the other side is odd) with `nat_gcd_sub_self_left` (the
Euclid-style subtraction step). -/
private theorem stein_body_gcd_preserve_left (m n k : Nat)
    (hmn : n ≤ m) (hn_odd : n % 2 = 1)
    (hk_dvd : 2 ^ k ∣ (m - n)) :
    Nat.gcd ((m - n) / 2 ^ k) n = Nat.gcd m n := by
  rw [nat_gcd_halve_even_pow k (m - n) n hn_odd hk_dvd,
      Nat.gcd_comm (m - n) n, nat_gcd_sub_self_left n m hmn,
      Nat.gcd_comm n m]

/-- **Stein body right-branch gcd preservation.** Symmetric to
`stein_body_gcd_preserve_left`: when `n ≥ m > 0` with `m` odd and
`2^k ∣ (n - m)`, the body-step replacement `n ↦ (n - m) / 2^k`
preserves the gcd. -/
private theorem stein_body_gcd_preserve_right (m n k : Nat)
    (hmn : m ≤ n) (hm_odd : m % 2 = 1)
    (hk_dvd : 2 ^ k ∣ (n - m)) :
    Nat.gcd m ((n - m) / 2 ^ k) = Nat.gcd m n := by
  rw [Nat.gcd_comm m ((n - m) / 2 ^ k),
      nat_gcd_halve_even_pow k (n - m) m hm_odd hk_dvd,
      Nat.gcd_comm (n - m) m, nat_gcd_sub_self_left m n hmn]

/-- **Strict decrease of the Stein termination measure (left branch).**
When `m > n > 0` both odd and `k ≥ 1` (the trailing-zero count of the
difference), the new pair `⟨(m - n) / 2^k, n⟩` has strictly smaller
sum than `⟨m, n⟩`.

Proof: `(m - n) / 2^k ≤ (m - n) / 2 < m - n < m`, hence
`(m - n) / 2^k + n < m + n`. -/
private theorem stein_term_decrease_left (m n k : Nat)
    (hmn : n < m) (hn_pos : 0 < n) (hk_pos : 1 ≤ k) :
    (m - n) / 2 ^ k + n < m + n := by
  -- `(m - n) / 2^k ≤ m - n` (any divisor ≥ 1) and `m - n < m` (since n > 0).
  have h_div_le : (m - n) / 2 ^ k ≤ m - n := Nat.div_le_self _ _
  omega

/-- **Strict decrease of the Stein termination measure (right branch).**
Symmetric to `stein_term_decrease_left`. -/
private theorem stein_term_decrease_right (m n k : Nat)
    (hmn : m < n) (hm_pos : 0 < m) (hk_pos : 1 ≤ k) :
    m + (n - m) / 2 ^ k < m + n := by
  have h := stein_term_decrease_left n m k hmn hm_pos hk_pos
  omega

/-! ## Outer Stein-loop scaffolding (definitions for the next pass)

These abbrevs match the shape of the outer `while m != n` loop in
`gcd_stein_u64.gcd_stein`.  They are placed here so the next proof pass
can build the Hoare triple via `Spec.MonoLoopCombinator.while_loop`
and `unfold rust_primitives.hax.while_loop` will reveal `steinLoop`.

The natural invariant — `m, n` both positive and odd, `Nat.gcd m n`
preserved — is `steinInv`.  Strict decrease of `m + n` is the
termination measure, supported by `stein_term_decrease_{left,right}`. -/

private abbrev steinCond : Tuple2 u64 u64 → Bool :=
  fun s => s._0 != s._1

private abbrev steinBody : Tuple2 u64 u64 → RustM (Tuple2 u64 u64) :=
  fun s =>
    match s with
    | ⟨m, n⟩ =>
      (do
        if (← (m >? n)) then do
          let m : u64 ← (m -? n)
          let m : u64 ← (m >>>? (← (gcd_stein_u64.trailing_zeros_u64 m)))
          pure (rust_primitives.hax.Tuple2.mk m n)
        else do
          let n : u64 ← (n -? m)
          let n : u64 ← (n >>>? (← (gcd_stein_u64.trailing_zeros_u64 n)))
          pure (rust_primitives.hax.Tuple2.mk m n) :
        RustM (rust_primitives.hax.Tuple2 u64 u64))

private abbrev steinLoop (m₀ n₀ : u64) : RustM (Tuple2 u64 u64) :=
  Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk steinCond
    (rust_primitives.hax.Tuple2.mk m₀ n₀) steinBody

/-- Strong invariant for the outer Stein loop: both components are
positive, both are odd, and the `Nat`-level gcd of the pair equals `G`
(the gcd of the original odd parts before the loop).  At termination
the loop guard `m ≠ n` falsifies, leaving `m = n`, so
`Nat.gcd m.toNat m.toNat = m.toNat = G`. -/
private abbrev steinInv (G : Nat) (s : Tuple2 u64 u64) : Prop :=
  0 < s._0.toNat ∧ 0 < s._1.toNat ∧
  s._0.toNat % 2 = 1 ∧ s._1.toNat % 2 = 1 ∧
  Nat.gcd s._0.toNat s._1.toNat = G

/-- Termination measure for the outer Stein loop: the sum `m.toNat +
n.toNat` strictly decreases each iteration. -/
private abbrev steinTerm (s : Tuple2 u64 u64) : Nat :=
  s._0.toNat + s._1.toNat

/-! ## Sub-lemmas for `gcd_stein_postcondition`

The closed-form correctness of `gcd_stein` decomposes into:

1. **Boundary cases** (`a = 0` or `b = 0`) — already closed above via the
   short-circuit theorems `gcd_stein_a_zero` / `gcd_stein_b_zero`,
   bridged through `Nat.gcd_zero_left` / `Nat.gcd_zero_right`.

2. **Main case** (`a ≠ 0 ∧ b ≠ 0`) — needs

   - `trailing_zeros_u64_correctness`: for `x ≠ 0`, `trailing_zeros_u64 x`
     returns `k` such that `x.toNat = 2^k.toNat * ((x.toNat) >>> k.toNat)`
     and `((x.toNat) >>> k.toNat) % 2 = 1` (i.e. odd post-shift).

   - `stein_outer_loop_invariant`: the outer `while m != n` loop
     preserves `Nat.gcd m.toNat n.toNat * 2^shift.toNat =
     Nat.gcd a.toNat b.toNat` together with `m` and `n` odd.

   - `stein_outer_loop_termination`: `m.toNat + n.toNat` is a strict
     decreasing measure for the outer loop (every body iteration
     either subtracts strictly positive `n` from `m > n`, or vice versa,
     then divides by ≥ 1 factor of 2).

   - `final_shift_no_overflow`: `m << shift` does not overflow because
     after the outer loop terminates `m = Nat.gcd a.toNat b.toNat / 2^shift.toNat`,
     so `m * 2^shift.toNat = Nat.gcd a.toNat b.toNat ≤ max(a, b) < 2^64`.

Each is non-trivial in its own right, hence the surviving `sorry`
covers only the main-case combination, with the boundary cases closed
inline below. -/

/-- **Functional correctness (closed form).** For every pair of `u64`
inputs, `gcd_stein` succeeds and returns the integer gcd of the two
inputs (computed over `Nat`).  This single equation pins down every
concrete `known_values` case as well as the `zero_zero_is_zero`
boundary (`Nat.gcd 0 0 = 0`).

**Proof state (after retry attempt 4):**

* `a = 0` branch — closed via `gcd_stein_a_zero` + `Nat.gcd_zero_left`.
* `b = 0` branch — closed via `gcd_stein_b_zero` + `Nat.gcd_zero_right`.
* `a ≠ 0 ∧ b ≠ 0` branch — `sorry` remains, but the proof now
  (1) extracts the three `trailing_zeros_u64` witnesses with their
  divisibility / oddness clauses, (2) discharges the
  `(a == 0) || (b == 0) = false` boundary check, (3) unfolds the
  function and runs a `simp only` that uses the three witnesses
  (`h_tz_a`, `h_tz_b`, `h_tz_ab`) as rewrite rules — eliminating each
  `trailing_zeros_u64` call.

**Infrastructure added in retry-4 (above this theorem):**

All five of the algebraic / termination identities the outer-loop
Hoare triple would need are now **fully proved**:

* `nat_gcd_sub_self_left` — Euclid subtraction step (existing).
* `nat_gcd_halve_even` — gcd(2k, n) = gcd(k, n) for `n` odd (existing).
* `nat_gcd_halve_even_pow` — iterated form `gcd(m/2^k, n) = gcd(m, n)`
  for `n` odd and `2^k ∣ m` (existing).
* `stein_diff_even_pos` — `m - n` is positive and even when `m, n`
  are both positive, both odd, and `m > n`.  This is the fact that
  forces `trailing_zeros_u64 (m - n) ≥ 1` in every Stein iteration.
* `stein_body_gcd_preserve_left/right` — single-step gcd preservation
  for the body's two branches:
  `Nat.gcd ((m - n) / 2^k) n = Nat.gcd m n`  (when `n` odd, `2^k ∣ m-n`)
  and the symmetric variant for the `m ≤ n` branch.
* `stein_term_decrease_left/right` — strict decrease of `m + n` as
  termination measure, granted `k ≥ 1`.

The outer-loop scaffolding (`steinCond`, `steinBody`, `steinLoop`,
`steinInv`, `steinTerm`) is also defined above so a future pass can
state `stein_loop_triple` by `apply Spec.MonoLoopCombinator.while_loop`
and `unfold rust_primitives.hax.while_loop` will reveal `steinLoop`.

**Specific stuck sub-goal after the `simp only` (this theorem's body):**

After the simp rewrites away the three `trailing_zeros_u64` calls
the goal still contains
  `rust_primitives.hax.while_loop ... ⟨a >>> k_a.toNat.toUInt64,
                                       b >>> k_b.toNat.toUInt64⟩ ...`
plus a final `(m_final <<<? k_ab)`.  Closing this requires three
*non-mechanical* pieces of work that do not exist yet:

1. **`stein_loop_triple` itself** — a Hoare triple over `steinLoop`
   with invariant `steinInv (Nat.gcd m_odd n_odd)` and termination
   `steinTerm`.  Stating it is mechanical (`steinInv`, `steinTerm`
   are now defined), but the *body step* requires composing the
   inner `trailing_zeros_u64_correctness` with the branch-specific
   gcd-preservation lemma `stein_body_gcd_preserve_{left,right}` —
   roughly 150 lines of `tz_loop_triple`-style proof, with the extra
   complication that the body contains a *nested* `RustM` call
   (the inner `trailing_zeros_u64`).

2. **The closed-form bridge** between `Nat.gcd m_odd n_odd` and
   `Nat.gcd a b`: specifically,
   `Nat.gcd a.toNat b.toNat = 2^k_ab.toNat * Nat.gcd m_odd.toNat n_odd.toNat`.
   This depends on the bit-level identity `k_ab = min(k_a, k_b)`
   (since `tz(a|b) = min(tz(a), tz(b))`).  Once that identity is
   available, `nat_gcd_halve_even_pow` cancels the residual `2^|k_a - k_ab|`
   or `2^|k_b - k_ab|` factor against the odd partner.

3. **No-truncation for the final `m_final <<<? k_ab`**:
   `m_final.toNat * 2 ^ k_ab.toNat < 2^64` follows from item 2
   (since the product equals `Nat.gcd a.toNat b.toNat` and
   `gcd_lt_2_64` already shows that bound).  The shift itself
   then evaluates to `RustM.ok (UInt64.ofNat (m_final.toNat * 2^k_ab.toNat))`
   via a `UInt64.toNat_shiftLeft` analogue.

**Structural unblock the next pass would need:** prove
`stein_loop_triple` as a stand-alone theorem.  Every algebraic piece
it needs has been factored into a named lemma above, so the only
genuinely-new content is the body-step bind-chain reduction.  The
`tz_loop_triple` proof in this file is the template — the differences
are the case-split on `m > n` vs `m ≤ n` and the nested
`trailing_zeros_u64` call inside the body.  See the in-body comment
following the `simp only` for the precise goal-shape after the
trailing-zeros rewrites land. -/
theorem gcd_stein_postcondition (a b : u64) :
    gcd_stein_u64.gcd_stein a b
      = RustM.ok (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) := by
  -- Boundary case: a = 0.  Closed via gcd_stein_a_zero + Nat.gcd_zero_left.
  by_cases ha : a = 0
  · subst ha
    rw [gcd_stein_a_zero]
    apply congrArg RustM.ok
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_ofNat_of_lt' (gcd_lt_2_64 0 b)]
    show b.toNat = Nat.gcd (0 : u64).toNat b.toNat
    rw [show ((0 : u64).toNat) = 0 from rfl, Nat.gcd_zero_left]
  -- Boundary case: b = 0.  Closed via gcd_stein_b_zero + Nat.gcd_zero_right.
  by_cases hb : b = 0
  · subst hb
    rw [gcd_stein_b_zero]
    apply congrArg RustM.ok
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_ofNat_of_lt' (gcd_lt_2_64 a 0)]
    show a.toNat = Nat.gcd a.toNat (0 : u64).toNat
    rw [show ((0 : u64).toNat) = 0 from rfl, Nat.gcd_zero_right]
  -- Main case: a ≠ 0 ∧ b ≠ 0.
  -- Pull out the three trailing-zeros applications using the now-proved
  -- `trailing_zeros_u64_correctness` lemma.  The result is a witness
  -- for each (shift, k_a, k_b) plus the divisibility / oddness facts.
  obtain ⟨k_ab, h_tz_ab, h_kab_lt, h_ab_mod, h_ab_odd⟩ :=
    trailing_zeros_u64_correctness (a ||| b) (by
      intro h_or_zero
      -- a ≠ 0 and a ≤ a ||| b gives a ||| b ≠ 0.
      have h_a_pos : 0 < a.toNat := by
        rcases Nat.eq_zero_or_pos a.toNat with h | h
        · exfalso; apply ha; apply UInt64.toNat_inj.mp; rw [h]; rfl
        · exact h
      have h_le : a.toNat ≤ a.toNat ||| b.toNat := Nat.left_le_or
      have h_or_pos : 0 < (a ||| b).toNat := by
        rw [UInt64.toNat_or]; omega
      have h_or_zero_nat : (a ||| b).toNat = 0 := by rw [h_or_zero]; rfl
      omega)
  obtain ⟨k_a, h_tz_a, h_ka_lt, h_a_mod, h_a_odd⟩ :=
    trailing_zeros_u64_correctness a ha
  obtain ⟨k_b, h_tz_b, h_kb_lt, h_b_mod, h_b_odd⟩ :=
    trailing_zeros_u64_correctness b hb
  -- Discharge the boundary check (a == 0) || (b == 0) = false.
  have h_a_ne_beq : (a == (0 : u64)) = false := by
    cases h : (a == (0 : u64)) with
    | true => exact absurd (beq_iff_eq.mp h) ha
    | false => rfl
  have h_b_ne_beq : (b == (0 : u64)) = false := by
    cases h : (b == (0 : u64)) with
    | true => exact absurd (beq_iff_eq.mp h) hb
    | false => rfl
  -- Unfold the function definition.
  unfold gcd_stein_u64.gcd_stein
  -- Use simp to attempt to reduce the function body, treating
  -- h_tz_a/h_tz_b/h_tz_ab as rewrite rules so each `trailing_zeros_u64`
  -- call collapses to `RustM.ok k_*` followed by `pure_bind`.
  simp only [rust_primitives.cmp.eq, rust_primitives.hax.logical_op.or,
             pure_bind, h_a_ne_beq, h_b_ne_beq, Bool.false_or,
             Bool.false_eq_true, ↓reduceIte,
             h_tz_a, h_tz_b, h_tz_ab]
  -- After unfolding and the boundary discharge, the goal is the else-branch:
  --   (do let shift ← trailing_zeros_u64 (← (a |||? b));
  --        let m ← (a >>>? (← trailing_zeros_u64 a));
  --        let n ← (b >>>? (← trailing_zeros_u64 b));
  --        let ⟨m, n⟩ ← rust_primitives.hax.while_loop ...;
  --        (m <<<? shift)) = RustM.ok (UInt64.ofNat (Nat.gcd a.toNat b.toNat))
  --
  -- The next mechanical step would be to use h_tz_ab/h_tz_a/h_tz_b to
  -- eliminate the three trailing-zeros let-bindings.  Each rewrite
  -- requires lifting the bare `trailing_zeros_u64 x = RustM.ok k`
  -- equation to a do-block context, which `simp only [bind_assoc]`
  -- combined with `pure_bind` can normalize.  The genuinely-hard
  -- remaining work is the *outer Stein while-loop*, which has the
  -- same shape as `tz_loop_triple` above but with a more elaborate
  -- body that itself calls `trailing_zeros_u64`.
  --
  -- **Specific stuck sub-goal:** at this point the goal contains
  -- `rust_primitives.hax.while_loop ... ⟨a >>> k_a, b >>> k_b⟩
  --   (fun ⟨m, n⟩ => do if m > n then ... else ...)` followed by
  -- `(m_final <<<? k_ab)`.  Closing this requires:
  --   (1) An outer-loop Hoare triple `stein_loop_triple` with
  --       invariant `m, n both odd ∧ m, n both positive ∧
  --       Nat.gcd m.toNat n.toNat = Nat.gcd (a.toNat / 2^k_a) (b.toNat / 2^k_b)`
  --       and termination measure `m.toNat + n.toNat`.  The body step
  --       case-splits on `m > n` vs `m ≤ n` and uses
  --       `nat_gcd_halve_even_pow` (proved above) plus
  --       `Nat.gcd_self_sub_left` from Lean core.
  --   (2) The closed form `Nat.gcd a.toNat b.toNat =
  --       Nat.gcd (a.toNat / 2^k_a) (b.toNat / 2^k_b) * 2^k_ab`
  --       — relates the gcd of the odd parts back to the gcd of the
  --       original inputs, via `Nat.gcd 2 a = 1` reasoning.  This
  --       step is the algebraic core of Stein's algorithm.
  --   (3) Showing the final `m_final <<<? k_ab` does not overflow:
  --       `m_final.toNat * 2 ^ k_ab.toNat = Nat.gcd a.toNat b.toNat <
  --       2 ^ 64` follows from `gcd_lt_2_64` once we have (2).
  --
  -- **Structural unblock the next pass would need:** prove
  -- `stein_loop_triple` as a stand-alone theorem.  The body step
  -- is the only genuinely-new content (everything else, including
  -- the algebraic lemmas, is already in place in this file).  The
  -- body step requires composing the inner `trailing_zeros_u64`
  -- spec — `trailing_zeros_u64_correctness` here — with the gcd
  -- preservation identity `nat_gcd_halve_even_pow` (already
  -- proved).  The `tz_loop_triple` structure above is the
  -- template to copy.
  sorry

/-- **No-panic / totality.** Stein's algorithm has no documented failure
mode (every `-?` is guarded by a `>`, the final `<<? shift` cannot
overflow because `gcd(a, b) ≤ max(a, b)`).  The function therefore
returns `RustM.ok _` on the entire input domain.  Stated separately
from `gcd_stein_postcondition` because it is the explicit "no failure"
clause of the contract, independent of the returned value. -/
theorem gcd_stein_total (a b : u64) :
    ∃ v : u64, gcd_stein_u64.gcd_stein a b = RustM.ok v :=
  ⟨_, gcd_stein_postcondition a b⟩

/-- **Common-divisor clause (left).** The returned value divides the
first input.  One of the two independent claims certified by the
`result_divides_both_inputs` property test.

Derived from `gcd_stein_postcondition` via `Nat.gcd_dvd_left`; carries
no independent `sorry` (so the only proof obligation remaining is the
closed-form postcondition itself). -/
theorem gcd_stein_divides_a (a b : u64) :
    ∃ v : u64, gcd_stein_u64.gcd_stein a b = RustM.ok v ∧ v.toNat ∣ a.toNat := by
  refine ⟨_, gcd_stein_postcondition a b, ?_⟩
  rw [gcd_toNat_ofNat]
  exact Nat.gcd_dvd_left a.toNat b.toNat

/-- **Common-divisor clause (right).** The returned value divides the
second input.  The other independent claim from
`result_divides_both_inputs`.

Derived from `gcd_stein_postcondition` via `Nat.gcd_dvd_right`. -/
theorem gcd_stein_divides_b (a b : u64) :
    ∃ v : u64, gcd_stein_u64.gcd_stein a b = RustM.ok v ∧ v.toNat ∣ b.toNat := by
  refine ⟨_, gcd_stein_postcondition a b, ?_⟩
  rw [gcd_toNat_ofNat]
  exact Nat.gcd_dvd_right a.toNat b.toNat

/-- **Greatest-divisor clause.** Every common divisor of `a` and `b`
divides the returned value.  This is the contract certified by the
`result_is_greatest` property test (which checks no integer strictly
greater than the result divides both inputs; equivalently, every
common divisor `d` satisfies `d ∣ gcd`, hence `d ≤ gcd` when both are
nonzero).  Stated in the `d ∣ result` form for parity with
`gcd_while_greatest` and to match `Nat.dvd_gcd`.

Derived from `gcd_stein_postcondition` via `Nat.dvd_gcd`. -/
theorem gcd_stein_greatest (a b : u64) :
    ∃ v : u64, gcd_stein_u64.gcd_stein a b = RustM.ok v ∧
      ∀ d : Nat, d ∣ a.toNat → d ∣ b.toNat → d ∣ v.toNat := by
  refine ⟨_, gcd_stein_postcondition a b, ?_⟩
  intro d hda hdb
  rw [gcd_toNat_ofNat]
  exact Nat.dvd_gcd hda hdb

end Gcd_stein_u64Obligations
