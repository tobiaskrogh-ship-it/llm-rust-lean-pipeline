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
`trailing_zeros_u64 x = RustM.ok k` where `k` is the largest exponent
such that `2^k.toNat ∣ x.toNat`.  Equivalently: `x.toNat % 2^k.toNat = 0`
and `x.toNat % 2^(k.toNat + 1) ≠ 0` (and `k.toNat < 64`).

Structural unblock: prove via the `while_example` two-stage template.
The Stage-1 invariant is the strong predicate

  `count.toNat + Nat.log2 y.toNat ≤ Nat.log2 x.toNat ∧`
  `y.toNat * 2^count.toNat = x.toNat ∧ y.toNat > 0`

(i.e. `count` factors of 2 have already been extracted from `x` into
the cumulative `2^count`, and `y` carries the remaining odd-completion
once it stops being even).  Termination measure: `y.toNat`.  Stage 2
peels back to the equation via `RustM.Triple_iff_BitVec`. -/
private theorem trailing_zeros_u64_correctness (x : u64) (hx : x ≠ 0) :
    ∃ k : u32, gcd_stein_u64.trailing_zeros_u64 x = RustM.ok k ∧
      k.toNat < 64 ∧
      x.toNat % 2 ^ k.toNat = 0 ∧
      (x.toNat / 2 ^ k.toNat) % 2 = 1 := by
  sorry

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

**Proof state (after this turn):**

* `a = 0` branch — closed via `gcd_stein_a_zero` + `Nat.gcd_zero_left`.
* `b = 0` branch — closed via `gcd_stein_b_zero` + `Nat.gcd_zero_right`.
* `a ≠ 0 ∧ b ≠ 0` branch — left as `sorry`.

**Specific stuck sub-goal (main case):** after the boundary cases
collapse, the goal reduces to proving

  `do { let shift ← tz(m|n); let m ← m >> tz(m); let n ← n >> tz(n);`
  `     let ⟨m,n⟩ ← outer_loop ⟨m,n⟩; m << shift } = RustM.ok (UInt64.ofNat (Nat.gcd a.toNat b.toNat))`

  under `a ≠ 0 ∧ b ≠ 0`.  This requires reasoning about three nested
  `rust_primitives.hax.while_loop` calls (the trailing-zeros loop is
  invoked four times: on `m|n`, on `m`, on `n`, and inside every outer
  iteration), each requiring its own Hoare-triple correctness statement
  plus the `RustM.Triple_iff_BitVec` ladder to peel back to an equation.
  The classical Stein invariant `2^shift * Nat.gcd m n = Nat.gcd a b`
  is the proof's core, but stating it requires a `Nat.log2_lowest_bit`
  / `Nat.maxPowDvd` predicate that the Hax prelude does not expose —
  and would need to be developed locally first.

**Structural unblocks the next pass would need (in order):**

1. A separately-verified `trailing_zeros_u64_correctness` lemma (the
   Hoare-triple form of "returns k with 2^k | x and (x >>> k) odd"),
   then its equation form via `RustM.Triple_iff_BitVec`.  Estimate: a
   ~80-line proof following the `while_example` template.

2. A `Nat.gcd_stein_step` lemma capturing the algebraic identity
   `Nat.gcd m n = Nat.gcd (m - n) n` when `m ≥ n`, combined with
   `Nat.gcd_two_div_two_odd : Nat.gcd (2*k) (2*l+1) = Nat.gcd k (2*l+1)`.
   These exist in Mathlib's `Mathlib.Data.Nat.GCD.Basic` under names
   like `Nat.gcd_sub_self_left` and `Nat.Coprime.coprime_dvd_two` — the
   Hax prelude does not pull them in.

3. Cross-target import of the `while_example`-style two-stage ladder
   (Stage 1 Hoare triple via `Spec.MonoLoopCombinator.while_loop`,
   Stage 2 equation via `RustM.Triple_iff_BitVec`) for the *outer*
   Stein loop.  Would close the main equation once (1) and (2) are
   available.

4. A `UInt64.shiftLeft_no_overflow_iff` lemma proving `x <<< s` does
   not overflow when `x.toNat * 2^s.toNat < 2^64`; combine with the
   loop invariant's `m = Nat.gcd a b / 2^shift` to discharge the final
   `<<<?`. -/
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
  -- Main case: a ≠ 0 ∧ b ≠ 0.  See docstring for the structural unblock.
  exact sorry

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
