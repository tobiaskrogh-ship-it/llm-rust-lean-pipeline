-- Companion obligations file for the `sqrt_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import sqrt_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Sqrt_u64Obligations

open rust_primitives.hax (Tuple2)

/-! ### `log2` loop infrastructure -/

/-- Strong invariant for the `log2` loop. The state is `⟨result, v⟩`.
    Tracks: `result ≤ 63`, `v.toNat = x.toNat / 2^result.toNat`, and `v.toNat ≥ 1`. -/
private def log2Inv (x : u64) (s : Tuple2 u32 u64) : Prop :=
  s._0.toNat ≤ 63 ∧
  s._1.toNat = x.toNat / 2 ^ s._0.toNat ∧
  s._1.toNat ≥ 1

/-- Termination measure: the loop variable `v` (the "remaining" value being shifted). -/
private def log2Term (s : Tuple2 u32 u64) : Nat := s._1.toNat

/-- Loop guard for `log2`: `v > 1`. -/
private abbrev log2Cond : Tuple2 u32 u64 → Bool :=
  fun s => decide (s._1.toNat > 1)

/-- Loop body for `log2`: `(result, v) ↦ (result + 1, v >>> 1)`. -/
private abbrev log2Body : Tuple2 u32 u64 → RustM (Tuple2 u32 u64) :=
  fun s =>
    match s with
    | ⟨result, v⟩ =>
      (do
        let v : u64 ← (v >>>? (1 : i32));
        let result : u32 ← (result +? (1 : u32));
        pure (rust_primitives.hax.Tuple2.mk result v) :
        RustM (Tuple2 u32 u64))

/-- The `log2` loop, reified as a `Lean.Loop.MonoLoopCombinator.while_loop`. -/
private abbrev log2Loop (x : u64) : RustM (Tuple2 u32 u64) :=
  Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk log2Cond ⟨0, x⟩ log2Body

/-- Auxiliary: for any `u64` value `x` and shift amount `k ≥ 63`,
    `x.toNat / 2^k ≤ 1`. -/
private theorem u64_div_pow_ge63_le_one (x : u64) (k : Nat) (hk : k ≥ 63) :
    x.toNat / 2 ^ k ≤ 1 := by
  have hx_lt : x.toNat < 2 ^ 64 := x.toNat_lt
  have h_pow_le : 2 ^ 64 ≤ 2 ^ (k + 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have h_pow_succ : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
  have h_x_lt_2k : x.toNat < 2 ^ k * 2 := by omega
  have h_div_lt : x.toNat / 2 ^ k < 2 := by
    rw [Nat.div_lt_iff_lt_mul hpos]
    have h_comm : 2 * 2 ^ k = 2 ^ k * 2 := Nat.mul_comm 2 (2 ^ k)
    omega
  omega

/-- Stage 1: Hoare-triple for the `log2` loop, given `x ≥ 1`. -/
private theorem log2_loop_triple (x : u64) (hx : x.toNat ≥ 1) :
    ⦃⌜ log2Inv x ⟨0, x⟩ ⌝⦄
      log2Loop x
    ⦃⇓ r => ⌜ log2Inv x r ∧ ¬ log2Cond r = true ⌝⦄ := by
  apply Std.Do.Spec.MonoLoopCombinator.while_loop ⟨0, x⟩ Lean.Loop.mk
    log2Cond log2Body (log2Inv x) log2Term
  intro s hcond hinv
  cases s with
  | mk r v =>
    obtain ⟨hr_le, hveq, hv_pos⟩ := hinv
    have hv_gt1 : v.toNat > 1 := by
      change decide (v.toNat > 1) = true at hcond
      exact decide_eq_true_iff.mp hcond
    have hr_lt : r.toNat < 63 := by
      rcases Nat.lt_or_ge r.toNat 63 with hlt | hge
      · exact hlt
      · exfalso
        have hv_le : v.toNat ≤ 1 := by
          rw [hveq]
          exact u64_div_pow_ge63_le_one x r.toNat hge
        omega
    have h_shr : (v >>>? (1 : i32) : RustM u64) = pure (v >>> (1 : u64)) := by
      show (rust_primitives.ops.bit.Shr.shr v (1 : i32) : RustM u64)
            = pure (v >>> (1 : u64))
      show (if (0 : Int32) ≤ (1 : Int32) && (1 : Int32) < 64 then
              pure (v >>> ((1 : Int32).toNatClampNeg.toUInt64))
            else .fail .integerOverflow) = pure (v >>> (1 : u64))
      simp only [show ((0 : Int32) ≤ (1 : Int32) && (1 : Int32) < 64) = true from rfl,
                 ↓reduceIte]
      rfl
    have h_no_ovf : UInt32.addOverflow r (1 : u32) = false := by
      cases h_eq : UInt32.addOverflow r (1 : u32) with
      | false => rfl
      | true =>
        exfalso
        rw [UInt32.addOverflow_iff] at h_eq
        have h1 : (1 : u32).toNat = 1 := rfl
        omega
    have h_add : (r +? (1 : u32) : RustM u32) = pure (r + 1) := by
      show (rust_primitives.ops.arith.Add.add r (1 : u32) : RustM u32)
            = pure (r + 1)
      show (if BitVec.uaddOverflow r.toBitVec (1 : u32).toBitVec then
              (.fail .integerOverflow : RustM u32)
            else pure (r + 1)) = pure (r + 1)
      rw [show BitVec.uaddOverflow r.toBitVec (1 : u32).toBitVec = false from h_no_ovf]
      rfl
    dsimp only [log2Body]
    rw [h_shr]
    simp only [pure_bind]
    rw [h_add]
    simp only [pure_bind]
    have h_v_shr : (v >>> (1 : u64)).toNat = v.toNat / 2 := by
      rw [UInt64.toNat_shiftRight, show (1 : u64).toNat = 1 from rfl,
          Nat.shiftRight_eq_div_pow, Nat.pow_one]
    have h_r_add : (r + 1).toNat = r.toNat + 1 := by
      have h_bound : r.toNat + (1 : u32).toNat < 2 ^ 32 := by
        have h1 : (1 : u32).toNat = 1 := rfl
        omega
      rw [UInt32.toNat_add_of_lt h_bound]; rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (v >>> (1 : u64)).toNat < v.toNat
      rw [h_v_shr]; omega
    · show (r + 1).toNat ≤ 63
      rw [h_r_add]; omega
    · show (v >>> (1 : u64)).toNat = x.toNat / 2 ^ (r + 1).toNat
      rw [h_v_shr, h_r_add, hveq, Nat.pow_succ, Nat.div_div_eq_div_mul]
    · show (v >>> (1 : u64)).toNat ≥ 1
      rw [h_v_shr]; omega

/-- Bridge: `2^r ≤ x ∧ x < 2^(r+1)` from `x / 2^r = 1` and `r ≤ 63`. -/
private theorem log2_exit_bounds (x : u64) (r : Nat) (hr : r ≤ 63)
    (hdiv : x.toNat / 2 ^ r = 1) :
    2 ^ r ≤ x.toNat ∧ x.toNat < 2 ^ (r + 1) := by
  have hpos : 0 < 2 ^ r := Nat.two_pow_pos r
  refine ⟨?_, ?_⟩
  · have hmul : x.toNat / 2 ^ r * 2 ^ r ≤ x.toNat := Nat.div_mul_le_self _ _
    rw [hdiv, Nat.one_mul] at hmul
    exact hmul
  · have h_div_lt : x.toNat / 2 ^ r < 2 := by rw [hdiv]; decide
    have h_x_lt : x.toNat < 2 * 2 ^ r :=
      (Nat.div_lt_iff_lt_mul hpos).mp h_div_lt
    have h_pow : 2 ^ (r + 1) = 2 ^ r * 2 := Nat.pow_succ 2 r
    have h_comm : 2 ^ r * 2 = 2 * 2 ^ r := Nat.mul_comm _ _
    omega

/-! ### Closed small-input lemma (the `a < 4` branch). -/

/-- Totality on the small-input branch. -/
private theorem sqrt_small_no_failure (x : u64) (h : x < 4) :
    ∃ v : u64, sqrt_u64.sqrt x = RustM.ok v := by
  unfold sqrt_u64.sqrt
  simp only [rust_primitives.cmp.lt, rust_primitives.cmp.gt, decide_eq_true_eq, pure_bind]
  rw [if_pos h]
  by_cases h2 : x > 0
  · rw [if_pos h2]; exact ⟨1, rfl⟩
  · rw [if_neg h2]; exact ⟨0, rfl⟩

/-- Closed-form value of `sqrt` on the small-input branch.
    Used to discharge the Hoare-triple obligations for `x < 4`. -/
private theorem sqrt_small_eq (x : u64) (h : x < 4) :
    sqrt_u64.sqrt x = if x > 0 then RustM.ok 1 else RustM.ok 0 := by
  unfold sqrt_u64.sqrt
  simp only [rust_primitives.cmp.lt, rust_primitives.cmp.gt, decide_eq_true_eq, pure_bind]
  rw [if_pos h]
  by_cases h2 : x > 0
  · rw [if_pos h2, if_pos h2]; rfl
  · rw [if_neg h2, if_neg h2]; rfl

/-! ### General-case obligations.

The structural reasoning that closes these three theorems is:

  * **Loop 1** — `log2`'s inner `while_loop`. `log2_loop_triple` above
    establishes the Hoare triple
    `⦃log2Inv x ⟨0, x⟩⦄ log2Loop x ⦃⇓ r => log2Inv x r ∧ ¬cond r⦄`,
    from which `r._0.toNat ≤ 63 ∧ x.toNat / 2^r._0.toNat = 1` follows.

  * **Loop 2** — the Babylonian descent in `sqrt`. Body preservation needs
    the AM-GM step `x ≥ ⌊√a⌋ ⇒ (a/x + x)/2 ≥ ⌊√a⌋`, which requires a
    locally-developed `Nat.sqrt` plus its AM-GM characterisation.

  * **Loop overflow side conditions** — all `+?`, `/?`, `<<<?`, `>>>?`
    operations in the `sqrt` body need their non-failure conditions
    discharged.
-/

/-! ### Helper lemma scaffolding for the large case

The following helper lemmas are *named* by the structural-unblock docstrings
below. They are stated here so a future pass picks up the exact obligations
needed and does not have to re-discover them. They are left as `sorry` because
they require a non-trivial `Nat.sqrt` development (Nat.sqrt is provided in
Lean 4 core via `Init.Data.Nat.Sqrt`; the lemmas below correspond to
`Nat.sqrt_le_self`, `Nat.lt_succ_sqrt`, and the Babylonian-descent AM-GM step). -/

/-- Newton-step preservation of "above the integer square root".
    For `x ≥ ⌊√a⌋` and `x ≥ 1`, the Newton step `(a/x + x)/2` is still
    `≥ ⌊√a⌋`. This is the *only* hard sub-goal in the Babylonian-descent
    invariant: termination via `x.toNat` decreasing follows from the loop
    guard `x > xn`; the lower-bound and upper-bound postconditions follow
    from the AM-GM characterisation of the descent fixed-point. -/
private theorem natSqrt_newton_step (a x : Nat) (hx_pos : x ≥ 1)
    (hxa : x ≥ Nat.sqrt a) : (a / x + x) / 2 ≥ Nat.sqrt a := by
  -- Proof would unfold `Nat.sqrt` via its `Nat.sqrt_le_self`/`Nat.lt_succ_sqrt`
  -- characterisations, reducing to the algebraic AM-GM identity
  --   x + a/x ≥ 2 * Nat.sqrt a
  -- which holds because `(x - Nat.sqrt a) * (Nat.sqrt a) ≥ 0` and
  -- `a ≥ Nat.sqrt a * Nat.sqrt a`. The Hax/Lean prelude does not currently
  -- expose enough Nat.sqrt API for `omega`/`grind` to discharge this directly;
  -- the proof would need explicit case analysis on whether `x = Nat.sqrt a`
  -- (then `a/x ≥ x` and step ≥ x) or `x > Nat.sqrt a` (the harder case).
  sorry

/-- Initial-guess bound: `1 <<< ((log2 a + 1) / 2) ≤ 2^32` and `≥ 1`,
    given `log2 a ≤ 63`. Used to discharge the no-overflow side condition
    of `(a /? x) +? x` after the initial Newton step. -/
private theorem initial_guess_bounds (l : Nat) (hl : l ≤ 63) :
    (1 : Nat) ≤ 2 ^ ((l + 1) / 2) ∧ 2 ^ ((l + 1) / 2) ≤ 2 ^ 32 := by
  refine ⟨Nat.one_le_two_pow, ?_⟩
  apply Nat.pow_le_pow_right (by decide : 1 ≤ 2)
  omega
-/

-- (closing `-/` matches the doc-string block above)
===

/-- Postcondition (lower bound): the result `r` of `sqrt x` satisfies `r² ≤ x`.

    Proof status: small case (`x < 4`) closed via `sqrt_small_eq`; large
    case left as `sorry` (Babylonian-descent invariant). -/
theorem sqrt_lower_bound (x : u64) :
    ⦃ ⌜ True ⌝ ⦄
      sqrt_u64.sqrt x
    ⦃ ⇓ r => ⌜ r.toNat * r.toNat ≤ x.toNat ⌝ ⦄ := by
  by_cases h : x < 4
  · -- Small case (x < 4): use the closed form sqrt x = ok 1 or ok 0.
    rw [sqrt_small_eq x h]
    by_cases h2 : x > 0
    · -- result is 1, need 1*1 ≤ x.toNat. Have x > 0 ⇒ x.toNat ≥ 1.
      rw [if_pos h2]
      refine Triple.pure (1 : u64) ?_
      intro _
      have h1 : (1 : u64).toNat = 1 := rfl
      have hx_pos : x.toNat > 0 := by
        have h2' : (0 : u64) < x := h2
        rw [UInt64.lt_iff_toNat_lt] at h2'
        have h0 : (0 : u64).toNat = 0 := rfl
        omega
      show (1 : u64).toNat * (1 : u64).toNat ≤ x.toNat
      rw [h1]; omega
    · -- result is 0, need 0 ≤ x.toNat. Trivially true.
      rw [if_neg h2]
      refine Triple.pure (0 : u64) ?_
      intro _
      have h0 : (0 : u64).toNat = 0 := rfl
      show (0 : u64).toNat * (0 : u64).toNat ≤ x.toNat
      rw [h0]; omega
  · -- Large case (x ≥ 4): Babylonian descent invariant required.
    --
    -- Stuck sub-goal: after applying `Spec.MonoLoopCombinator.while_loop` with
    -- the AM-GM invariant `x.toNat ≥ ⌊√a.toNat⌋`, the body-preservation goal
    -- reduces to `x ≥ ⌊√a⌋ ⇒ (a/x + x)/2 ≥ ⌊√a⌋` in `Nat` arithmetic with
    -- floor-division. This requires a `Nat.sqrt`-style development.
    --
    -- Structural unblock: a separately-verified `Nat.sqrt` development
    -- (definition, monotonicity, AM-GM characterisation
    -- `x*x ≤ a ∧ a < (x+1)*(x+1) preserved under Newton step`) added to a
    -- shared Lean module and imported here.
    sorry

/-- Postcondition (upper bound): `x < (r + 1)²`.

    Proof status: small case (`x < 4`) closed via `sqrt_small_eq`; large
    case left as `sorry` (same obstacle as `sqrt_lower_bound`). -/
theorem sqrt_upper_bound (x : u64) :
    ⦃ ⌜ True ⌝ ⦄
      sqrt_u64.sqrt x
    ⦃ ⇓ r => ⌜ x.toNat < (r.toNat + 1) * (r.toNat + 1) ⌝ ⦄ := by
  by_cases h : x < 4
  · rw [sqrt_small_eq x h]
    by_cases h2 : x > 0
    · -- result is 1, need x.toNat < (1+1) * (1+1) = 4. Have x < 4.
      rw [if_pos h2]
      refine Triple.pure (1 : u64) ?_
      intro _
      have h1 : (1 : u64).toNat = 1 := rfl
      have hx_lt : x.toNat < 4 := by
        have h' : x < (4 : u64) := h
        rw [UInt64.lt_iff_toNat_lt] at h'
        have h4 : (4 : u64).toNat = 4 := rfl
        omega
      show x.toNat < ((1 : u64).toNat + 1) * ((1 : u64).toNat + 1)
      rw [h1]; omega
    · -- result is 0, need x.toNat < (0+1) * (0+1) = 1. Have x = 0.
      rw [if_neg h2]
      refine Triple.pure (0 : u64) ?_
      intro _
      have h0 : (0 : u64).toNat = 0 := rfl
      have hx_eq : x.toNat = 0 := by
        rcases Nat.eq_zero_or_pos x.toNat with he | hp
        · exact he
        · exfalso
          apply h2
          show (0 : u64) < x
          rw [UInt64.lt_iff_toNat_lt]
          have h0' : (0 : u64).toNat = 0 := rfl
          omega
      show x.toNat < ((0 : u64).toNat + 1) * ((0 : u64).toNat + 1)
      rw [h0]; omega
  · -- Large case: same Babylonian-descent obstacle as `sqrt_lower_bound`.
    sorry

/-- Totality / no-panic.

    Proof status: small case (`x < 4`) closed via `sqrt_small_no_failure`;
    large case left as `sorry`. -/
theorem sqrt_no_failure (x : u64) :
    ∃ v : u64, sqrt_u64.sqrt x = RustM.ok v := by
  by_cases h : x < 4
  · exact sqrt_small_no_failure x h
  · -- Large case (x ≥ 4): full Babylonian descent + log2 must succeed.
    --
    -- Stuck sub-goal: each operation has a discharge strategy (>>>? by
    -- decide; +? by `log2 a ≤ 63` from `log2_loop_triple`; <<<? by
    -- `(log2 a + 1) / 2 < 64`; /? by `x ≥ 1` from the loop invariant),
    -- but threading them through the nested do-block, conditional Newton
    -- step, and descent `while_loop` requires the Newton-descent invariant
    -- in tandem with the value-correctness proof.
    --
    -- Structural unblock: same as `sqrt_lower_bound` (Nat.sqrt
    -- development); once Newton-descent invariant is in place, the
    -- non-failure side conditions follow directly.
    sorry

end Sqrt_u64Obligations
