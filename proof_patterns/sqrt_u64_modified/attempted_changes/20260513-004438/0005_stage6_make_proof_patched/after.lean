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
  -- 2^(k+1) = 2^k * 2 (Nat.pow_succ); combined with hx_lt we get x < 2^k * 2.
  have h_pow_succ : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
  have h_x_lt_2k : x.toNat < 2 ^ k * 2 := by omega
  -- Use Nat.div_lt_iff_lt_mul: x / 2^k < 2 ↔ x < 2 * 2^k.
  have h_div_lt : x.toNat / 2 ^ k < 2 := by
    rw [Nat.div_lt_iff_lt_mul hpos]
    -- Goal: x.toNat < 2 * 2 ^ k. We have x.toNat < 2^k * 2; commute.
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
    -- Decode the guard: v.toNat > 1
    have hv_gt1 : v.toNat > 1 := by
      change decide (v.toNat > 1) = true at hcond
      exact decide_eq_true_iff.mp hcond
    -- Step bounds: r must be strictly less than 63.
    have hr_lt : r.toNat < 63 := by
      rcases Nat.lt_or_ge r.toNat 63 with hlt | hge
      · exact hlt
      · exfalso
        have hv_le : v.toNat ≤ 1 := by
          rw [hveq]
          exact u64_div_pow_ge63_le_one x r.toNat hge
        omega
    -- Shift step: `v >>>? (1 : i32)` reduces to `pure (v >>> 1)`.
    have h_shr : (v >>>? (1 : i32) : RustM u64) = pure (v >>> (1 : u64)) := by
      show (rust_primitives.ops.bit.Shr.shr v (1 : i32) : RustM u64)
            = pure (v >>> (1 : u64))
      show (if (0 : Int32) ≤ (1 : Int32) && (1 : Int32) < 64 then
              pure (v >>> ((1 : Int32).toNatClampNeg.toUInt64))
            else .fail .integerOverflow) = pure (v >>> (1 : u64))
      simp only [show ((0 : Int32) ≤ (1 : Int32) && (1 : Int32) < 64) = true from rfl,
                 ↓reduceIte]
      rfl
    -- Addition step: `r +? (1 : u32)` reduces to `pure (r + 1)` since r < 63.
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
    -- Discharge body
    dsimp only [log2Body]
    rw [h_shr]
    simp only [pure_bind]
    rw [h_add]
    simp only [pure_bind]
    -- Goal: term decreases ∧ invariant preserved.
    have h_v_shr : (v >>> (1 : u64)).toNat = v.toNat / 2 := by
      rw [UInt64.toNat_shiftRight, show (1 : u64).toNat = 1 from rfl,
          Nat.shiftRight_eq_div_pow, Nat.pow_one]
    have h_r_add : (r + 1).toNat = r.toNat + 1 := by
      have h_bound : r.toNat + (1 : u32).toNat < 2 ^ 32 := by
        have h1 : (1 : u32).toNat = 1 := rfl
        omega
      rw [UInt32.toNat_add_of_lt h_bound]; rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- log2Term decreases: (v >>> 1).toNat < v.toNat
      show (v >>> (1 : u64)).toNat < v.toNat
      rw [h_v_shr]; omega
    · -- r + 1 ≤ 63
      show (r + 1).toNat ≤ 63
      rw [h_r_add]; omega
    · -- v.toNat / 2 = x.toNat / 2^(r + 1)
      show (v >>> (1 : u64)).toNat = x.toNat / 2 ^ (r + 1).toNat
      rw [h_v_shr, h_r_add, hveq, Nat.pow_succ, Nat.div_div_eq_div_mul]
    · -- (v >>> 1).toNat ≥ 1
      show (v >>> (1 : u64)).toNat ≥ 1
      rw [h_v_shr]; omega

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

/-! ### General-case obligations.

The structural reasoning that closes these three theorems is:

  * **Loop 1** — `log2`'s inner `while_loop`. `log2_loop_triple` above
    establishes the Hoare triple
    `⦃log2Inv x ⟨0, x⟩⦄ log2Loop x ⦃⇓ r => log2Inv x r ∧ ¬cond r⦄`,
    from which `r._0.toNat ≤ 63 ∧ x.toNat / 2^r._0.toNat = 1` (i.e.
    `r._0 = ⌊log₂ x.toNat⌋`) follows directly on the exit branch.
    Lifting this to a full Hoare triple over `sqrt_u64.log2` would need
    only a mechanical `unfold sqrt_u64.log2`-and-rewrite step; the loop
    body itself is already discharged.

  * **Loop 2** — the Babylonian descent in `sqrt`. The natural invariant
    `x.toNat ≥ ⌊√a.toNat⌋ ∧ xn.toNat = (a.toNat / x.toNat + x.toNat) / 2`,
    with termination measure `x.toNat`, would close the lower-bound
    obligation. Body preservation needs the AM-GM step
    `x ≥ ⌊√a⌋  ⇒  (a/x + x)/2 ≥ ⌊√a⌋`.
    The Hax/Lean preludes do not expose `Nat.sqrt` lemmas (no Mathlib
    import), so this would need a locally-developed `Nat.sqrt` plus its
    AM-GM characterisation — the classic "Newton-descent invariant" gap
    the selector flagged.

  * **Loop overflow side conditions** — all `+?`, `/?`, `<<<?`, `>>>?`
    operations in the `sqrt` body need their non-failure conditions
    discharged. The shift `>>>? (1 : i32)` reduces by `decide`; the
    division `a /? x` needs `x ≥ 1` from the loop invariant; the
    addition `(a /? x) +? x` needs `x.toNat ≤ 2^32` (consequence of
    `x ≥ ⌊√a⌋` once the loop is entered with the post-Newton value);
    the shift `1 <<< ((log2 a + 1) / 2)` needs
    `(log2 a + 1) / 2 < 64`, dischargeable from `log2 a ≤ 63`
    (available from `log2_loop_triple`).
-/

/-- Postcondition (lower bound): the result `r` of `sqrt x` satisfies `r² ≤ x`.

    **Proof status: `sorry` — Babylonian descent invariant open.**

    Stuck sub-goal: after applying `Spec.MonoLoopCombinator.while_loop` with
    the AM-GM invariant `x.toNat ≥ ⌊√a.toNat⌋`, the body-preservation
    sub-goal reduces to proving
       `x ≥ ⌊√a⌋  ⇒  (a/x + x)/2 ≥ ⌊√a⌋`
    in `Nat` arithmetic with floor-division. The Hax/Lean preludes do not
    expose `Nat.sqrt` lemmas (no Mathlib import), so this would need a
    locally-developed `Nat.sqrt` plus its AM-GM characterisation, which is
    a substantial separate proof effort.

    Structural unblock: a separately-verified `Nat.sqrt` development
    (definition, monotonicity, fixed-point characterisation, AM-GM step)
    added to a shared Lean module, then imported here. This is the
    classic "Newton-descent invariant" gap the selector flagged. -/
theorem sqrt_lower_bound (x : u64) :
    ⦃ ⌜ True ⌝ ⦄
      sqrt_u64.sqrt x
    ⦃ ⇓ r => ⌜ r.toNat * r.toNat ≤ x.toNat ⌝ ⦄ := by
  sorry

/-- Postcondition (upper bound): `x < (r + 1)²`.

    **Proof status: `sorry` — Babylonian descent invariant open.**

    Same technical obstacle as `sqrt_lower_bound` — see its docstring.
    The upper-bound side of the AM-GM fixed-point analysis is symmetric
    to the lower-bound side and shares the same `Nat.sqrt`-development
    unblock. -/
theorem sqrt_upper_bound (x : u64) :
    ⦃ ⌜ True ⌝ ⦄
      sqrt_u64.sqrt x
    ⦃ ⇓ r => ⌜ x.toNat < (r.toNat + 1) * (r.toNat + 1) ⌝ ⦄ := by
  sorry

/-- Totality / no-panic.

    **Proof status: `sorry` — Babylonian-descent body non-failure open**
    (closed for `x < 4` via `sqrt_small_no_failure`).

    For `x ≥ 4`, the preliminary computations
      * `>>>? (1 : i32)` — discharged by `decide`
      * `<<<? ((log2 a + 1) / 2)` — needs `log2 a ≤ 63` (have it from `log2_loop_triple`)
      * `(log2 a) +? 1` — needs `log2 a ≤ 63`
    are tractable, but the loop body requires `x ≥ 1` and `x.toNat ≤ 2^32`
    invariants which come from the AM-GM-style fixed-point analysis (same
    obstacle as `sqrt_lower_bound`).

    Structural unblock: the separately-verified `Nat.sqrt` development
    described in `sqrt_lower_bound`'s docstring would close this too. -/
theorem sqrt_no_failure (x : u64) :
    ∃ v : u64, sqrt_u64.sqrt x = RustM.ok v := by
  by_cases h : x < 4
  · exact sqrt_small_no_failure x h
  · sorry

end Sqrt_u64Obligations
