-- Companion obligations file for the `sqrt_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

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

/-! ## Helper lemma: `log2_rec` correctness

`log2_rec y count` returns `count + ⌊log₂ y⌋` (under the convention
`⌊log₂ 0⌋ = ⌊log₂ 1⌋ = 0`). Proof by strong induction on `y.toNat`. -/

@[simp] private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

/-- `Nat.log2 n ≤ 63` whenever `1 ≤ n < 2^64`. Used to discharge the
    `count + log2 < 2^32` precondition of `log2_rec_correct` for `u64` inputs. -/
private theorem nat_log2_le_63 (n : Nat) (h_pos : 0 < n) (h_lt : n < 2 ^ 64) :
    Nat.log2 n ≤ 63 := by
  have h_lt' : Nat.log2 n < 64 :=
    (Nat.log2_lt (Nat.pos_iff_ne_zero.mp h_pos)).mpr h_lt
  omega

/-- `2 ^ Nat.log2 n ≤ n` for `n ≥ 1`. Derived from `Nat.log2_lt`. -/
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

/-- Reduction of `(1 : u64) <<<? (k : u32)` when `k.toNat < 64`. -/
private theorem u64_shl_u32_reduce (k : UInt32) (h_lt : k.toNat < 64) :
    ((1 : u64) <<<? k : RustM u64) = pure ((1 : UInt64) <<< k.toNat.toUInt64) := by
  unfold rust_primitives.ops.bit.Shl.shl
  unfold instShlUInt64UInt32
  show (if (decide ((0 : UInt32) ≤ k) && decide (k < (64 : UInt32))) = true then
          pure ((1 : UInt64) <<< k.toNat.toUInt64)
        else RustM.fail Error.integerOverflow) = pure ((1 : UInt64) <<< k.toNat.toUInt64)
  have h_0_le : (0 : UInt32) ≤ k := by
    rw [UInt32.le_iff_toNat_le]; exact Nat.zero_le _
  have h_lt_64 : k < (64 : UInt32) := by
    rw [UInt32.lt_iff_toNat_lt]
    show k.toNat < (64 : UInt32).toNat
    have : (64 : UInt32).toNat = 64 := rfl
    rw [this]; exact h_lt
  rw [show (decide ((0 : UInt32) ≤ k) && decide (k < (64 : UInt32))) = true from by
    rw [decide_eq_true h_0_le, decide_eq_true h_lt_64]; rfl]
  simp only [if_true]

/-- For `k.toNat < 64`, `(1 : UInt64) <<< k = 2 ^ k.toNat` at the `Nat` level. -/
private theorem u64_one_shl_toNat (k : UInt64) (h : k.toNat < 64) :
    ((1 : UInt64) <<< k).toNat = 2 ^ k.toNat := by
  rw [UInt64.toNat_shiftLeft]
  show UInt64.toNat 1 <<< (k.toNat % 64) % 2 ^ 64 = 2 ^ k.toNat
  have h1 : UInt64.toNat 1 = 1 := rfl
  have h_mod : k.toNat % 64 = k.toNat := Nat.mod_eq_of_lt h
  rw [h1, h_mod, Nat.shiftLeft_eq, Nat.one_mul]
  have h_pow_lt : 2 ^ k.toNat < 2 ^ 64 :=
    Nat.pow_lt_pow_right (by decide : 1 < 2) h
  exact Nat.mod_eq_of_lt h_pow_lt

/-- `log2_rec y count = RustM.ok (count + Nat.log2 y.toNat)` provided
    the accumulator doesn't overflow. For `y.toNat ≤ 2^64 - 1`,
    `Nat.log2 y.toNat ≤ 63`. -/
private theorem log2_rec_correct (y : u64) (count : u32)
    (h_no_ovf : count.toNat + Nat.log2 y.toNat < 2 ^ 32) :
    sqrt_u64.log2_rec y count
      = RustM.ok (UInt32.ofNat (count.toNat + Nat.log2 y.toNat)) := by
  -- Induct on y.toNat.
  induction hk : y.toNat using Nat.strongRecOn generalizing y count with
  | _ k ih =>
    unfold sqrt_u64.log2_rec
    -- Reduce `(y <=? 1)` to `pure (decide (y ≤ 1))`.
    show ((y <=? (1 : u64)) >>= _) = _
    have h_le_eqq : (y <=? (1 : u64) : RustM Bool) = pure (decide (y ≤ 1)) := rfl
    rw [h_le_eqq]
    simp only [pure_bind]
    subst hk  -- Make ih reference y.toNat directly.
    by_cases hle : y ≤ 1
    · -- Base case: y ≤ 1, so Nat.log2 y.toNat = 0; returns pure count.
      simp only [decide_eq_true hle, if_true]
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
    · -- Step case: y > 1, recurse on (y >> 1, count + 1).
      simp only [decide_eq_false hle, Bool.false_eq_true, if_false]
      have h_y_ge_2 : 2 ≤ y.toNat := by
        have h_not_le : ¬ y.toNat ≤ 1 := fun h => hle (UInt64.le_iff_toNat_le.mpr h)
        omega
      -- Reduce `y >>>? 1` to `pure (y >>> 1)`.
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
      -- Reduce `count +? 1` to `pure (count + 1)`, using overflow bound.
      -- We have count.toNat + Nat.log2 y.toNat < 2^32 and Nat.log2 y.toNat ≥ 1
      -- (since y ≥ 2), so count.toNat < 2^32 - 1, so count + 1 doesn't overflow.
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
      -- Apply IH: (y >>> 1).toNat = y.toNat / 2 < y.toNat = k.
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
      -- IH gives log2_rec (y >> 1) (count + 1) = RustM.ok ...
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


/-! ## Master postcondition

The Rust source `sqrt : u64 → u64` returns the truncated integer square root.
Its contract is captured by two universal bounds on the result:

  * **Lower bound** — `r² ≤ x`,
  * **Upper bound** — `x < (r+1)²` (stated at the `Nat` level so that the
    "modulo u64 overflow" caveat from the Rust property test disappears —
    when `r = 2^32 − 1` the product `(r+1)*(r+1)` is exactly `2^64`, which
    still strictly exceeds `x.toNat ≤ 2^64 − 1`).

The function is total: no precondition is needed, since for every `u64`
input the math gives `r ≤ ⌊√(2^64 − 1)⌋ = 2^32 − 1`, well within the
output type. Failure modes (division by zero in the inner Babylonian step,
shift-overflow, integer overflow on `+`) are all ruled out by this bound
together with `log2 x ≤ 63`. -/

/-! ## Attempted attack on the master postcondition

Structural attack:

1. Split on `a < 4` (early-return arm) vs `a ≥ 4` (Babylonian arm).
2. For `a < 4`: closed by case analysis on `x.toNat ∈ {0, 1, 2, 3}`.
3. For `a ≥ 4`: requires Babylonian convergence — see status below.

### Progress made in this pass

The following helper theorems are now PROVED:

  - `log2_rec_correct` — the log2 helper computes `count + ⌊log₂ y⌋`.
  - `nat_amgm`, `nat_amgm_eq`, `nat_sum_sq_expand`, `nat_sum_sq_qd`,
    `nat_succ_sq`, `nat_4_mul_succ_sq` — Nat-level polynomial identities.
  - `nat_babylonian_lb` — the Newton-Raphson step never lands below
    `⌊√a⌋ − 1`. This is the mathematical core (≈ 80 lines).
  - `nat_iter_le_self_implies` — if `(a/x + x)/2 ≤ x`, then `a < (x+1)²`.
  - `nat_iter_ge_self_iff` — `x ≤ (a/x + x)/2 ↔ x*x ≤ a`.
  - `nat_iter_lt_self_of_sq_gt` — if `a < x*x`, then `(a/x+x)/2 < x`.
  - `sqrt_loop_up_spec` — full proof of the upward Babylonian loop.
  - `sqrt_loop_down_spec` — full proof of the downward Babylonian loop.

### Surviving sorry (sqrt_postcondition, `a ≥ 4` arm)

What remains is purely the **monadic-bind reduction chain** in the
`a ≥ 4` branch of `sqrt_postcondition`:

  log2 → +1 → /2 → <<<? → /? → +? → >>>? → sqrt_loop_up → sqrt_loop_down

This chain has three sub-sorries:

  (1) `h_pre_up` — existence of the initial state `(x0, xn0)` with
      `x0 = 2^((log2 x + 1)/2)`, `xn0 = (x/x0 + x0)/2`, and all
      overflow preconditions discharged.
  (2) `h_x1_small` — `2 * x1.toNat + 2 < 2^64` for loop_down's overflow
      precondition. Provable from a bound `x1 ≤ √x + 1 ≤ 2^32 + 1`
      which loop_up's postcondition would need to carry (it doesn't
      currently).
  (3) The final equation tying the monadic chain to `RustM.ok r`.

Each is mechanical: (1) and (3) follow the pattern from
`log2_rec_correct` for monadic reductions (≈ 200 lines for the seven
reductions). (2) needs strengthening `sqrt_loop_up_spec` to include
an upper bound on `x'`.

### Structural unblock

  (a) Strengthen `sqrt_loop_up_spec` postcondition with
      `x'.toNat ≤ max x.toNat (xn.toNat + 1)` (~10 extra lines in
      the proof; the IH naturally tracks this).
  (b) Write out the seven monadic-bind reductions in
      `sqrt_postcondition`'s big-case arm using the patterns already
      established (~200 lines). -/

/-! ## Babylonian step infrastructure and loop specs.

Helper theorems for `sqrt_postcondition`. The mathematical core
(`nat_babylonian_lb` and friends) plus the two loop specs
(`sqrt_loop_up_spec`, `sqrt_loop_down_spec`) are all fully proved
below. -/

/-! ## Nat-level Babylonian step lemma.

The mathematical core of the proof. For `0 < x` and any `a`, let
`f = (a/x + x) / 2` (Newton-Raphson next iterate). Then `(f+1)² > a`,
i.e. `f ≥ ⌊√a⌋` mod off-by-one. -/

/-- Polynomial-expansion lemma for `(q + x) * (q + x)`. Proved manually
    via `Nat.mul_add`/`Nat.add_mul`/`Nat.mul_comm` since `ring` is not
    available in this environment. -/
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
  -- LHS = (2q+d)² = 4q² + 4qd + d²
  -- RHS = 4 * (q² + qd) + d² = 4q² + 4qd + d²
  have h_lhs : (q + (q + d)) * (q + (q + d)) =
      q*q + q*(q+d) + q*(q+d) + (q+d)*(q+d) := by
    have := nat_sum_sq_expand q (q + d)
    -- = q*q + q*(q+d) + q*(q+d) + (q+d)*(q+d)
    omega
  have h_expand_q_qd : q * (q + d) = q * q + q * d := Nat.mul_add q q d
  have h_expand_qd_sq : (q + d) * (q + d) = q*q + q*d + q*d + d*d := nat_sum_sq_expand q d
  have h_rhs : 4 * (q * (q + d)) = 4 * (q * q) + 4 * (q * d) := by
    rw [h_expand_q_qd]; omega
  omega

private theorem nat_amgm (q x : Nat) :
    4 * (q * x) ≤ (q + x) * (q + x) := by
  have h_expand := nat_sum_sq_expand q x
  -- (q+x)² = q² + qx + qx + x² = q² + 2qx + x². Need ≥ 4qx, i.e., q² + x² ≥ 2qx.
  by_cases hqx : q ≤ x
  · obtain ⟨d, hd⟩ : ∃ d, x = q + d := ⟨x - q, by omega⟩
    have h_sum_sq : (q + (q + d)) * (q + (q + d)) = 4 * (q * (q + d)) + d * d :=
      nat_sum_sq_qd q d
    rw [← hd] at h_sum_sq
    have h_d_sq : d * d ≥ 0 := Nat.zero_le _
    omega
  · have hqx' : x < q := Nat.lt_of_not_le hqx
    obtain ⟨d, hd⟩ : ∃ d, q = x + d := ⟨q - x, by omega⟩
    -- (q+x)² = (x+d+x)² = (x + (x+d))² = 4*x*(x+d) + d² = 4*xq + d² = 4qx + d².
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

/-- Polynomial identity: `(k + 1) * (k + 1) = k * k + 2 * k + 1`. Manual since `ring` is unavailable. -/
private theorem nat_succ_sq (k : Nat) : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by
  have h := nat_sum_sq_expand k 1
  -- (k + 1) * (k + 1) = k*k + k*1 + k*1 + 1*1
  have h1 : k * 1 = k := Nat.mul_one k
  have h2 : (1 : Nat) * 1 = 1 := rfl
  omega

/-- `4 * ((f+1)² ) = (2*f + 2) * (2*f + 2)`. -/
private theorem nat_4_mul_succ_sq (f : Nat) :
    4 * ((f + 1) * (f + 1)) = (2 * f + 2) * (2 * f + 2) := by
  -- Both sides = 4*f² + 8*f + 4.
  have h_lhs : (f + 1) * (f + 1) = f * f + 2 * f + 1 := nat_succ_sq f
  have h_rhs : (2 * f + 2) * (2 * f + 2) = (2 * f) * (2 * f) + 2 * (2 * f) + 2 * (2 * f) + 4 := by
    have h := nat_sum_sq_expand (2 * f) 2
    have h22 : (2 : Nat) * 2 = 4 := rfl
    omega
  -- (2f)*(2f) = 4*f*f = 4*(f*f).
  have h_2fsq : (2 * f) * (2 * f) = 4 * (f * f) := by
    have : (2 * f) * (2 * f) = 2 * (f * (2 * f)) := Nat.mul_assoc 2 f (2 * f)
    rw [this]
    rw [show f * (2 * f) = 2 * (f * f) from by
      rw [show f * (2 * f) = (f * 2) * f from (Nat.mul_assoc f 2 f).symm,
          Nat.mul_comm f 2, Nat.mul_assoc]]
    rw [show (2 : Nat) * (2 * (f * f)) = 4 * (f * f) from by
      rw [← Nat.mul_assoc]]
  -- 2 * (2 * f) = 4 * f.
  have h_2_2f : 2 * (2 * f) = 4 * f := by
    rw [← Nat.mul_assoc]
  omega

/-- Cauchy-Schwarz / sum-of-squares bound:
    `(p+q)² ≤ 2 (p² + q²)` for `p q : Nat`. -/
private theorem nat_cauchy (p q : Nat) :
    (p + q) * (p + q) ≤ 2 * (p * p + q * q) := by
  -- Reduce to `2pq ≤ p² + q²`.
  have h_expand : (p + q) * (p + q) = p * p + p * q + p * q + q * q :=
    nat_sum_sq_expand p q
  by_cases hpq : p ≤ q
  · -- q = p + d for some d ≥ 0; (p² + q²) - 2pq = d².
    obtain ⟨d, hd⟩ : ∃ d, q = p + d := ⟨q - p, by omega⟩
    subst hd
    -- p * (p + d) = p² + p*d
    have h_pq : p * (p + d) = p * p + p * d := Nat.mul_add p p d
    -- (p + d)² = p² + p*d + p*d + d²
    have h_qq := nat_sum_sq_expand p d
    omega
  · -- p = q + e for some e > 0; symmetric.
    obtain ⟨d, hd⟩ : ∃ d, p = q + d := ⟨p - q, by omega⟩
    subst hd
    have h_pq : (q + d) * q = q * q + d * q := Nat.add_mul q d q
    have h_pp := nat_sum_sq_expand q d
    have h_comm : d * q = q * d := Nat.mul_comm d q
    omega

private theorem nat_babylonian_lb (a x : Nat) (hx : 0 < x) :
    a < ((a / x + x) / 2 + 1) * ((a / x + x) / 2 + 1) := by
  -- Notation aliases via local lets (no `set` tactic available).
  -- q = a / x, f = (a/x + x) / 2, d = |q - x|.
  -- Plan: show 4 * (f+1)² > 4a by chaining
  --   (2f+1)² ≥ (q+x)² = 4qx + d²,
  --   (2f+2)² = (2f+1)² + 4f + 3,
  --   4qx + 4x ≥ 4(a + 1) ⟹ 4qx ≥ 4a + 4 - 4x,
  --   4f ≥ 2(q+x) - 2 ⟹ 4f + 3 - 4x ≥ 2q - 2x + 1,
  -- so (2f+2)² ≥ 4a + d² + 2q - 2x + 5 > 4a (positivity of d² + 2q - 2x + 5).
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
  have h_2f_eq : 2 * ((a / x + x) / 2) = (a / x + x) / 2 * 2 := Nat.mul_comm _ _
  have h_sq_le : (2 * ((a / x + x) / 2) + 1) * (2 * ((a / x + x) / 2) + 1)
      ≥ (a / x + x) * (a / x + x) := Nat.mul_le_mul h_2f_lb h_2f_lb
  -- The d * d term from h_amgm_eq.
  have h_d_sq_ge_zero :
      (if a / x ≤ x then (x - a / x) * (x - a / x) else (a / x - x) * (a / x - x)) ≥ 0 :=
    Nat.zero_le _
  -- (2f+1)² ≥ 4 * q * x + d * d
  have h_2f1_sq_lb : (2 * ((a / x + x) / 2) + 1) * (2 * ((a / x + x) / 2) + 1)
      ≥ 4 * ((a / x) * x) + (if a / x ≤ x then (x - a / x) * (x - a / x)
                              else (a / x - x) * (a / x - x)) := by
    have h := h_sq_le
    omega
  -- Algebra: (2f+2)² = 4 * (f+1)². And (2f+2)² = (2f+1)² + 4f + 3.
  have h_4_f1_sq := nat_4_mul_succ_sq ((a / x + x) / 2)
  -- (2f + 2) * (2f + 2) = (2f+1+1)*(2f+1+1) using nat_succ_sq with k = 2f+1.
  have h_2f2 : (2 * ((a / x + x) / 2) + 2) * (2 * ((a / x + x) / 2) + 2)
      = (2 * ((a / x + x) / 2) + 1) * (2 * ((a / x + x) / 2) + 1)
        + 4 * ((a / x + x) / 2) + 3 := by
    have h_eq : 2 * ((a / x + x) / 2) + 2 = (2 * ((a / x + x) / 2) + 1) + 1 := by omega
    rw [h_eq]
    have := nat_succ_sq (2 * ((a / x + x) / 2) + 1)
    -- (k+1)*(k+1) = k*k + 2*k + 1 with k = 2f+1
    -- 2 * (2f+1) = 4f + 2
    have h_2k : 2 * (2 * ((a / x + x) / 2) + 1) = 4 * ((a / x + x) / 2) + 2 := by
      rw [Nat.mul_add, Nat.mul_one]
      rw [show 2 * (2 * ((a / x + x) / 2)) = 4 * ((a / x + x) / 2) from by
        rw [← Nat.mul_assoc]]
    omega
  -- Now combine.
  -- (2f+2)² ≥ 4qx + d² + 4f + 3, where d² ≥ 0.
  -- 4qx ≥ 4*a + 4 - 4*x (from h_qx_plus_x: 4*((a/x)*x + x) ≥ 4*(a+1))
  -- 4f ≥ 2*q + 2*x - 2 (from h_2f_lb)
  -- So (2f+2)² ≥ (4a + 4 - 4x) + d² + (2q + 2x - 2) + 3 = 4a + 5 + 2q - 2x + d²
  -- d² + 2q - 2x + 5 > 0:
  --   Case q ≤ x: d = x - q. d² - 2(x - q) + 5 = d² - 2d + 5. (d-1)² + 4 ≥ 4 > 0.
  --   Case q > x: 2q - 2x ≥ 2. 5 + 2q - 2x ≥ 7 > 0.
  have h_4qx_lb : 4 * ((a / x) * x) + 4 * x ≥ 4 * a + 4 := by
    have h := h_qx_plus_x; omega
  have h_4f_lb : 4 * ((a / x + x) / 2) ≥ 2 * (a / x) + 2 * x - 2 := by
    have h := h_2f_lb; omega
  -- Combine.
  have h_lhs_ge : (2 * ((a / x + x) / 2) + 2) * (2 * ((a / x + x) / 2) + 2)
      ≥ 4 * ((a / x) * x) + (if a / x ≤ x then (x - a / x) * (x - a / x)
                              else (a / x - x) * (a / x - x))
        + 4 * ((a / x + x) / 2) + 3 := by
    have h1 := h_2f1_sq_lb
    have h2 := h_2f2
    omega
  -- Show LHS > 4a.
  have h_gt : (2 * ((a / x + x) / 2) + 2) * (2 * ((a / x + x) / 2) + 2) > 4 * a := by
    -- Need: (RHS bound from h_lhs_ge) > 4a.
    -- RHS = 4qx + d² + 4f + 3.
    -- ≥ (4a + 4 - 4x) + d² + (2q + 2x - 2) + 3 = 4a + 5 + 2q - 2x + d².
    -- Show 5 + 2q - 2x + d² > 0.
    by_cases hqx : a / x ≤ x
    · -- d = x - a/x.
      have h_d_val : (if a / x ≤ x then (x - a / x) * (x - a / x)
                     else (a / x - x) * (a / x - x)) = (x - a / x) * (x - a / x) := by
        rw [if_pos hqx]
      rw [h_d_val] at h_lhs_ge
      -- d = x - a/x, then a/x + d = x.
      let d := x - a / x
      have hd_eq : d = x - a / x := rfl
      have hd_plus : d + a / x = x := by simp [hd_eq]; omega
      -- d * d + 2 * (a/x) - 2 * x + 5 = (d-1)² + 4 ≥ 4 > 0.
      -- Use: (d-1)*(d-1) = d*d - 2*d + 1 when d ≥ 1, or 0 when d = 0.
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
      -- Now omega should close it, using h_lhs_ge, h_4qx_lb, h_4f_lb, hd_plus, h_d_sq_lb.
      -- d * d in h_lhs_ge as (x - a/x) * (x - a/x). Let's substitute.
      have h_d_sq_eq : (x - a / x) * (x - a / x) = d * d := by simp [hd_eq]
      rw [h_d_sq_eq] at h_lhs_ge
      omega
    · -- a/x > x. d = a/x - x ≥ 1. 2*(a/x) - 2*x ≥ 2. So 5 + 2q - 2x ≥ 7 > 0.
      have hqx' : a / x > x := Nat.lt_of_not_le hqx
      have h_d_val : (if a / x ≤ x then (x - a / x) * (x - a / x)
                     else (a / x - x) * (a / x - x)) = (a / x - x) * (a / x - x) := by
        rw [if_neg hqx]
      rw [h_d_val] at h_lhs_ge
      have h_d_sq_ge : (a / x - x) * (a / x - x) ≥ 0 := Nat.zero_le _
      omega
  -- Convert (2f+2)² > 4a to 4*(f+1)² > 4a.
  have h_final : 4 * (((a / x + x) / 2 + 1) * ((a / x + x) / 2 + 1)) > 4 * a := by
    have h := h_4_f1_sq
    omega
  exact Nat.lt_of_mul_lt_mul_left h_final

/-- Corollary: if Newton-Raphson doesn't decrease (i.e. `iter ≤ x`), then we
    are above-or-at the integer root (`a < (x+1)²`). This is the loop_up
    exit-condition implication. -/
private theorem nat_iter_le_self_implies (a x : Nat) (hx : 0 < x)
    (h_le : (a / x + x) / 2 ≤ x) :
    a < (x + 1) * (x + 1) := by
  have h_lb := nat_babylonian_lb a x hx
  -- (a/x + x)/2 ≤ x, so ((a/x+x)/2 + 1)² ≤ (x+1)². And a < that.
  have h_sq_le : ((a / x + x) / 2 + 1) * ((a / x + x) / 2 + 1)
      ≤ (x + 1) * (x + 1) :=
    Nat.mul_le_mul (Nat.add_le_add_right h_le 1) (Nat.add_le_add_right h_le 1)
  omega

/-- Characterisation of loop_down's exit condition: `iter(a, x) ≥ x ↔ x² ≤ a`. -/
private theorem nat_iter_ge_self_iff (a x : Nat) (hx : 0 < x) :
    x ≤ (a / x + x) / 2 ↔ x * x ≤ a := by
  constructor
  · intro h
    -- (a/x + x) / 2 ≥ x iff a/x + x ≥ 2x iff a/x ≥ x iff a ≥ x*x.
    have h_sum_ge : a / x + x ≥ 2 * x := by
      have : 2 * x ≤ 2 * ((a/x + x)/2) := by omega
      have h_div2 : 2 * ((a/x + x)/2) ≤ a/x + x := by
        have := Nat.div_add_mod (a/x + x) 2
        omega
      omega
    have h_q_ge : a / x ≥ x := by omega
    -- a/x ≥ x means a ≥ x * x.
    have h_div_mul : x * (a / x) ≤ a := Nat.mul_div_le a x
    have h_step : x * x ≤ x * (a / x) := Nat.mul_le_mul_left x h_q_ge
    omega
  · intro h_xx_le
    -- a ≥ x*x means a/x ≥ x.
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

/-- Loop_down descent lemma: when `x² > a`, the iterate strictly decreases. -/
private theorem nat_iter_lt_self_of_sq_gt (a x : Nat) (hx : 0 < x)
    (h_sq_gt : a < x * x) :
    (a / x + x) / 2 < x := by
  -- iter < x iff a/x + x < 2x iff a/x < x iff a < x*x.
  have h_q_lt : a / x < x := by
    rcases Nat.lt_or_ge (a / x) x with h | h
    · exact h
    · exfalso
      have h_mul : x * x ≤ x * (a / x) := Nat.mul_le_mul_left x h
      have h_div_le : x * (a / x) ≤ a := Nat.mul_div_le a x
      omega
  have h_sum_lt : a / x + x < 2 * x := by omega
  have h_div_lt : (a / x + x) / 2 < (2 * x) / 2 := by
    rw [show (2 * x) / 2 = x from by rw [Nat.mul_comm]; exact Nat.mul_div_cancel x (by decide)]
    have : a / x + x ≤ 2 * x - 1 := by omega
    have h_half : (a / x + x) / 2 ≤ (2 * x - 1) / 2 := Nat.div_le_div_right this
    have h_simp : (2 * x - 1) / 2 = x - 1 := by
      have h_eq : 2 * x - 1 = 1 + 2 * (x - 1) := by omega
      rw [h_eq]
      rw [Nat.add_mul_div_left 1 (x - 1) (by decide : 0 < 2)]
      have : (1 : Nat) / 2 = 0 := by decide
      omega
    omega
  have h_2x : (2 * x) / 2 = x := by
    rw [Nat.mul_comm]; exact Nat.mul_div_cancel x (by decide)
  omega

/-! ## Loop specs.

These now use the correct invariants from the Babylonian analysis:
  * `sqrt_loop_up_spec` exit gives `a < (x'+1)²` (not `x'² ≥ a`).
  * `sqrt_loop_down_spec` precondition uses `a < (x+1)²`. -/

/-- `sqrt_loop_up` postcondition: starting from a Babylonian state
    `(x, xn)` with `xn = (a/x + x)/2` and `0 < x`, the loop terminates
    with `(x', xn')` satisfying the loop-down precondition.

    Termination measure: `a + 1 - x.toNat` (strictly decreases because
    `x' = xn > x` in the recursion branch).

    We track `0 < a.toNat` (to bound `xn ≥ 1` for subsequent iterations)
    and `x.toNat ≤ a.toNat + 1` (for measure boundedness; preserved
    because `iter ≤ a` always). The arithmetic overflow precondition
    `a.toNat / x.toNat + x.toNat < 2 ^ 64` is also tracked. -/
private theorem sqrt_loop_up_spec (a x xn : u64)
    (h_x_pos : 0 < x.toNat)
    (h_a_pos : 1 ≤ a.toNat)
    (h_x_le : x.toNat ≤ a.toNat)
    (h_xn_eq : xn.toNat = (a.toNat / x.toNat + x.toNat) / 2)
    (h_no_ovf : a.toNat / x.toNat + x.toNat < 2 ^ 64)
    (h_x_sq_lb : 4 * (x.toNat * x.toNat) ≥ a.toNat)
    (h_x_sq_ub : x.toNat * x.toNat ≤ 4 * a.toNat) :
    ∃ x' xn' : u64, sqrt_u64.sqrt_loop_up a x xn = RustM.ok ⟨x', xn'⟩ ∧
      xn'.toNat ≤ x'.toNat ∧
      0 < x'.toNat ∧
      xn'.toNat = (a.toNat / x'.toNat + x'.toNat) / 2 ∧
      a.toNat < (x'.toNat + 1) * (x'.toNat + 1) ∧
      x'.toNat * x'.toNat ≤ 4 * a.toNat := by
  -- Measure: a + 1 - x.toNat (strictly decreases since x' > x in recursion).
  induction hk : (a.toNat + 1 - x.toNat) using Nat.strongRecOn
    generalizing x xn with
  | _ k ih =>
    subst hk
    unfold sqrt_u64.sqrt_loop_up
    have h_lt_eqq : (x <? xn : RustM Bool) = pure (decide (x < xn)) := rfl
    rw [h_lt_eqq]
    simp only [pure_bind]
    by_cases hlt : x < xn
    · -- Recursive case: x < xn, iterate.
      simp only [decide_eq_true hlt, if_true]
      have h_x_lt_xn : x.toNat < xn.toNat := UInt64.lt_iff_toNat_lt.mp hlt
      -- The new state's x is xn, new xn is iter(a, xn).
      -- Reduce a /? xn (need xn > 0).
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
      -- Babylonian: a < (xn+1)² (since xn = iter(a, x)).
      have h_iter_lb : a.toNat < (xn.toNat + 1) * (xn.toNat + 1) := by
        have h_lb := nat_babylonian_lb a.toNat x.toNat h_x_pos
        rw [← h_xn_eq] at h_lb
        exact h_lb
      -- a/xn ≤ xn + 2.
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
      -- xn ≤ a + 2 (from h_iter_lb: a ≤ xn² + 2xn means xn² ≤ a, xn ≤ ⌈√a⌉ ≤ a+1).
      have h_xn_le_a : xn.toNat ≤ a.toNat := by
        -- xn ≤ a since xn² ≤ a + 2xn so xn(xn-2) ≤ a... actually need different bound.
        -- iter(a, x) = (a/x + x)/2 ≤ (a + x)/2 ≤ (a + a)/2 = a (assuming x ≤ a).
        rw [h_xn_eq]
        have h_div_le_a : a.toNat / x.toNat ≤ a.toNat := Nat.div_le_self a.toNat x.toNat
        have h_sum_le_2a : a.toNat / x.toNat + x.toNat ≤ 2 * a.toNat := by omega
        have h_half_le : (a.toNat / x.toNat + x.toNat) / 2 ≤ (2 * a.toNat) / 2 :=
          Nat.div_le_div_right h_sum_le_2a
        have h_simp : (2 * a.toNat) / 2 = a.toNat := by
          rw [Nat.mul_comm]; exact Nat.mul_div_cancel a.toNat (by decide)
        omega
      -- No overflow on a/xn + xn: 2*xn + 2.
      -- We need a/xn + xn < 2^64. Use: a/xn ≤ a ≤ 2^64 - 1, xn ≤ a ≤ 2^64 - 1, sum can overflow.
      -- TIGHTER: a/xn ≤ xn + 2 (Babylonian). Sum ≤ 2*xn + 2.
      -- For 2*xn + 2 < 2^64, need xn < 2^63 - 1.
      -- xn ≤ a / 2 + x ... hmm.
      -- Use h_no_ovf: a/x + x < 2^64. So xn = (a/x+x)/2 < 2^63.
      have h_xn_lt_2_63 : xn.toNat < 2 ^ 63 := by
        rw [h_xn_eq]
        have h_le : a.toNat / x.toNat + x.toNat ≤ 2 ^ 64 - 1 := by omega
        have h_div_le : (a.toNat / x.toNat + x.toNat) / 2 ≤ (2 ^ 64 - 1) / 2 :=
          Nat.div_le_div_right h_le
        have h_compute : (2 ^ 64 - 1) / 2 = 2 ^ 63 - 1 := by decide
        omega
      -- Issue: 2*xn + 2 could equal 2^64 if xn = 2^63 - 1. Need stricter bound.
      -- Use: a/xn + xn ≤ (xn + 2) + xn = 2*xn + 2.
      -- For xn ≤ 2^63 - 1: 2*xn + 2 ≤ 2^64. Equality at limit.
      -- Crucially, if xn = 2^63 - 1, then a/xn could be much less than xn + 2.
      -- Specifically, a ≤ 2^64 - 1 < 2*(2^63 - 1) * (2^63 - 1) for xn ≥ 2^32.
      --
      -- Workaround: also use that a/xn ≤ (2^64 - 1) / xn, get a tighter bound.
      -- Key: xn ≥ 2 in the recursion (since x ≥ 1 and x < xn), so
      -- a/xn * 2 ≤ a/xn * xn ≤ a ≤ 2^64 - 1, hence a/xn ≤ 2^63 - 1.
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
        -- a/xn * 2 ≤ a < 2^64, so a/xn ≤ (2^64 - 1)/2 = 2^63 - 1.
        omega
      have h_no_ovf_rec : a.toNat / xn.toNat + xn.toNat < 2 ^ 64 := by omega
      -- Reduce +? and >>>?.
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
      -- Strengthened invariants for the new state (xn, iter(a, xn)).
      -- (i)  4 * xn² ≥ a:  follows from `a ≤ xn² + 2xn` (nat_babylonian_lb)
      --      plus `xn ≥ 1`, since `3 xn² ≥ 2 xn` for `xn ≥ 1`.
      have h_xn_sq_lb_new : 4 * (xn.toNat * xn.toNat) ≥ a.toNat := by
        have h_succ : (xn.toNat + 1) * (xn.toNat + 1) = xn.toNat * xn.toNat + 2 * xn.toNat + 1 :=
          nat_succ_sq xn.toNat
        have h_a_le : a.toNat ≤ xn.toNat * xn.toNat + 2 * xn.toNat := by
          have := h_iter_lb; omega
        -- 3 xn² ≥ 2 xn for xn ≥ 1 (i.e., xn * (3 xn - 2) ≥ 0).
        have h_xn_sq_ge_xn : xn.toNat * xn.toNat ≥ xn.toNat * 1 :=
          Nat.mul_le_mul_left xn.toNat h_xn_pos
        omega
      -- (ii) xn² ≤ 4 a: from xn ≤ (a/x + x)/2 ≤ √(2·((a/x)² + x²)) ≤ √(16a) = 4√a.
      --      Concretely: 4 xn² ≤ (a/x + x)² ≤ 2((a/x)² + x²) ≤ 2(4a + 4a) = 16a.
      have h_xn_sq_ub_new : xn.toNat * xn.toNat ≤ 4 * a.toNat := by
        -- Step A: 2 * xn ≤ a/x + x.
        have h_2xn_le : 2 * xn.toNat ≤ a.toNat / x.toNat + x.toNat := by
          rw [h_xn_eq]
          have h := Nat.div_mul_le_self (a.toNat / x.toNat + x.toNat) 2
          omega
        -- Step B: (a/x)² ≤ 4 a (from 4 x² ≥ a and (a/x) * x ≤ a).
        have h_ax_sq_le : (a.toNat / x.toNat) * (a.toNat / x.toNat) ≤ 4 * a.toNat := by
          have h_div_mul : (a.toNat / x.toNat) * x.toNat ≤ a.toNat := Nat.div_mul_le_self _ _
          -- ((a/x) * x)² ≤ a²
          have h_sq : ((a.toNat / x.toNat) * x.toNat) * ((a.toNat / x.toNat) * x.toNat)
              ≤ a.toNat * a.toNat := Nat.mul_le_mul h_div_mul h_div_mul
          -- Rearrange: (a/x)² * x² ≤ a²
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
          -- Multiply h_sq by 4: (a/x)² * (4 x²) ≤ 4 * a²
          have h_4 : 4 * (((a.toNat / x.toNat) * (a.toNat / x.toNat)) * (x.toNat * x.toNat))
              ≤ 4 * (a.toNat * a.toNat) := Nat.mul_le_mul_left 4 h_sq
          have h_4_rearr : 4 * (((a.toNat / x.toNat) * (a.toNat / x.toNat)) * (x.toNat * x.toNat))
              = ((a.toNat / x.toNat) * (a.toNat / x.toNat)) * (4 * (x.toNat * x.toNat)) := by
            rw [← Nat.mul_assoc, Nat.mul_comm 4 _, Nat.mul_assoc]
          rw [h_4_rearr] at h_4
          -- Now h_4: (a/x)² * (4 x²) ≤ 4 a². Use 4 x² ≥ a:
          have h_mid : ((a.toNat / x.toNat) * (a.toNat / x.toNat)) * a.toNat
              ≤ ((a.toNat / x.toNat) * (a.toNat / x.toNat)) * (4 * (x.toNat * x.toNat)) :=
            Nat.mul_le_mul_left _ h_x_sq_lb
          -- Chain: (a/x)² * a ≤ 4 * a²
          have h_chain : ((a.toNat / x.toNat) * (a.toNat / x.toNat)) * a.toNat
              ≤ 4 * (a.toNat * a.toNat) := Nat.le_trans h_mid h_4
          -- Rearrange RHS: 4 * (a * a) = (4 * a) * a
          have h_eq : 4 * (a.toNat * a.toNat) = (4 * a.toNat) * a.toNat := by
            rw [← Nat.mul_assoc]
          rw [h_eq] at h_chain
          -- Cancel a > 0.
          exact Nat.le_of_mul_le_mul_right h_chain h_a_pos
        -- Step C: (a/x + x)² ≤ 2((a/x)² + x²)  [Cauchy]
        have h_cauchy_step := nat_cauchy (a.toNat / x.toNat) x.toNat
        -- Step D: combine. 4 xn² ≤ (2 xn)² ≤ (a/x + x)² ≤ 2(4a + 4a) = 16 a.
        have h_4xn_sq_le : (2 * xn.toNat) * (2 * xn.toNat)
            ≤ (a.toNat / x.toNat + x.toNat) * (a.toNat / x.toNat + x.toNat) :=
          Nat.mul_le_mul h_2xn_le h_2xn_le
        have h_2xn_sq : (2 * xn.toNat) * (2 * xn.toNat) = 4 * (xn.toNat * xn.toNat) := by
          have h1 : (2 * xn.toNat) * (2 * xn.toNat) = 2 * (xn.toNat * (2 * xn.toNat)) :=
            Nat.mul_assoc 2 xn.toNat (2 * xn.toNat)
          rw [h1, show xn.toNat * (2 * xn.toNat) = 2 * (xn.toNat * xn.toNat) from by
            rw [← Nat.mul_assoc, Nat.mul_comm xn.toNat 2, Nat.mul_assoc],
              ← Nat.mul_assoc]
        -- 2((a/x)² + x²) ≤ 2(4a + 4a) = 16a.
        have h_2_sum_le : 2 * ((a.toNat / x.toNat) * (a.toNat / x.toNat) + x.toNat * x.toNat)
            ≤ 2 * (4 * a.toNat + 4 * a.toNat) := by
          have h_add : (a.toNat / x.toNat) * (a.toNat / x.toNat) + x.toNat * x.toNat
              ≤ 4 * a.toNat + 4 * a.toNat := Nat.add_le_add h_ax_sq_le h_x_sq_ub
          exact Nat.mul_le_mul_left 2 h_add
        -- Combine: 4 xn² ≤ 16 a, so xn² ≤ 4 a.
        have h_combined : 4 * (xn.toNat * xn.toNat) ≤ 2 * (4 * a.toNat + 4 * a.toNat) := by
          rw [← h_2xn_sq]
          exact Nat.le_trans h_4xn_sq_le (Nat.le_trans h_cauchy_step h_2_sum_le)
        have h_16a : 2 * (4 * a.toNat + 4 * a.toNat) = 16 * a.toNat := by omega
        rw [h_16a] at h_combined
        -- 4 xn² ≤ 16 a ⟹ xn² ≤ 4 a (divide by 4).
        have : xn.toNat * xn.toNat ≤ 4 * a.toNat := by omega
        exact this
      -- Apply IH. New measure: a + 1 - xn.toNat < a + 1 - x.toNat (since xn > x).
      have h_measure_lt : a.toNat + 1 - xn.toNat < a.toNat + 1 - x.toNat := by
        omega
      obtain ⟨x', xn', h_eq', h_xn'_le, h_x'_pos, h_xn'_eq, h_x'_ub, h_x'_sq_ub⟩ :=
        ih (a.toNat + 1 - xn.toNat) h_measure_lt xn ((a / xn + xn) >>> (1 : UInt64))
          h_xn_pos h_xn_le_a h_new_xn_toNat h_no_ovf_rec h_xn_sq_lb_new h_xn_sq_ub_new rfl
      exact ⟨x', xn', h_eq', h_xn'_le, h_x'_pos, h_xn'_eq, h_x'_ub, h_x'_sq_ub⟩
    · -- Base case: x ≥ xn, exit.
      simp only [decide_eq_false hlt, Bool.false_eq_true, if_false]
      refine ⟨x, xn, rfl, ?_, h_x_pos, h_xn_eq, ?_, h_x_sq_ub⟩
      · -- xn.toNat ≤ x.toNat
        have h_not : ¬ x.toNat < xn.toNat := fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h)
        omega
      · -- a.toNat < (x.toNat + 1) * (x.toNat + 1) via nat_iter_le_self_implies
        have h_x_ge_xn : x.toNat ≥ xn.toNat := by
          have h_not : ¬ x.toNat < xn.toNat := fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h)
          omega
        have h_iter_le : (a.toNat / x.toNat + x.toNat) / 2 ≤ x.toNat := by
          rw [← h_xn_eq]; exact h_x_ge_xn
        exact nat_iter_le_self_implies a.toNat x.toNat h_x_pos h_iter_le

/-- `sqrt_loop_down` postcondition: starting from a state with the
    `a < (x+1)²` invariant and `xn = iter(a, x)`, the loop descends to
    `r = ⌊√a⌋`.

    Preconditions:
      * `0 < x.toNat` so divisions work.
      * `a.toNat < (x.toNat + 1) * (x.toNat + 1)` is the loop_down invariant.
      * `xn.toNat = iter(a, x)`.
      * `1 ≤ a.toNat` so recursive iterations don't hit `new_x = 0`.
      * `2 * x.toNat + 2 < 2 ^ 64` for arithmetic overflow safety
        (sum `a/x + x ≤ 2*x + 2` by Babylonian bound + invariant). -/
private theorem sqrt_loop_down_spec (a x xn : u64)
    (h_x_pos : 0 < x.toNat)
    (h_x_ub : a.toNat < (x.toNat + 1) * (x.toNat + 1))
    (h_xn_eq : xn.toNat = (a.toNat / x.toNat + x.toNat) / 2)
    (h_a_pos : 1 ≤ a.toNat)
    (h_x_small : 2 * x.toNat + 2 < 2 ^ 64) :
    ∃ r : u64, sqrt_u64.sqrt_loop_down a x xn = RustM.ok r ∧
      r.toNat * r.toNat ≤ a.toNat ∧
      a.toNat < (r.toNat + 1) * (r.toNat + 1) := by
  induction hk : x.toNat using Nat.strongRecOn generalizing x xn with
  | _ k ih =>
    subst hk
    unfold sqrt_u64.sqrt_loop_down
    have h_gt_eqq : (x >? xn : RustM Bool) = pure (decide (x > xn)) := rfl
    rw [h_gt_eqq]
    simp only [pure_bind]
    by_cases hgt : x > xn
    · -- Recursive case: x > xn, descend further.
      simp only [decide_eq_true hgt, if_true]
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
      -- Reduce a /? xn to pure (a / xn).
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
      -- a / xn ≤ xn + 2 (from h_iter_lb).
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
      -- xn ≤ x - 1 < x ≤ (2^64 - 2)/2 = 2^63 - 1. So 2*xn + 2 ≤ 2*x ≤ 2^64 - 2.
      have h_new_x_small : 2 * xn.toNat + 2 < 2 ^ 64 := by omega
      -- No overflow on a/xn + xn.
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
      -- Apply IH. h_a_pos doesn't depend on x/xn so it's not re-generalised
      -- by the induction; only h_x_pos, h_x_ub, h_xn_eq, h_x_small are.
      obtain ⟨r, hr_eq, hr_lb, hr_ub⟩ := ih xn.toNat h_xn_lt_x xn ((a / xn + xn) >>> (1 : UInt64))
        h_xn_pos h_iter_lb h_new_xn_toNat h_new_x_small rfl
      exact ⟨r, hr_eq, hr_lb, hr_ub⟩
    · -- Base case: x ≤ xn, exit.
      simp only [decide_eq_false hgt, Bool.false_eq_true, if_false]
      refine ⟨x, rfl, ?_, h_x_ub⟩
      have h_x_le_xn : x.toNat ≤ xn.toNat := by
        have h_not : ¬ x.toNat > xn.toNat := fun h => hgt (UInt64.lt_iff_toNat_lt.mpr h)
        omega
      have h_x_le_iter : x.toNat ≤ (a.toNat / x.toNat + x.toNat) / 2 := by
        rw [← h_xn_eq]; exact h_x_le_xn
      exact (nat_iter_ge_self_iff a.toNat x.toNat h_x_pos).mp h_x_le_iter

/-- Master existential: `sqrt x` returns some `r : u64` simultaneously
    satisfying the lower and upper bounds. Each individual contract clause
    below projects out of this lemma.

    The `a < 4` arm is closed directly by case analysis on `x.toNat`;
    the `a ≥ 4` arm requires the Babylonian-iteration correctness
    machinery and is left as `sorry` with the structural unblock above. -/
theorem sqrt_postcondition (x : u64) :
    ∃ r : u64, sqrt_u64.sqrt x = RustM.ok r ∧
      r.toNat * r.toNat ≤ x.toNat ∧
      x.toNat < (r.toNat + 1) * (r.toNat + 1) := by
  -- Step 1: unfold sqrt and dispatch on `x < 4`.
  unfold sqrt_u64.sqrt
  simp only []  -- inline the `have a := x` binding so the `rw` can fire
  show ∃ r, _ = RustM.ok r ∧ _ ∧ _
  rw [show (x <? (4 : u64) : RustM Bool) = pure (decide (x < 4)) from rfl]
  simp only [pure_bind]
  by_cases hlt : x < 4
  · -- Small-case arm: x.toNat ∈ {0, 1, 2, 3}.
    rw [decide_eq_true hlt]
    simp only [if_true]
    have h_gt_eqq : (x >? (0 : u64) : RustM Bool) = pure (decide (x > 0)) := rfl
    rw [h_gt_eqq]
    simp only [pure_bind]
    have hx_lt_4 : x.toNat < 4 := UInt64.lt_iff_toNat_lt.mp hlt
    by_cases hzero : x > 0
    · -- x > 0, so x.toNat ∈ {1, 2, 3}. Returns 1.
      rw [decide_eq_true hzero]
      simp only [if_true]
      refine ⟨1, rfl, ?_, ?_⟩
      · have h1 : (1 : u64).toNat = 1 := rfl
        rw [h1]
        have hpos : 0 < x.toNat := UInt64.lt_iff_toNat_lt.mp hzero
        omega
      · have h1 : (1 : u64).toNat = 1 := rfl
        rw [h1]
        omega
    · -- x = 0, returns 0.
      rw [decide_eq_false hzero]
      simp only [Bool.false_eq_true, if_false]
      refine ⟨0, rfl, ?_, ?_⟩
      · have h0 : (0 : u64).toNat = 0 := rfl; rw [h0]; omega
      · have h0 : (0 : u64).toNat = 0 := rfl; rw [h0]
        have hx_zero : x.toNat = 0 := by
          have h_not_pos : ¬ (0 < x.toNat) := fun h => hzero (UInt64.lt_iff_toNat_lt.mpr h)
          omega
        rw [hx_zero]; decide
  · -- Big-case arm (x ≥ 4): the Babylonian iteration.
    -- After by_cases on `x < 4`, this is the else branch. Reduce the if.
    rw [decide_eq_false hlt]
    simp only [Bool.false_eq_true, if_false]
    -- Basic bounds.
    have h_x_ge : 4 ≤ x.toNat := by
      have : ¬ x.toNat < 4 := fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h)
      omega
    have h_a_pos_master : 1 ≤ x.toNat := by omega
    have h_x_lt_2_64 : x.toNat < 2 ^ 64 := x.toNat_lt
    have h_log2_le_63 : Nat.log2 x.toNat ≤ 63 :=
      nat_log2_le_63 x.toNat h_a_pos_master h_x_lt_2_64
    have h_log2_ge_2 : Nat.log2 x.toNat ≥ 2 := by
      -- x.toNat ≥ 4 = 2^2 ⟹ log2 x ≥ 2.
      rcases Nat.lt_or_ge (Nat.log2 x.toNat) 2 with h | h
      · exfalso
        -- log2 x < 2 ⟹ x < 2^2 = 4 (by Nat.lt_pow_succ_log2 with bound).
        have h_x_lt_4 : x.toNat < 4 := by
          have h_lt_pow : x.toNat < 2 ^ (Nat.log2 x.toNat + 1) :=
            nat_lt_pow_succ_log2 x.toNat h_a_pos_master
          have h_pow_le : 2 ^ (Nat.log2 x.toNat + 1) ≤ 4 := by
            have h_le : Nat.log2 x.toNat + 1 ≤ 2 := by omega
            have := Nat.pow_le_pow_right (show 1 ≤ 2 from by decide) h_le
            have h_4 : 2 ^ 2 = 4 := by decide
            omega
          omega
        omega
      · exact h
    -- Step 1: reduce `log2 x` to `RustM.ok (UInt32.ofNat (Nat.log2 x.toNat))`.
    have h_log2_eq : sqrt_u64.log2 x = RustM.ok (UInt32.ofNat (Nat.log2 x.toNat)) := by
      show sqrt_u64.log2_rec x (0 : UInt32) = _
      have h := log2_rec_correct x (0 : UInt32) (by
        show (0 : UInt32).toNat + Nat.log2 x.toNat < 2 ^ 32
        have h0 : (0 : UInt32).toNat = 0 := rfl
        rw [h0]; omega)
      rw [h]
      have h0 : (0 : UInt32).toNat = 0 := rfl
      rw [h0, Nat.zero_add]
    rw [h_log2_eq]
    simp only [RustM_ok_bind]
    -- Step 2: reduce `(UInt32.ofNat (log2 x)) +? 1`.
    have h_log2x_toNat : (UInt32.ofNat (Nat.log2 x.toNat)).toNat = Nat.log2 x.toNat :=
      UInt32.toNat_ofNat_of_lt' (by omega : Nat.log2 x.toNat < 2 ^ 32)
    have h_add1 : (UInt32.ofNat (Nat.log2 x.toNat) +? (1 : u32) : RustM u32)
        = pure (UInt32.ofNat (Nat.log2 x.toNat) + 1) := by
      show (rust_primitives.ops.arith.Add.add (UInt32.ofNat (Nat.log2 x.toNat)) (1 : u32) : RustM u32)
           = pure (UInt32.ofNat (Nat.log2 x.toNat) + 1)
      show (if BitVec.uaddOverflow (UInt32.ofNat (Nat.log2 x.toNat)).toBitVec (1 : u32).toBitVec then
              (.fail .integerOverflow : RustM u32)
            else pure (UInt32.ofNat (Nat.log2 x.toNat) + 1)) = _
      have h_no_ovf : BitVec.uaddOverflow (UInt32.ofNat (Nat.log2 x.toNat)).toBitVec
                        (1 : u32).toBitVec = false := by
        cases h_eq : BitVec.uaddOverflow (UInt32.ofNat (Nat.log2 x.toNat)).toBitVec
                        (1 : u32).toBitVec with
        | false => rfl
        | true =>
          exfalso
          have : UInt32.addOverflow (UInt32.ofNat (Nat.log2 x.toNat)) (1 : u32) = true := h_eq
          rw [UInt32.addOverflow_iff] at this
          have h1 : (1 : UInt32).toNat = 1 := rfl
          rw [h_log2x_toNat, h1] at this
          omega
      rw [h_no_ovf]; rfl
    rw [h_add1]
    simp only [pure_bind]
    have h_log2_1_toNat : (UInt32.ofNat (Nat.log2 x.toNat) + 1).toNat
                          = Nat.log2 x.toNat + 1 := by
      have h1 : (1 : UInt32).toNat = 1 := rfl
      have h_no_ovf : (UInt32.ofNat (Nat.log2 x.toNat)).toNat + (1 : UInt32).toNat < 2 ^ 32 := by
        rw [h_log2x_toNat, h1]; omega
      have h_eq := UInt32.toNat_add_of_lt h_no_ovf
      rw [h_eq, h_log2x_toNat, h1]
    -- Step 3: reduce `(...) /? 2`.
    have h_div2 : ((UInt32.ofNat (Nat.log2 x.toNat) + 1) /? (2 : u32) : RustM u32)
        = pure ((UInt32.ofNat (Nat.log2 x.toNat) + 1) / 2) := by
      show (rust_primitives.ops.arith.Div.div (UInt32.ofNat (Nat.log2 x.toNat) + 1) (2 : u32)
            : RustM u32)
           = pure ((UInt32.ofNat (Nat.log2 x.toNat) + 1) / 2)
      show (if (2 : u32) = 0 then (.fail .divisionByZero : RustM u32)
            else pure ((UInt32.ofNat (Nat.log2 x.toNat) + 1) / 2)) = _
      rw [if_neg (by decide : (2 : u32) ≠ 0)]
    rw [h_div2]
    simp only [pure_bind]
    -- Define k_nat = (Nat.log2 x.toNat + 1) / 2.
    -- It satisfies: 2 ≤ log2 x + 1 (so k_nat ≥ 1), and k_nat ≤ 32.
    have h_k_toNat : ((UInt32.ofNat (Nat.log2 x.toNat) + 1) / 2).toNat
                     = (Nat.log2 x.toNat + 1) / 2 := by
      rw [UInt32.toNat_div, h_log2_1_toNat]
      have h2 : (2 : UInt32).toNat = 2 := rfl
      rw [h2]
    have h_k_ge_1 : 1 ≤ (Nat.log2 x.toNat + 1) / 2 := by
      have h_le : 2 ≤ Nat.log2 x.toNat + 1 := by omega
      have : (2 : Nat) / 2 ≤ (Nat.log2 x.toNat + 1) / 2 := Nat.div_le_div_right h_le
      have h_2_div : (2 : Nat) / 2 = 1 := by decide
      omega
    have h_k_le_32 : (Nat.log2 x.toNat + 1) / 2 ≤ 32 := by
      have h_le : Nat.log2 x.toNat + 1 ≤ 64 := by omega
      have : (Nat.log2 x.toNat + 1) / 2 ≤ 64 / 2 := Nat.div_le_div_right h_le
      have h_64_div : (64 : Nat) / 2 = 32 := by decide
      omega
    have h_k_u32_lt_64 : ((UInt32.ofNat (Nat.log2 x.toNat) + 1) / 2).toNat < 64 := by
      rw [h_k_toNat]; omega
    -- Step 4: reduce `(1 : u64) <<<? k_u32`.
    have h_shl_x0 := u64_shl_u32_reduce ((UInt32.ofNat (Nat.log2 x.toNat) + 1) / 2)
                     h_k_u32_lt_64
    rw [h_shl_x0]
    simp only [pure_bind]
    -- Compute x0.toNat = 2 ^ k_nat.
    -- The shift amount in u64 is k.toNat.toUInt64 : UInt64.
    have h_k_toUInt64_toNat : (((UInt32.ofNat (Nat.log2 x.toNat) + 1) / 2).toNat.toUInt64).toNat
                              = (Nat.log2 x.toNat + 1) / 2 := by
      rw [h_k_toNat]
      exact UInt64.toNat_ofNat_of_lt' (by
        have : (Nat.log2 x.toNat + 1) / 2 ≤ 32 := h_k_le_32
        omega : (Nat.log2 x.toNat + 1) / 2 < 2 ^ 64)
    have h_x0_expr_toNat : ((1 : UInt64) <<<
                        (((UInt32.ofNat (Nat.log2 x.toNat) + 1) / 2).toNat.toUInt64)).toNat
                      = 2 ^ ((Nat.log2 x.toNat + 1) / 2) := by
      have h_lt : (((UInt32.ofNat (Nat.log2 x.toNat) + 1) / 2).toNat.toUInt64).toNat < 64 := by
        rw [h_k_toUInt64_toNat]; omega
      rw [u64_one_shl_toNat _ h_lt, h_k_toUInt64_toNat]
    -- Generalize x0 = (1 : UInt64) <<< (...) so subsequent proofs are readable.
    generalize x0_def : (1 : UInt64) <<<
      (((UInt32.ofNat (Nat.log2 x.toNat) + 1) / 2).toNat.toUInt64) = x0
    rw [x0_def] at h_x0_expr_toNat
    -- Now h_x0_expr_toNat : x0.toNat = 2 ^ ((Nat.log2 x.toNat + 1) / 2).
    have h_x0_eq : x0.toNat = 2 ^ ((Nat.log2 x.toNat + 1) / 2) := h_x0_expr_toNat
    have h_x0_pos : 0 < x0.toNat := by
      rw [h_x0_eq]; exact Nat.pow_pos (by decide : 0 < 2)
    have h_x0_ge_2 : 2 ≤ x0.toNat := by
      rw [h_x0_eq]
      have : 2 ^ 1 ≤ 2 ^ ((Nat.log2 x.toNat + 1) / 2) :=
        Nat.pow_le_pow_right (by decide) h_k_ge_1
      have h_p1 : (2 : Nat) ^ 1 = 2 := by decide
      omega
    have h_x0_le_2_32 : x0.toNat ≤ 2 ^ 32 := by
      rw [h_x0_eq]
      exact Nat.pow_le_pow_right (by decide) h_k_le_32
    -- Bridge: 2 * k_nat is between log2 x and log2 x + 1 (inclusive).
    have h_2k_ge : 2 * ((Nat.log2 x.toNat + 1) / 2) ≥ Nat.log2 x.toNat := by
      have h_d := Nat.div_add_mod (Nat.log2 x.toNat + 1) 2
      have h_m_lt : (Nat.log2 x.toNat + 1) % 2 < 2 := Nat.mod_lt _ (by decide)
      omega
    have h_2k_le : 2 * ((Nat.log2 x.toNat + 1) / 2) ≤ Nat.log2 x.toNat + 1 := by
      have h_d := Nat.div_mul_le_self (Nat.log2 x.toNat + 1) 2
      omega
    -- x0^2 = 2^(2 * k_nat).
    have h_x0_sq_eq : x0.toNat * x0.toNat = 2 ^ (2 * ((Nat.log2 x.toNat + 1) / 2)) := by
      rw [h_x0_eq, ← Nat.pow_add]
      congr 1; omega
    -- 2^(log2 x) ≤ x.toNat ≤ ... 2^(log2 x + 1).
    have h_pow_log_le : 2 ^ Nat.log2 x.toNat ≤ x.toNat :=
      nat_pow_log2_le x.toNat h_a_pos_master
    have h_x_lt_pow : x.toNat < 2 ^ (Nat.log2 x.toNat + 1) :=
      nat_lt_pow_succ_log2 x.toNat h_a_pos_master
    -- x0^2 ≤ 2^(log2 x + 1) ≤ 2 * x.toNat ≤ 4 * x.toNat.
    have h_x0_sq_le_4x : x0.toNat * x0.toNat ≤ 4 * x.toNat := by
      rw [h_x0_sq_eq]
      have h_le_log_p1 : 2 ^ (2 * ((Nat.log2 x.toNat + 1) / 2))
          ≤ 2 ^ (Nat.log2 x.toNat + 1) :=
        Nat.pow_le_pow_right (by decide) h_2k_le
      have h_pow_le_2x : 2 ^ (Nat.log2 x.toNat + 1) ≤ 2 * x.toNat := by
        rw [Nat.pow_succ]
        have h_comm : 2 ^ Nat.log2 x.toNat * 2 = 2 * 2 ^ Nat.log2 x.toNat := Nat.mul_comm _ _
        omega
      omega
    -- 4 * x0^2 ≥ x.toNat (since 4 * 2^(2k) ≥ 4 * 2^log = 2^(log+2) > x).
    have h_4_x0_sq_ge_x : 4 * (x0.toNat * x0.toNat) ≥ x.toNat := by
      rw [h_x0_sq_eq]
      have h_ge_log : 2 ^ Nat.log2 x.toNat ≤ 2 ^ (2 * ((Nat.log2 x.toNat + 1) / 2)) :=
        Nat.pow_le_pow_right (by decide) h_2k_ge
      have h_mul_4 : 4 * 2 ^ Nat.log2 x.toNat ≤
                     4 * 2 ^ (2 * ((Nat.log2 x.toNat + 1) / 2)) :=
        Nat.mul_le_mul_left 4 h_ge_log
      -- 4 * 2^log = 2^(log + 2).
      have h_4_pow_eq : 4 * 2 ^ Nat.log2 x.toNat = 2 ^ (Nat.log2 x.toNat + 2) := by
        have h4 : (4 : Nat) = 2 ^ 2 := by decide
        rw [h4, ← Nat.pow_add]
        congr 1; omega
      rw [h_4_pow_eq] at h_mul_4
      -- 2^(log+2) = 2 * 2^(log+1) ≥ 2 * (x + 1) > x.
      have h_pow_succ_eq : 2 ^ (Nat.log2 x.toNat + 2) = 2 * 2 ^ (Nat.log2 x.toNat + 1) := by
        rw [show Nat.log2 x.toNat + 2 = (Nat.log2 x.toNat + 1) + 1 from by omega,
            Nat.pow_succ, Nat.mul_comm]
      have h_2_pow_ge : 2 ^ (Nat.log2 x.toNat + 2) ≥ x.toNat := by
        rw [h_pow_succ_eq]
        have h_x_lt : x.toNat < 2 ^ (Nat.log2 x.toNat + 1) := h_x_lt_pow
        omega
      omega
    -- x0 ≤ x.toNat (since x0² ≤ 4x ≤ x*x for x ≥ 4).
    have h_x0_le_x : x0.toNat ≤ x.toNat := by
      rcases Nat.lt_or_ge x.toNat x0.toNat with h_lt | h_ge
      · exfalso
        have h_x0_ge : x.toNat + 1 ≤ x0.toNat := h_lt
        have h_sq_ge : x0.toNat * x0.toNat ≥ (x.toNat + 1) * (x.toNat + 1) :=
          Nat.mul_le_mul h_x0_ge h_x0_ge
        have h_succ_sq : (x.toNat + 1) * (x.toNat + 1) = x.toNat * x.toNat + 2 * x.toNat + 1 :=
          nat_succ_sq x.toNat
        have h_x_sq_ge_4x : 4 * x.toNat ≤ x.toNat * x.toNat := by
          rw [Nat.mul_comm 4 x.toNat]
          exact Nat.mul_le_mul_left _ h_x_ge
        omega
      · exact h_ge
    -- Overflow check: x.toNat / x0.toNat + x0.toNat < 2^64.
    have h_no_ovf_init : x.toNat / x0.toNat + x0.toNat < 2 ^ 64 := by
      -- x / x0 ≤ x and x0 ≤ x, so sum ≤ 2x. But 2x could overflow.
      -- Tighter: x / x0 ≤ 4 x0 (since 4 x0² ≥ x). So sum ≤ 5 x0 ≤ 5 * 2^32 < 2^64.
      have h_div_le : x.toNat / x0.toNat ≤ 4 * x0.toNat := by
        -- x ≤ 4 x0² (lower bound). So x / x0 ≤ 4 x0.
        have h_x_le_4_x0_sq : x.toNat ≤ 4 * (x0.toNat * x0.toNat) := h_4_x0_sq_ge_x
        have h_div_le_4_x0 : x.toNat / x0.toNat ≤ (4 * (x0.toNat * x0.toNat)) / x0.toNat :=
          Nat.div_le_div_right h_x_le_4_x0_sq
        have h_simp : (4 * (x0.toNat * x0.toNat)) / x0.toNat = 4 * x0.toNat := by
          rw [show 4 * (x0.toNat * x0.toNat) = (4 * x0.toNat) * x0.toNat from by
            rw [Nat.mul_assoc]]
          exact Nat.mul_div_cancel (4 * x0.toNat) h_x0_pos
        omega
      have h_sum_le : x.toNat / x0.toNat + x0.toNat ≤ 5 * x0.toNat := by omega
      have h_5_x0_le : 5 * x0.toNat ≤ 5 * 2 ^ 32 := Nat.mul_le_mul_left 5 h_x0_le_2_32
      have h_5_pow_lt : 5 * 2 ^ 32 < 2 ^ 64 := by decide
      omega
    -- Step 5: reduce `x /? x0`.
    have h_x0_ne_zero : x0 ≠ 0 := by
      intro hcon
      have : x0.toNat = 0 := by rw [hcon]; rfl
      omega
    have h_div_x_x0 : (x /? x0 : RustM u64) = pure (x / x0) := by
      show (rust_primitives.ops.arith.Div.div x x0 : RustM u64) = pure (x / x0)
      show (if x0 = 0 then (.fail .divisionByZero : RustM u64) else pure (x / x0)) = _
      rw [if_neg h_x0_ne_zero]
    rw [h_div_x_x0]
    simp only [pure_bind]
    have h_x_div_x0_toNat : (x / x0).toNat = x.toNat / x0.toNat := UInt64.toNat_div x x0
    -- Step 6: reduce `(x / x0) +? x0`.
    have h_add_x_x0 : ((x / x0) +? x0 : RustM u64) = pure ((x / x0) + x0) := by
      show (rust_primitives.ops.arith.Add.add (x / x0) x0 : RustM u64) = pure ((x / x0) + x0)
      show (if BitVec.uaddOverflow (x / x0).toBitVec x0.toBitVec then
              (.fail .integerOverflow : RustM u64)
            else pure ((x / x0) + x0)) = _
      have h_no_ovf : BitVec.uaddOverflow (x / x0).toBitVec x0.toBitVec = false := by
        cases h_eq : BitVec.uaddOverflow (x / x0).toBitVec x0.toBitVec with
        | false => rfl
        | true =>
          exfalso
          have : UInt64.addOverflow (x / x0) x0 = true := h_eq
          rw [UInt64.addOverflow_iff] at this
          rw [h_x_div_x0_toNat] at this
          omega
      rw [h_no_ovf]; rfl
    rw [h_add_x_x0]
    simp only [pure_bind]
    have h_sum_toNat : ((x / x0) + x0).toNat = x.toNat / x0.toNat + x0.toNat := by
      apply UInt64.toNat_add_of_lt
      rw [h_x_div_x0_toNat]; exact h_no_ovf_init
    -- Step 7: reduce `(...) >>>? (1 : i32)`.
    have h_shr_xn0 : (((x / x0) + x0) >>>? (1 : i32) : RustM u64)
        = pure (((x / x0) + x0) >>> (1 : UInt64)) := by
      show (rust_primitives.ops.bit.Shr.shr ((x / x0) + x0) (1 : i32) : RustM u64) = _
      show (if ((0 : Int32) ≤ (1 : Int32) && (1 : Int32) < 64) then
              pure (((x / x0) + x0) >>> ((1 : Int32).toNatClampNeg.toUInt64))
            else .fail .integerOverflow) = pure (((x / x0) + x0) >>> (1 : UInt64))
      rw [show ((0 : Int32) ≤ (1 : Int32) && (1 : Int32) < 64) = true from rfl]
      simp only [if_true]
      have : (1 : Int32).toNatClampNeg.toUInt64 = (1 : UInt64) := rfl
      rw [this]
    rw [h_shr_xn0]
    simp only [pure_bind]
    -- Compute xn0.toNat for the (((x / x0) + x0) >>> 1) expression.
    have h_xn0_expr_toNat : (((x / x0) + x0) >>> (1 : UInt64)).toNat
        = (x.toNat / x0.toNat + x0.toNat) / 2 := by
      rw [UInt64.toNat_shiftRight, UInt64.toNat_one]
      show ((x / x0) + x0).toNat >>> (1 % 64) = _
      rw [show (1 % 64 : Nat) = 1 from rfl, Nat.shiftRight_eq_div_pow,
          show (2 ^ 1 : Nat) = 2 from rfl, h_sum_toNat]
    -- Generalize xn0 = ((x/x0) + x0) >>> 1.
    generalize xn0_def : ((x / x0) + x0) >>> (1 : UInt64) = xn0
    rw [xn0_def] at h_xn0_expr_toNat
    have h_xn0_toNat : xn0.toNat = (x.toNat / x0.toNat + x0.toNat) / 2 := h_xn0_expr_toNat
    -- Step 8: apply sqrt_loop_up_spec.
    obtain ⟨x1, xn1, h_up_eq, h_xn1_le, h_x1_pos, h_xn1_eq, h_x1_ub, h_x1_sq_ub⟩ :=
      sqrt_loop_up_spec x x0 xn0 h_x0_pos h_a_pos_master h_x0_le_x h_xn0_toNat h_no_ovf_init
        h_4_x0_sq_ge_x h_x0_sq_le_4x
    -- Derive x1 small bound from x1² ≤ 4 * x.toNat.
    have h_x1_small : 2 * x1.toNat + 2 < 2 ^ 64 := by
      -- x1² ≤ 4 x ≤ 4 * (2^64 - 1) = 2^66 - 4. So x1 ≤ √(2^66) = 2^33. So 2 x1 + 2 ≤ 2^34 < 2^64.
      have h_x1_sq_lt : x1.toNat * x1.toNat < 2 ^ 66 := by
        have h_4x_lt : 4 * x.toNat < 4 * 2 ^ 64 :=
          (Nat.mul_lt_mul_left (by decide : 0 < 4)).mpr h_x_lt_2_64
        have h_4_2_64 : 4 * (2 : Nat) ^ 64 = 2 ^ 66 := by decide
        omega
      -- If 2 x1 + 2 ≥ 2^64, then x1 ≥ 2^63 - 1, so x1² ≥ (2^63 - 1)² > 2^66. Contradiction.
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
    -- Step 9: apply sqrt_loop_down_spec.
    obtain ⟨r, h_down_eq, hlb, hub⟩ :=
      sqrt_loop_down_spec x x1 xn1 h_x1_pos h_x1_ub h_xn1_eq h_a_pos_master h_x1_small
    -- Tie the chain to RustM.ok r.
    refine ⟨r, ?_, hlb, hub⟩
    -- The goal at this point: `sqrt_loop_up x x0 xn0 >>= ... = RustM.ok r`.
    rw [h_up_eq]
    simp only [RustM_ok_bind]
    exact h_down_eq

/-! ## Contract clauses derived from the master postcondition. -/

/-- Totality / no-panic. The Rust source has no `panic!`; failure modes
    (`/?` divisor of zero on the initial guess and each Babylonian step,
    `+?` overflow on `a/x + x`, `>>>?` shift-overflow on the halving,
    `<<<?` shift-overflow on the initial guess) are all ruled out by the
    fact that on the `a ≥ 4` branch the function holds `x ≥ 1` invariantly
    and the shift amount is `≤ 63`. -/
theorem sqrt_total (x : u64) :
    ∃ r : u64, sqrt_u64.sqrt x = RustM.ok r := by
  obtain ⟨r, hr, _, _⟩ := sqrt_postcondition x
  exact ⟨r, hr⟩

/-- Lower bound (independent clause): `sqrt(x)² ≤ x`. Captures the property
    test `prop_sqrt_lower_bound` directly. A buggy implementation that
    returns too large a value (e.g. `x` itself for `x ≥ 2`, or `sqrt x + 1`
    on non-perfect squares) is caught here. Stated at `Nat`-level so that
    the `checked_mul` guard from the Rust test (which only triggers for
    incorrect oversize results) drops out. -/
theorem sqrt_lower_bound (x : u64) :
    ∃ r : u64, sqrt_u64.sqrt x = RustM.ok r ∧
      r.toNat * r.toNat ≤ x.toNat := by
  obtain ⟨r, hr, hlb, _⟩ := sqrt_postcondition x
  exact ⟨r, hr, hlb⟩

/-- Upper bound (independent clause): `x < (sqrt(x) + 1)²`. Captures the
    property test `prop_sqrt_upper_bound`. Independent from the lower
    bound: an implementation that always returns `0` would pass the lower
    bound but fail this one. Stated at `Nat`-level: the Rust test's
    "modulo overflow" vacuous case (when `(r+1)*(r+1)` doesn't fit in
    `u64`) becomes the genuine inequality `x.toNat < (r+1)*(r+1)` in
    `Nat`, which still holds since `x.toNat < 2^64 ≤ (r+1)*(r+1)` when
    `r = 2^32 − 1`. -/
theorem sqrt_upper_bound (x : u64) :
    ∃ r : u64, sqrt_u64.sqrt x = RustM.ok r ∧
      x.toNat < (r.toNat + 1) * (r.toNat + 1) := by
  obtain ⟨r, hr, _, hub⟩ := sqrt_postcondition x
  exact ⟨r, hr, hub⟩

/-! ## Boundary cases (small-input early-return arm)

The Rust source dispatches `a < 4` via an explicit early-return that
sidesteps the Babylonian iteration: `sqrt 0 = 0`, `sqrt {1,2,3} = 1`.
These are corollaries of the master postcondition but pin the explicit
code path that the loop helpers never see. From the `sqrt_small` test. -/

/-- Boundary case `sqrt 0 = 0`. Pins the `a = 0` arm of the early-return
    branch (`if a > 0 ... else 0`). Captures `sqrt(0) = 0` from
    `sqrt_small`. -/
theorem sqrt_zero : sqrt_u64.sqrt 0 = RustM.ok 0 := by
  unfold sqrt_u64.sqrt
  rfl

/-- Boundary case `sqrt 1 = 1`. Pins the `0 < a < 4` arm of the
    early-return branch. Captures `sqrt(1) = 1` from `sqrt_small`.
    The value `1` is the simplest perfect square. -/
theorem sqrt_one : sqrt_u64.sqrt 1 = RustM.ok 1 := by
  unfold sqrt_u64.sqrt
  rfl

end Sqrt_u64Obligations
