-- Companion obligations file for the `sum_to_n` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import sum_to_n

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Sum_to_nObligations

/-- Auxiliary arithmetic identity: the `Nat`-level Gauss recurrence.
    For `k ≥ 1`, `k * (k + 1) / 2 = k + (k - 1) * k / 2`. Used in the
    inductive step of `sum_to_n_compute` to relate the closed form at
    `k` to the closed form at `k - 1`. -/
private theorem gauss_step (k : Nat) (hk : 1 ≤ k) :
    k * (k + 1) / 2 = k + (k - 1) * k / 2 := by
  have e1 : (k - 1) * k + 2 * k = k * (k + 1) := by
    rw [← Nat.add_mul]
    have hsucc : k - 1 + 2 = k + 1 := by omega
    rw [hsucc, Nat.mul_comm]
  have e2 : ((k - 1) * k + 2 * k) / 2 = (k - 1) * k / 2 + k :=
    Nat.add_mul_div_left ((k - 1) * k) k (by decide : 0 < 2)
  rw [← e1, e2, Nat.add_comm]

/-- Workhorse characterization, by strong induction on `n.toNat`.
    `sum_to_n n` returns `.ok` of the Gauss closed form when it fits
    in `u64`, and `.fail .integerOverflow` otherwise. Both contract
    theorems below are 1-line corollaries: `if_pos` for the
    postcondition, `if_neg` for the failure case. -/
private theorem sum_to_n_compute (n : u64) :
    sum_to_n.sum_to_n n =
      if n.toNat * (n.toNat + 1) / 2 < 2 ^ 64 then
        RustM.ok (UInt64.ofNat (n.toNat * (n.toNat + 1) / 2))
      else
        RustM.fail .integerOverflow := by
  induction hk : n.toNat using Nat.strongRecOn generalizing n
  rename_i k ih
  rw [sum_to_n.sum_to_n]
  by_cases hk_zero : k = 0
  · -- Base case: k = 0, hence n = 0; both sides reduce by `decide`.
    have hn0 : n = 0 := by
      apply UInt64.toNat_inj.mp
      simp [hk, hk_zero]
    subst hn0
    subst hk_zero
    decide
  · -- Inductive case: k > 0; peel one recursive call, apply IH, split on the
    -- closed-form bound to discharge the addition's overflow flag.
    have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_zero
    have hn_pos : 0 < n.toNat := hk ▸ hk_pos
    have hn_ne_zero : ¬ (n == 0) = true := by
      intro hh
      have heq : n = 0 := by simpa [BEq.beq] using hh
      rw [heq] at hn_pos
      simp at hn_pos
    have hsubOK : ¬ UInt64.subOverflow n 1 = true := by
      simp only [UInt64.subOverflow_iff, UInt64.toNat_one]
      omega
    have hsubn : n -? 1 = pure (n - 1) := by
      show (rust_primitives.ops.arith.Sub.sub n 1 : RustM u64) = pure (n - 1)
      show (if BitVec.usubOverflow n.toBitVec (1 : UInt64).toBitVec then
              (.fail .integerOverflow : RustM u64)
            else pure (n - 1)) = pure (n - 1)
      have hb : BitVec.usubOverflow n.toBitVec (1 : UInt64).toBitVec = false := by
        simp only [UInt64.subOverflow] at hsubOK
        simpa using hsubOK
      rw [hb]; rfl
    have hsub_toNat : (n - 1).toNat = k - 1 := by
      rw [UInt64.toNat_sub_of_le']
      · simp [hk]
      · simp; omega
    simp only [show (n ==? 0 : RustM Bool) = pure (n == 0) from rfl, pure_bind]
    rw [if_neg hn_ne_zero]
    rw [hsubn]
    simp only [pure_bind]
    have ih' := ih (k - 1) (Nat.sub_lt hk_pos Nat.one_pos) (n - 1) hsub_toNat
    rw [ih']
    have hk_succ : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
    have hk_succ_eq : (k - 1) * (k - 1 + 1) / 2 = (k - 1) * k / 2 := by rw [hk_succ]
    rw [hk_succ_eq]
    by_cases hsmall : (k - 1) * k / 2 < 2 ^ 64
    · -- (k-1)*k/2 fits: IH returned .ok; bind reduces to a single addition.
      rw [if_pos hsmall]
      have hbind :
          (do let r ← (RustM.ok (UInt64.ofNat ((k - 1) * k / 2)) : RustM u64)
              n +? r) = (n +? UInt64.ofNat ((k - 1) * k / 2) : RustM u64) := rfl
      rw [hbind]
      have hs_toNat : (UInt64.ofNat ((k - 1) * k / 2)).toNat = (k - 1) * k / 2 := by
        show (BitVec.ofNat 64 ((k - 1) * k / 2)).toNat = (k - 1) * k / 2
        rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt hsmall
      have hgauss : k + (k - 1) * k / 2 = k * (k + 1) / 2 :=
        (gauss_step k hk_pos).symm
      show (rust_primitives.ops.arith.Add.add n (UInt64.ofNat ((k - 1) * k / 2)) : RustM u64) = _
      show (if BitVec.uaddOverflow n.toBitVec (UInt64.ofNat ((k - 1) * k / 2)).toBitVec then
              (.fail .integerOverflow : RustM u64)
            else pure (n + UInt64.ofNat ((k - 1) * k / 2))) = _
      have haddOverflow_iff_b :
          BitVec.uaddOverflow n.toBitVec (UInt64.ofNat ((k - 1) * k / 2)).toBitVec =
            decide (n.toNat + (UInt64.ofNat ((k - 1) * k / 2)).toNat ≥ 2 ^ 64) := rfl
      rw [haddOverflow_iff_b, hk, hs_toNat, hgauss]
      by_cases hbig : k * (k + 1) / 2 < 2 ^ 64
      · -- Final addition fits: returns .ok, value matches the closed form at k.
        rw [if_pos hbig]
        simp only [decide_eq_true_iff]
        have hdec : ¬ (k * (k + 1) / 2 ≥ 2 ^ 64) := by omega
        rw [if_neg hdec]
        congr 1
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_add_of_lt (by rw [hk, hs_toNat]; omega)]
        rw [hk, hs_toNat, hgauss]
        show k * (k + 1) / 2 = (BitVec.ofNat 64 (k * (k + 1) / 2)).toNat
        rw [BitVec.toNat_ofNat]
        exact (Nat.mod_eq_of_lt hbig).symm
      · -- Final addition overflows: returns .fail.
        rw [if_neg hbig]
        simp only [decide_eq_true_iff]
        have hdec : k * (k + 1) / 2 ≥ 2 ^ 64 := Nat.not_lt.mp hbig
        rw [if_pos hdec]
    · -- (k-1)*k/2 doesn't fit: IH already returned .fail; propagate.
      rw [if_neg hsmall]
      have hbig_total : ¬ k * (k + 1) / 2 < 2 ^ 64 := by
        intro hlt
        apply hsmall
        have : (k - 1) * k ≤ k * (k + 1) :=
          Nat.mul_le_mul (Nat.sub_le k 1) (Nat.le_succ k)
        exact Nat.lt_of_le_of_lt (Nat.div_le_div_right this) hlt
      rw [if_neg hbig_total]
      rfl

/-- Postcondition (functional correctness).

For every `n : u64` whose Gauss closed-form sum `n*(n+1)/2` still fits
in `u64`, `sum_to_n n` succeeds and returns that closed form. The
hypothesis acts as the function's *implicit* precondition: the Rust
source has no `requires` clause, but the recursion's `n + sum_to_n(n-1)`
would panic on overflow if the partial sum (which is exactly
`n*(n+1)/2`) did not fit. -/
theorem sum_to_n_closed_form (n : u64)
    (h : n.toNat * (n.toNat + 1) / 2 < 2 ^ 64) :
    sum_to_n.sum_to_n n
      = RustM.ok (UInt64.ofNat (n.toNat * (n.toNat + 1) / 2)) := by
  rw [sum_to_n_compute, if_pos h]

/-- Failure condition (integer overflow).

When the Gauss closed-form sum `n*(n+1)/2` exceeds `u64`'s range, the
recursion's `n + sum_to_n(n-1)` step computing that sum overflows and
the function panics with `Error.integerOverflow`. This is the only
way `sum_to_n` can fail: the `n - 1` step is guarded by the explicit
`if n == 0` branch, so subtraction underflow never occurs. -/
theorem sum_to_n_overflow (n : u64)
    (h : 2 ^ 64 ≤ n.toNat * (n.toNat + 1) / 2) :
    sum_to_n.sum_to_n n = RustM.fail .integerOverflow := by
  rw [sum_to_n_compute,
      if_neg (by omega : ¬ n.toNat * (n.toNat + 1) / 2 < 2 ^ 64)]

end Sum_to_nObligations
