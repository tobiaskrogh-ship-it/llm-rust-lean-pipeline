-- Companion obligations file for the `count_to` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import count_to

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Count_toObligations

theorem count_to_identity (n : u64) :
    count_to.count_to n = RustM.ok n := by
  induction h : n.toNat using Nat.strongRecOn generalizing n with
  | _ k ih =>
    unfold count_to.count_to
    by_cases hn : n = 0
    · subst hn; rfl
    · have hpos : 0 < n.toNat := by
        rcases Nat.eq_zero_or_pos n.toNat with h0 | h0
        · exact absurd (UInt64.toNat_inj.mp h0) hn
        · exact h0
      have hn_lt : n.toNat < 2 ^ 64 := n.toFin.isLt
      have hone : (1 : u64).toNat = 1 := rfl
      have hsub_toNat : (n - 1).toNat = n.toNat - 1 :=
        UInt64.toNat_sub_of_le' (by show (1 : u64).toNat ≤ n.toNat; omega)
      have hsub_lt : (n - 1).toNat < k := by rw [hsub_toNat, h]; omega
      have h_nounder : UInt64.subOverflow n 1 = false := by
        generalize h_eq : UInt64.subOverflow n 1 = bo; cases bo
        · rfl
        · exfalso; rw [UInt64.subOverflow_iff, hone] at h_eq; omega
      have h_noover : UInt64.addOverflow (n - 1) 1 = false := by
        generalize h_eq : UInt64.addOverflow (n - 1) 1 = bo; cases bo
        · rfl
        · exfalso; rw [UInt64.addOverflow_iff, hsub_toNat, hone] at h_eq; omega
      have h_add_eq : (n - 1) + (1 : u64) = n := UInt64.toNat_inj.mp (by
        rw [UInt64.toNat_add_of_lt (by rw [hsub_toNat, hone]; omega), hsub_toNat, hone]; omega)
      simp only [show (n ==? (0 : u64)) = (pure (decide (n = 0)) : RustM Bool) from rfl,
                 decide_eq_false hn, pure_bind, Bool.false_eq_true, ↓reduceIte]
      show (if BitVec.usubOverflow n.toBitVec (1 : u64).toBitVec
            then (.fail .integerOverflow : RustM u64) else pure (n - 1)) >>= _ = _
      rw [show BitVec.usubOverflow n.toBitVec (1 : u64).toBitVec = false from h_nounder]
      simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
      rw [ih (n - 1).toNat hsub_lt (n - 1) rfl]
      show (if BitVec.uaddOverflow (n - 1).toBitVec (1 : u64).toBitVec
            then (.fail .integerOverflow : RustM u64) else pure ((n - 1) + 1)) = _
      rw [show BitVec.uaddOverflow (n - 1).toBitVec (1 : u64).toBitVec = false from h_noover]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [h_add_eq]
      rfl

end Count_toObligations
