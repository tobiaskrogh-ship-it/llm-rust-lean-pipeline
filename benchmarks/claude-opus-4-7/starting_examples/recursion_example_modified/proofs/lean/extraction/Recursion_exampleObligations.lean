-- Obligations for `count_down`.
--
-- The Rust source is a tail-recursive function that decrements `n` until it
-- reaches 0, always returning 0. Hax extracts it as a `partial_fixpoint`,
-- which means the proof goes through Lean's `partial_fixpoint` machinery
-- rather than `Spec.MonoLoopCombinator.while_loop` (the while-loop case
-- demonstrated by `while_example`).
--
-- Proof obligation: `count_down n = pure 0` for every `n : u64`. The proof
-- proceeds by strong induction on `n.toNat`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import recursion_example

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Recursion_exampleObligations

/-- Postcondition: `count_down n` always returns 0, regardless of `n`. -/



theorem count_down_returns_zero (n : u64) :
    recursion_example.count_down n = RustM.ok 0 := by
  induction h : n.toNat using Nat.strongRecOn generalizing n with
  | _ k ih =>
    unfold recursion_example.count_down
    by_cases hn : n.toNat = 0
    · -- Base: n.toNat = 0, so n = 0. The if-branch returns pure 0.
      have hn0 : n = 0 := UInt64.toNat_inj.mp (by simp [hn])
      subst hn0
      rfl
    · -- Step: n.toNat ≠ 0. Reduce `n ==? 0` and `n -? 1`, then apply IH.
      have hn_pos : 0 < n.toNat := Nat.pos_of_ne_zero hn
      have hone : (1 : u64).toNat = 1 := rfl
      have hone_le : (1 : u64).toNat ≤ n.toNat := by rw [hone]; omega
      -- `n ==? 0 = pure false`
      have h_neq : (decide (n = 0)) = false :=
        decide_eq_false (fun h => hn (by rw [h]; rfl))
      simp only [show (n ==? (0 : u64)) = (pure (decide (n = 0)) : RustM Bool) from rfl,
                 h_neq, pure_bind]
      -- `n -? 1 = pure (n - 1)`
      have h_no_underflow : UInt64.subOverflow n 1 = false := by
        generalize hbo : UInt64.subOverflow n 1 = bo
        cases bo with
        | false => rfl
        | true =>
          exfalso
          rw [UInt64.subOverflow_iff] at hbo
          rw [hone] at hbo
          omega
      have h_sub : (n -? (1 : u64) : RustM u64) = pure (n - 1) := by
        show (rust_primitives.ops.arith.Sub.sub n 1 : RustM u64) = pure (n - 1)
        show (if BitVec.usubOverflow n.toBitVec (1 : u64).toBitVec then
                (.fail .integerOverflow : RustM u64)
              else pure (n - 1)) = pure (n - 1)
        rw [show BitVec.usubOverflow n.toBitVec (1 : u64).toBitVec = false from h_no_underflow]
        rfl
      rw [h_sub]
      simp only [pure_bind]
      -- Apply IH to `count_down (n - 1)`. We need (n - 1).toNat < n.toNat = k.
      apply ih (n - 1).toNat
      · rw [UInt64.toNat_sub_of_le' hone_le, hone, h]
        omega
      · rfl

end Recursion_exampleObligations
