-- Companion obligations file for the `factorial` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import factorial

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace FactorialObligations

/-- Mathematical factorial on `Nat`, defined locally because core Lean 4
    does not ship a `Nat.factorial` and we have no Mathlib in this build. -/
private def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- All factorials up to and including `20!` fit in a `u64`.
    A single `decide` enumerates `k ∈ {0, …, 20}` and checks each value
    against `2 ^ 64`; this is the *only* place this proof reduces a closed
    numeric goal by kernel evaluation. Every subsequent step uses this
    bound symbolically. -/
private theorem fact_lt_two_pow_64 : ∀ k, k ≤ 20 → fact k < 2 ^ 64 := by
  decide

/-- Postcondition (base-case anchor):
    `factorial(0)` returns `1`.

    This is an independent absolute claim that anchors the recurrence
    below to the unique mathematical solution `n!`. Without it, an
    implementation that always returned `0` would still satisfy the
    recurrence (since `0 = n * 0`). -/
theorem factorial_zero :
    factorial.factorial 0 = RustM.ok 1 := by
  unfold factorial.factorial
  rfl

/-- Step lemma (helper for `factorial_overflow` and `factorial_value`):
    for any `n` with `1 < n.toNat`, the function unfolds to the "else"
    branch and reduces to the bind `factorial(n - 1) >>= (n *? ·)`. The
    hypothesis `1 < n.toNat` is exactly what makes (a) `n <=? 1`
    evaluate to `pure false` and (b) `n -? 1` not underflow. -/
private theorem factorial_step (n : u64) (h : 1 < n.toNat) :
    factorial.factorial n
      = (factorial.factorial (n - 1)) >>= fun k => n *? k := by
  have h_le : decide (n ≤ (1 : u64)) = false := by
    rw [decide_eq_false_iff_not, UInt64.not_le]
    rw [UInt64.lt_iff_toNat_lt]
    exact h
  -- Express the underflow check in the form that appears literally in
  -- the unfolded `do` block (i.e. `BitVec.usubOverflow ...`).
  have h_no_underflow : n.toBitVec.usubOverflow (UInt64.toBitVec 1) = false := by
    generalize h_eq : n.toBitVec.usubOverflow (UInt64.toBitVec 1) = b
    cases b with
    | false => rfl
    | true =>
      exfalso
      -- `UInt64.subOverflow n 1` unfolds to the LHS of `h_eq` definitionally.
      have h_so : UInt64.subOverflow n 1 = true := h_eq
      rw [UInt64.subOverflow_iff] at h_so
      simp at h_so
      omega
  conv =>
    lhs
    unfold factorial.factorial
  simp only [rust_primitives.cmp.le, h_le, pure_bind,
    rust_primitives.ops.arith.Sub.sub, h_no_underflow, Bool.false_eq_true,
    ↓reduceIte]

/-- Auxiliary functional-correctness lemma, proved by `Nat` induction
    mirroring the structure of the recursion. For every `k ≤ 20` and
    every `u64` value `n` with `n.toNat = k`, `factorial(n)` returns
    `k!` (encoded as a `u64`).

    The base case (`k = 0`) reduces via `factorial_zero`.
    For the successor case we split on whether `k = 0`:
      * `k = 0` (so `n.toNat = 1`): the function takes the `n ≤ 1`
        branch and returns `pure 1` directly, no recursion.
      * `k ≥ 1` (so `1 < n.toNat`): peel one call with `factorial_step`,
        apply the induction hypothesis to `n - 1`, then verify that the
        final multiplication does not overflow using `fact_lt_two_pow_64`. -/
private theorem factorial_value :
    ∀ (k : Nat), k ≤ 20 → ∀ (n : u64),
      n.toNat = k →
      factorial.factorial n = RustM.ok (UInt64.ofNat (fact k)) := by
  intro k
  induction k with
  | zero =>
    intro _ n hn
    -- `n.toNat = 0` forces `n = 0`; reduce via `factorial_zero`.
    have h_n_eq : n = 0 := by
      have : n = UInt64.ofNat n.toNat :=
        (UInt64.ofNat_eq_of_toNat_eq rfl).symm
      rw [this, hn]; rfl
    rw [h_n_eq, factorial_zero]
    rfl
  | succ k ih =>
    intro hk n hn
    by_cases hk0 : k = 0
    · -- `n.toNat = 1`: function takes the `n ≤ 1` branch and returns `pure 1`.
      subst hk0
      have h_n_eq : n = 1 := by
        have : n = UInt64.ofNat n.toNat :=
          (UInt64.ofNat_eq_of_toNat_eq rfl).symm
        rw [this, hn]; rfl
      rw [h_n_eq]
      unfold factorial.factorial
      rfl
    · -- `n.toNat = k + 1 ≥ 2`, so `1 < n.toNat`. Peel a call with `factorial_step`.
      have h_lt : 1 < n.toNat := by omega
      rw [factorial_step n h_lt]
      -- `(n - 1).toNat = k`, so the IH applies.
      have h_one_le : (1 : u64).toNat ≤ n.toNat := by simp; omega
      have h_n_minus : (n - 1).toNat = k := by
        rw [UInt64.toNat_sub_of_le' h_one_le]; simp; omega
      have hk' : k ≤ 20 := by omega
      rw [ih hk' (n - 1) h_n_minus]
      -- Goal: `n *? UInt64.ofNat (fact k) = RustM.ok (UInt64.ofNat (fact (k+1)))`.
      -- Show the multiplication does not overflow using `fact_lt_two_pow_64`.
      have h_fact_succ_lt : fact (k + 1) < 2 ^ 64 :=
        fact_lt_two_pow_64 (k + 1) hk
      have h_k1_lt : k + 1 < 2 ^ 64 := by omega
      have h_fact_k_lt : fact k < 2 ^ 64 :=
        fact_lt_two_pow_64 k hk'
      -- toNat of both factors.
      have h_n_toNat : n.toNat = k + 1 := hn
      have h_m_toNat : (UInt64.ofNat (fact k)).toNat = fact k :=
        UInt64.toNat_ofNat_of_lt' h_fact_k_lt
      -- Product is `fact (k+1) = (k+1) * fact k`, which fits in u64.
      have h_prod_lt : n.toNat * (UInt64.ofNat (fact k)).toNat < 2 ^ 64 := by
        rw [h_n_toNat, h_m_toNat]
        show (k + 1) * fact k < 2 ^ 64
        change fact (k + 1) < 2 ^ 64
        exact h_fact_succ_lt
      -- No-overflow flag is false.
      have h_no_overflow :
          BitVec.umulOverflow n.toBitVec (UInt64.ofNat (fact k)).toBitVec = false := by
        have : ¬ UInt64.mulOverflow n (UInt64.ofNat (fact k)) := by
          rw [UInt64.mulOverflow_iff]; omega
        simpa [UInt64.mulOverflow] using this
      -- Unfold `*?` on `UInt64`.
      show (rust_primitives.ops.arith.Mul.mul n (UInt64.ofNat (fact k)) : RustM u64)
            = RustM.ok (UInt64.ofNat (fact (k + 1)))
      simp only [rust_primitives.ops.arith.Mul.mul, h_no_overflow,
        Bool.false_eq_true, ↓reduceIte]
      -- Now goal: `pure (n * UInt64.ofNat (fact k)) = RustM.ok (UInt64.ofNat (fact (k+1)))`.
      apply congrArg RustM.ok
      -- Reduce to a `toNat` equality and use that both sides have the same `toNat`.
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_mul, h_n_toNat, h_m_toNat,
        UInt64.toNat_ofNat_of_lt' h_fact_succ_lt]
      -- `(k+1) * fact k % 2^64 = fact (k+1)`.
      show (k + 1) * fact k % 2 ^ 64 = fact (k + 1)
      have h_unfold : fact (k + 1) = (k + 1) * fact k := rfl
      rw [← h_unfold]
      exact Nat.mod_eq_of_lt h_fact_succ_lt

/-- Postcondition (structural / recurrence):
    For every `n` with `1 ≤ n ≤ 20` (the non-overflowing range),
    `factorial(n) = n * factorial(n - 1)` — the recursive value of
    `factorial` agrees with the result of multiplying `n` by the
    factorial of `n - 1`, and in particular both successfully return
    a value (no overflow / no panic).

    Combined with the base case above, this pins down the exact
    mathematical value of `factorial` on its entire valid domain by
    induction. The upper bound `20` is the largest input for which
    `n!` fits in `u64`; including it exercises the boundary value.

    Proof: apply the auxiliary `factorial_value` (proved by induction)
    at both `n` and `n - 1`, then close the resulting `u64` numeric
    identity `n * UInt64.ofNat ((n.toNat - 1)!) = UInt64.ofNat n.toNat!`
    using the same no-overflow argument as inside the induction. -/
theorem factorial_recurrence (n : u64)
    (hlo : 1 ≤ n.toNat) (hhi : n.toNat ≤ 20) :
    factorial.factorial n
      = (factorial.factorial (n - 1)) >>= fun k => RustM.ok (n * k) := by
  -- Functional correctness on `n` (LHS).
  rw [factorial_value n.toNat hhi n rfl]
  -- Functional correctness on `n - 1` (RHS bound argument).
  have h_one_le : (1 : u64).toNat ≤ n.toNat := by simp; omega
  have h_n_minus : (n - 1).toNat = n.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le' h_one_le]; simp
  have h_pred_le : n.toNat - 1 ≤ 20 := by omega
  rw [factorial_value (n.toNat - 1) h_pred_le (n - 1) h_n_minus]
  -- Goal:  `RustM.ok (UInt64.ofNat (fact n.toNat))`
  --      = `RustM.ok (UInt64.ofNat (fact (n.toNat - 1))) >>= fun k => RustM.ok (n * k)`
  -- Reduce the bind, then prove the resulting `u64` equality by `toNat`.
  show RustM.ok (UInt64.ofNat (fact n.toNat))
        = RustM.ok (n * UInt64.ofNat (fact (n.toNat - 1)))
  apply congrArg RustM.ok
  -- Set up bounds.
  have h_fact_n_lt : fact n.toNat < 2 ^ 64 := fact_lt_two_pow_64 n.toNat hhi
  have h_fact_pred_lt : fact (n.toNat - 1) < 2 ^ 64 :=
    fact_lt_two_pow_64 (n.toNat - 1) h_pred_le
  -- Compute `toNat` of both sides.
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_mul, UInt64.toNat_ofNat_of_lt' h_fact_pred_lt,
    UInt64.toNat_ofNat_of_lt' h_fact_n_lt]
  -- Goal:  `fact n.toNat = n.toNat * fact (n.toNat - 1) % 2 ^ 64`
  -- Use the recurrence `fact (m + 1) = (m + 1) * fact m` (definitional).
  obtain ⟨m, hm⟩ : ∃ m, n.toNat = m + 1 := ⟨n.toNat - 1, by omega⟩
  rw [hm]
  show (m + 1) * fact m = (m + 1) * fact (m + 1 - 1) % 2 ^ 64
  have h_succ : (m + 1) - 1 = m := by omega
  rw [h_succ, Nat.mod_eq_of_lt]
  show (m + 1) * fact m < 2 ^ 64
  change fact (m + 1) < 2 ^ 64
  rw [← hm]
  exact h_fact_n_lt

/-- Failure condition:
    Inputs `n ≥ 21` violate the precondition (because `21!` exceeds
    `u64::MAX`). The recursive multiplication `n * factorial(n - 1)`
    therefore overflows, and the `RustM`-encoded function returns
    `.fail .integerOverflow`. This pins down the boundary of the
    precondition `n ≤ 20`. -/
theorem factorial_overflow (n : u64) (h : 21 ≤ n.toNat) :
    factorial.factorial n = RustM.fail .integerOverflow := by
  -- Generalise to a Nat induction starting at n.toNat = 21.
  suffices aux : ∀ (k : Nat) (n : u64),
      n.toNat = 21 + k → factorial.factorial n = RustM.fail .integerOverflow by
    exact aux (n.toNat - 21) n (by omega)
  intro k
  induction k with
  | zero =>
    intro n hn
    have h_n_eq : n = UInt64.ofNat n.toNat :=
      (UInt64.ofNat_eq_of_toNat_eq rfl).symm
    rw [h_n_eq, hn]
    native_decide
  | succ k ih =>
    intro n hn
    -- n.toNat ≥ 22, so 1 < n.toNat. Reduce via the step lemma.
    have h_lt : 1 < n.toNat := by omega
    rw [factorial_step n h_lt]
    -- (n - 1).toNat = n.toNat - 1 = 21 + k, so IH applies.
    have h_one_le : (1 : u64).toNat ≤ n.toNat := by
      simp; omega
    have h_n_minus : (n - 1).toNat = 21 + k := by
      rw [UInt64.toNat_sub_of_le' h_one_le]
      simp; omega
    rw [ih (n - 1) h_n_minus]
    rfl

end FactorialObligations
