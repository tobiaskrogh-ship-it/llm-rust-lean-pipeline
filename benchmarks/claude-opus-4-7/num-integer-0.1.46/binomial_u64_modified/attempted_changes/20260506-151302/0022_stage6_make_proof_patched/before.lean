-- Companion obligations file for the `binomial_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import binomial_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Binomial_u64Obligations

/-- Mathematical binomial coefficient on `Nat`, defined locally because
    we have no Mathlib in this build. Standard recurrence:
    `C(n, 0) = 1`, `C(0, k+1) = 0`, `C(n+1, k+1) = C(n, k) + C(n, k+1)`. -/
private def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- Postcondition (boundary, `k > n`):
    when `k` strictly exceeds `n`, the function returns `0` successfully
    (the `if k > n { return 0 }` branch). This pins down the conventional
    `C(n, k) = 0` for `k > n` and matches the `k_greater_than_n_is_zero`
    Rust test. -/
theorem binomial_k_gt_n_zero (n k : u64) (h : n < k) :
    binomial_u64.binomial n k = RustM.ok 0 := by
  unfold binomial_u64.binomial
  have h_gt : k > n := h
  have h_decide : decide (k > n) = true := decide_eq_true_iff.mpr h_gt
  simp only [rust_primitives.cmp.gt, h_decide, pure_bind, ↓reduceIte]
  rfl

/-- Postcondition (boundary, `k = 0`):
    `binomial(n, 0) = 1` for every `n`. The function takes the `k ≤ n`
    branch (since `0 ≤ n` always), then `k ≤ n - k` (since `0 ≤ n`), then
    enters the loop with `iters_left = 0` and exits immediately, returning
    the initial `r = 1`. Matches the first half of the
    `boundary_k_zero_and_k_eq_n` test and the `(0, 0, 1)` case of
    `test_binomial_u64`. -/
theorem binomial_k_zero (n : u64) :
    binomial_u64.binomial n 0 = RustM.ok 1 := by
  unfold binomial_u64.binomial
  -- Step 1: outer (0 >? n) is false
  have h_not_gt : decide ((0 : u64) > n) = false := by
    apply decide_eq_false; intro h
    exact absurd (UInt64.lt_iff_toNat_lt.mp h) (by simp)
  simp only [rust_primitives.cmp.gt, h_not_gt, pure_bind,
             Bool.false_eq_true, ↓reduceIte]
  -- Step 2: n -? 0 = pure n
  have h_no_uflow : BitVec.usubOverflow n.toBitVec ((0 : u64).toBitVec) = false := by
    show UInt64.subOverflow n 0 = false
    have : ¬ (UInt64.subOverflow n 0 = true) := by
      rw [UInt64.subOverflow_iff]; simp
    exact eq_false_of_ne_true this
  have h_sub : (n -? (0 : u64) : RustM u64) = pure n := by
    show (rust_primitives.ops.arith.Sub.sub n 0 : RustM u64) = pure n
    show (if BitVec.usubOverflow n.toBitVec ((0 : u64).toBitVec) then
            (.fail .integerOverflow : RustM u64)
          else pure (n - 0)) = pure n
    rw [h_no_uflow]; simp
  rw [h_sub]
  simp only [pure_bind, h_not_gt, Bool.false_eq_true, ↓reduceIte]
  -- Step 5: reduce the while_loop with iters_left = 0
  -- Init state has iters_left = 0, so cond := decide (iters_left > 0) = false
  -- on first iteration. The combinator therefore returns pure init, and
  -- the surrounding `let __discr ← _ ; pure __discr._3` reduces to pure 1.
  unfold rust_primitives.hax.while_loop
  unfold Lean.Loop.MonoLoopCombinator.while_loop
  unfold Lean.Loop.MonoLoopCombinator.forIn
  unfold Lean.Loop.MonoLoopCombinator.forIn.loop
  unfold Lean.Loop.loopCombinator
  rfl

/-- Postcondition (boundary, `k = n`):
    `binomial(n, n) = 1` for every `n`. For `n > 0`, the function takes
    the `k > n - k` branch (`n > 0 = n - n`) and recurses to
    `binomial(n, 0) = 1`. For `n = 0`, both predicates are false and the
    loop is skipped, returning `1`. Matches the second half of the
    `boundary_k_zero_and_k_eq_n` test. -/
theorem binomial_k_eq_n (n : u64) :
    binomial_u64.binomial n n = RustM.ok 1 := by
  -- Case-split on n = 0 vs n > 0
  by_cases hn : n = 0
  · -- n = 0: binomial 0 0 reduces to binomial_k_zero applied at 0.
    subst hn
    exact binomial_k_zero 0
  · -- n > 0: take the symmetry branch (k = n > n - n = 0), recurse to binomial n 0.
    have hn_pos : 0 < n.toNat := by
      have : n.toNat ≠ 0 := fun h => hn (UInt64.toNat_inj.mp (by simpa using h))
      omega
    unfold binomial_u64.binomial
    -- Step 1: outer (n >? n) is false
    have h_not_self : decide (n > n) = false := by
      apply decide_eq_false; intro h
      exact absurd (UInt64.lt_iff_toNat_lt.mp h) (by omega)
    simp only [rust_primitives.cmp.gt, h_not_self, pure_bind,
               Bool.false_eq_true, ↓reduceIte]
    -- Step 2: n -? n = pure 0
    have h_no_uflow : BitVec.usubOverflow n.toBitVec n.toBitVec = false := by
      show UInt64.subOverflow n n = false
      have : ¬ (UInt64.subOverflow n n = true) := by
        rw [UInt64.subOverflow_iff]; omega
      exact eq_false_of_ne_true this
    have h_sub : (n -? n : RustM u64) = pure 0 := by
      show (rust_primitives.ops.arith.Sub.sub n n : RustM u64) = pure 0
      show (if BitVec.usubOverflow n.toBitVec n.toBitVec then
              (.fail .integerOverflow : RustM u64)
            else pure (n - n)) = pure 0
      rw [h_no_uflow]; simp
    rw [h_sub]
    -- Step 3: (n >? 0) = pure true (since n > 0)
    have h_n_gt_zero : decide (n > (0 : u64)) = true := by
      apply decide_eq_true_iff.mpr
      have : (0 : u64) < n :=
        UInt64.lt_iff_toNat_lt.mpr (by simpa using hn_pos)
      exact this
    simp only [pure_bind, h_n_gt_zero, ↓reduceIte]
    -- After rw [h_sub] earlier replaced both `n -? n` occurrences and
    -- pure_bind collapsed the binds, the goal is `binomial n 0 = ok 1`.
    exact binomial_k_zero n

/-- Helper: when the function takes its symmetric "recurse on n - k" branch
    (i.e. `k ≤ n` and `k > n - k`), it reduces to `binomial n (n - k)`
    in one step. This is the fundamental reduction that powers
    `binomial_symmetry`. -/
private theorem binomial_recurse_branch (n k : u64)
    (h_le : k ≤ n) (h_gt : (n - k) < k) :
    binomial_u64.binomial n k = binomial_u64.binomial n (n - k) := by
  -- Unfold only the LHS so we don't also unfold the recursive call on the RHS
  conv_lhs => unfold binomial_u64.binomial
  -- (k >? n) = false (since k ≤ n)
  have h_not_kn : decide (k > n) = false := by
    apply decide_eq_false; intro h_lt
    have h1 : n.toNat < k.toNat := UInt64.lt_iff_toNat_lt.mp h_lt
    have h2 : k.toNat ≤ n.toNat := UInt64.le_iff_toNat_le.mp h_le
    omega
  simp only [rust_primitives.cmp.gt, h_not_kn, pure_bind,
             Bool.false_eq_true, ↓reduceIte]
  -- (n -? k) = pure (n - k)
  have h_no_uflow : BitVec.usubOverflow n.toBitVec k.toBitVec = false := by
    show UInt64.subOverflow n k = false
    have : ¬ (UInt64.subOverflow n k = true) := by
      rw [UInt64.subOverflow_iff]
      exact Nat.not_lt.mpr (UInt64.le_iff_toNat_le.mp h_le)
    exact eq_false_of_ne_true this
  have h_sub : (n -? k : RustM u64) = pure (n - k) := by
    show (rust_primitives.ops.arith.Sub.sub n k : RustM u64) = pure (n - k)
    show (if BitVec.usubOverflow n.toBitVec k.toBitVec then
            (.fail .integerOverflow : RustM u64)
          else pure (n - k)) = pure (n - k)
    rw [h_no_uflow]; simp
  rw [h_sub]
  -- (k >? (n - k)) = true (from h_gt)
  have h_k_gt : decide (k > (n - k)) = true := by
    apply decide_eq_true_iff.mpr; exact h_gt
  simp only [pure_bind, h_k_gt, ↓reduceIte]

/-- Postcondition (symmetry):
    `binomial(n, k) = binomial(n, n - k)` whenever `k ≤ n`. This is the
    defining symmetry of binomial coefficients and is structurally
    encoded into the function: when `k > n - k`, the function explicitly
    recurses with `n - k`, ensuring both sides ultimately enter the loop
    with the smaller of the two arguments. Matches the symmetry assertion
    inside `test_binomial_u64`'s `check!` macro
    (`binomial(x, x - y) == binomial(x, y)` when `y ≤ x`). -/
theorem binomial_symmetry (n k : u64) (h : k ≤ n) :
    binomial_u64.binomial n k = binomial_u64.binomial n (n - k) := by
  -- Useful Nat-level facts
  have h_le_n : k.toNat ≤ n.toNat := UInt64.le_iff_toNat_le.mp h
  have h_nk_toNat : (n - k).toNat = n.toNat - k.toNat :=
    UInt64.toNat_sub_of_le' h_le_n
  -- (n - k) ≤ n always (since k ≤ n)
  have h_nk_le_n : (n - k) ≤ n := by
    rw [UInt64.le_iff_toNat_le, h_nk_toNat]; omega
  -- n - (n - k) = k whenever k ≤ n
  have h_n_sub_nk : n - (n - k) = k := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le' (UInt64.le_iff_toNat_le.mp h_nk_le_n), h_nk_toNat]
    omega
  -- Three cases on k vs n - k (Nat-level)
  rcases Nat.lt_trichotomy k.toNat (n - k).toNat with h_lt | h_eq | h_gt
  · -- Case k < n - k: apply helper backwards (RHS recurses to LHS)
    have h_nk_gt : n - (n - k) < (n - k) := by
      rw [h_n_sub_nk, UInt64.lt_iff_toNat_lt]
      exact h_lt
    rw [binomial_recurse_branch n (n - k) h_nk_le_n h_nk_gt, h_n_sub_nk]
  · -- Case k = n - k: substitute and use rfl
    have h_eq' : k = n - k := by
      apply UInt64.toNat_inj.mp; exact h_eq
    rw [← h_eq']
  · -- Case k > n - k: apply helper directly (LHS recurses to RHS)
    have h_k_gt : (n - k) < k := UInt64.lt_iff_toNat_lt.mpr h_gt
    exact binomial_recurse_branch n k h h_k_gt

/-- Postcondition (Pascal's recurrence):
    `C(n, k) = C(n - 1, k - 1) + C(n - 1, k)` for `1 ≤ k ≤ n` and
    `n ≤ 50`. The bound `n ≤ 50` matches the Rust `pascal_recurrence`
    test exactly and stays comfortably inside the no-overflow range
    (`n ≤ 67` per the docstring), so both recursive calls succeed and the
    final addition does not overflow. The case `k = n` is handled by the
    `k > n` branch on the right-hand `binomial(n - 1, k)` term, which
    returns `0`, exactly as the recurrence requires for the diagonal. -/
theorem binomial_pascal_recurrence (n k : u64)
    (hk_pos : 1 ≤ k.toNat) (hkn : k.toNat ≤ n.toNat) (hn : n.toNat ≤ 50) :
    binomial_u64.binomial n k =
      (do let a ← binomial_u64.binomial (n - 1) (k - 1)
          let b ← binomial_u64.binomial (n - 1) k
          RustM.ok (a + b)) := by
  sorry

/-- Postcondition (functional correctness on the documented safe range):
    for every `n` with `n.toNat ≤ 67` and any `k`, the function returns
    the mathematical binomial coefficient `C(n, k)`, encoded as a `u64`.
    The bound `n ≤ 67` is the documented overflow-free domain (the
    largest `n` for which `C(n, k)` fits in `u64` for every `k`); on this
    domain, neither the cumulative product in `r` nor the
    `multiply_and_divide` intermediate calculation overflows. This single
    equational statement subsumes the `pascal_oracle_up_to_n67` Rust
    test, the `agrees_with_source` cross-check (in its `n ≤ 67` range),
    and every `test_binomial_u64` value with `n ≤ 67` (i.e., `(35, 11)`,
    `(14, 4)`, `(0, 0)`, `(2, 3)`). -/
theorem binomial_closed_form (n k : u64) (h : n.toNat ≤ 67) :
    binomial_u64.binomial n k =
      RustM.ok (UInt64.ofNat (choose n.toNat k.toNat)) := by
  sorry

/-- Postcondition (concrete value beyond the safe range):
    `binomial(100, 2) = 4950`. This is the only `test_binomial_u64`
    test value with `n > 67`; the function happens to succeed because
    `multiply_and_divide` keeps every intermediate u64 product below
    `2^64` even though `n` exceeds the safe-for-all-k bound. Captured
    here as a separate theorem because the `binomial_closed_form`
    statement above does not cover `n > 67`. -/
theorem binomial_100_2 :
    binomial_u64.binomial 100 2 = RustM.ok 4950 := by
  native_decide

end Binomial_u64Obligations
