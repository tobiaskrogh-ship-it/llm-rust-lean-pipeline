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

/-- Mathematical binomial coefficient on `Nat`, defined by Pascal's
    recurrence.  Used in `binomial_postcondition` as the reference oracle.
    (We define it locally because the core Lean library doesn't ship
    `Nat.choose`; the Mathlib name is unavailable in this build.) -/
private def natChoose : Nat → Nat → Nat
  | _,     0     => 1
  | 0,     _+1   => 0
  | n+1,   k+1   => natChoose n k + natChoose n (k+1)

/-! ## Contract clauses for `binomial_u64.binomial`

Each theorem captures one independent clause of the function's contract,
matching a property-style test in the Rust source.  Proofs are `sorry`
placeholders; they are filled in by the proof stage.

The overflow-free range for `u64` binomial coefficients is `n ≤ 67`
(matching the table in the doc-comment of the original
`num_integer::binomial` and the bound used by the `pascal_oracle_up_to_n67`
test).  The Pascal-recurrence test stays at `n ≤ 50`. -/

/-- Helper: `n -? k = pure (n - k)` whenever `k.toNat ≤ n.toNat`. -/
private theorem sub_pure {n k : u64} (h : k.toNat ≤ n.toNat) :
    (n -? k : RustM u64) = pure (n - k) := by
  have h_no_underflow : UInt64.subOverflow n k = false := by
    generalize hbo : UInt64.subOverflow n k = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      rw [UInt64.subOverflow_iff] at hbo
      omega
  show (rust_primitives.ops.arith.Sub.sub n k : RustM u64) = pure (n - k)
  show (if BitVec.usubOverflow n.toBitVec k.toBitVec then
          (.fail .integerOverflow : RustM u64)
        else pure (n - k)) = pure (n - k)
  rw [show BitVec.usubOverflow n.toBitVec k.toBitVec = false from h_no_underflow]
  rfl

/-- `k > n` case: when the second argument exceeds the first, the function
    returns 0 without panicking.  Captures the explicit early-return clause
    `if k > n { return 0; }` in the source and the property test
    `k_greater_than_n_is_zero`. -/
theorem binomial_k_gt_n (n k : u64) (hkn : n.toNat < k.toNat) :
    binomial_u64.binomial n k = RustM.ok 0 := by
  unfold binomial_u64.binomial
  have hgt : decide (k > n) = true :=
    decide_eq_true (UInt64.lt_iff_toNat_lt.mpr hkn)
  simp only [show (k >? n) = (pure (decide (k > n)) : RustM Bool) from rfl,
             hgt, pure_bind, if_true]
  rfl

/-- Boundary case `k = 0`: `C(n, 0) = 1` for every `n`.

    The proof reduces both `k > n` and `k > n - k` guards to false, then
    handles the `while d <= k` loop via `Spec.MonoLoopCombinator.while_loop`
    with the vacuous invariant `s._0 = 1 ∧ s._2 = 1`: since the loop guard
    requires `d.toNat ≤ 0 = k.toNat` but the invariant pins `d.toNat = 1`,
    the body step is vacuously satisfied (`cond b = true ∧ inv b` is
    contradictory).  Stage 2 then converts the resulting Hoare triple to
    the equational form via `RustM.Triple_iff_BitVec`. -/
theorem binomial_k_zero (n : u64) :
    binomial_u64.binomial n 0 = RustM.ok 1 := by
  -- Stage 1: Hoare triple stating the return value is 1.
  have h_triple :
      ⦃⌜ True ⌝⦄ binomial_u64.binomial n 0 ⦃⇓ r => ⌜ r = 1 ⌝⦄ := by
    unfold binomial_u64.binomial
    -- (0 >? n) = pure false; (n -? 0) = pure n.
    have h_gt_false : decide ((0 : u64) > n) = false := by
      apply decide_eq_false
      intro h
      have := UInt64.lt_iff_toNat_lt.mp h
      simp at this
    have h_sub_zero : (n -? (0 : u64) : RustM u64) = pure n := by
      have h := sub_pure (n := n) (k := 0) (by simp)
      rw [h]
      congr 1
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le' (by simp : (0:u64).toNat ≤ n.toNat)]
      simp
    -- Reduce the early-return guards.
    simp only [show ((0 : u64) >? n) = (pure (decide ((0 : u64) > n)) : RustM Bool) from rfl,
               h_gt_false, h_sub_zero, pure_bind,
               Bool.false_eq_true, ↓reduceIte]
    -- The remaining goal is a triple about the do-block:
    --   do { let ⟨d, n', r'⟩ ← while_loop ... ⟨1, n, 1⟩; pure r' }
    -- Unfold the while_loop into Loop.MonoLoopCombinator.while_loop.
    unfold rust_primitives.hax.while_loop
    -- Apply the spec for the loop with vacuous invariant.
    apply Triple.bind
    · -- Loop spec
      apply Std.Do.Spec.MonoLoopCombinator.while_loop
        (rust_primitives.hax.Tuple3.mk (1 : u64) n (1 : u64))
        Lean.Loop.mk
        _ _
        (fun s : rust_primitives.hax.Tuple3 u64 u64 u64 =>
            s._0.toNat = 1 ∧ s._2.toNat = 1)
        (fun _ => 0)
      intro b hcond hinv
      -- cond b = true means b._0.toNat ≤ 0; inv says b._0.toNat = 1 → contradiction.
      exfalso
      -- Unfold the cond's hax_construct_pure form to extract its meaning.
      -- The cond, derived by hax_construct_pure from (d <=? k) with k = 0, is
      -- fun s => decide (s._0.toNat ≤ 0).
      obtain ⟨h_d_eq, _⟩ := hinv
      -- We need `cond b = true` to imply `b._0.toNat ≤ 0`.
      -- The derived pureCond for `(d <=? 0)` is `decide (s._0.toNat ≤ 0)`.
      have h_cond : decide (b._0.toNat ≤ 0) = true := hcond
      have h_le : b._0.toNat ≤ 0 := of_decide_eq_true h_cond
      omega
    · intro s
      cases s with
      | mk d n' r' =>
        refine Triple.pure r' ?_
        intro ⟨hinv, _⟩
        -- inv gives r'.toNat = 1, so r' = 1.
        obtain ⟨_, h_r_eq⟩ := hinv
        apply UInt64.toNat_inj.mp
        rw [h_r_eq]
        rfl
  -- Stage 2: convert the triple to an equation.
  rw [RustM.Triple_iff_BitVec] at h_triple
  simp only [decide_true, Bool.not_true, Bool.false_or,
             Bool.and_eq_true, decide_eq_true_eq] at h_triple
  obtain ⟨hok, hval⟩ := h_triple
  cases hf : binomial_u64.binomial n 0 with
  | none => rw [hf] at hok; simp [RustM.toBVRustM] at hok
  | some result =>
    cases result with
    | ok v => rw [hf] at hval; simp [RustM.toBVRustM] at hval; exact congrArg RustM.ok hval
    | error e => rw [hf] at hok; cases e <;> simp [RustM.toBVRustM] at hok

/-- Symmetry: `C(n, k) = C(n, n - k)` for `k ≤ n`.  The implementation
    exploits this via the recursive call `binomial(n, n - k)` when
    `k > n - k`; the property test `symmetry` documents it as an
    independent contract clause.  Both sides denote `RustM u64`; the
    subtraction `n - k` is `u64` subtraction and is well-defined under
    `k ≤ n`. -/
theorem binomial_symmetry (n k : u64) (hkn : k.toNat ≤ n.toNat) :
    binomial_u64.binomial n k = binomial_u64.binomial n (n - k) := by
  have h_sub_nat : (n - k).toNat = n.toNat - k.toNat := UInt64.toNat_sub_of_le' hkn
  have h_nk_le_n : (n - k).toNat ≤ n.toNat := by rw [h_sub_nat]; omega
  -- Split on whether k = n - k, k < n - k, or k > n - k.
  rcases Nat.lt_trichotomy k.toNat (n - k).toNat with h_lt | h_eq | h_gt
  · -- Case k < n - k: LHS takes the loop branch; RHS recurses back to k.
    -- Show the RHS recurses to `binomial n k`.
    have h_unfold_rhs :
        binomial_u64.binomial n (n - k) = binomial_u64.binomial n k := by
      conv =>
        lhs
        unfold binomial_u64.binomial
      have h_gt_n_false : decide ((n - k) > n) = false := by
        apply decide_eq_false
        intro h
        exact absurd (UInt64.lt_iff_toNat_lt.mp h) (Nat.not_lt.mpr h_nk_le_n)
      have h_sub_eq : (n -? (n - k) : RustM u64) = pure (n - (n - k)) :=
        sub_pure h_nk_le_n
      have h_nk_eq_k : n - (n - k) = k := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_sub_of_le' h_nk_le_n, h_sub_nat]
        omega
      have h_gt_k : decide ((n - k) > k) = true := by
        apply decide_eq_true
        apply UInt64.lt_iff_toNat_lt.mpr
        rw [h_sub_nat]; omega
      simp only [show ((n - k) >? n) = (pure (decide ((n - k) > n)) : RustM Bool) from rfl,
                 show ((n - k) >? k) = (pure (decide ((n - k) > k)) : RustM Bool) from rfl,
                 h_gt_n_false, h_gt_k, h_sub_eq, h_nk_eq_k, pure_bind,
                 Bool.false_eq_true, ↓reduceIte]
    rw [h_unfold_rhs]
  · -- Case k = n - k: the two sides are literally equal arguments.
    have h_eq_u64 : k = n - k := by
      apply UInt64.toNat_inj.mp; rw [h_sub_nat] at h_eq; omega
    rw [← h_eq_u64]
  · -- Case k > n - k: LHS recurses to RHS directly.
    conv =>
      lhs
      unfold binomial_u64.binomial
    have h_kn_false : decide (k > n) = false := by
      apply decide_eq_false; intro h
      exact absurd (UInt64.lt_iff_toNat_lt.mp h) (Nat.not_lt.mpr hkn)
    have h_sub_eq' : (n -? k : RustM u64) = pure (n - k) := sub_pure hkn
    have h_gt' : decide (k > (n - k)) = true := by
      apply decide_eq_true
      apply UInt64.lt_iff_toNat_lt.mpr
      omega
    simp only [show (k >? n) = (pure (decide (k > n)) : RustM Bool) from rfl,
               show (k >? (n - k)) = (pure (decide (k > (n - k))) : RustM Bool) from rfl,
               h_kn_false, h_gt', h_sub_eq', pure_bind,
               Bool.false_eq_true, ↓reduceIte]

/-- Pascal's recurrence: for `1 ≤ k ≤ n` (and within the overflow-free range
    `n ≤ 50` used by the property test `pascal_recurrence`),
    `C(n, k) = C(n - 1, k - 1) + C(n - 1, k)` at the `u64` level.
    The existential bundles the three successful results so the equality
    can be stated on plain `u64` values; for `n ≤ 50` every term fits in
    `u64` (`C(50, 25) ≈ 1.26 × 10^14 ≪ 2^64`) so the `u64` addition does
    not overflow. -/
theorem binomial_pascal_recurrence (n k : u64)
    (hk_pos : 0 < k.toNat) (hkn : k.toNat ≤ n.toNat) (hn : n.toNat ≤ 50) :
    ∃ v vsub1 vsub2 : u64,
      binomial_u64.binomial n k = RustM.ok v ∧
      binomial_u64.binomial (n - 1) (k - 1) = RustM.ok vsub1 ∧
      binomial_u64.binomial (n - 1) k = RustM.ok vsub2 ∧
      v = vsub1 + vsub2 := by
  sorry

/-- Main postcondition: in the overflow-free range `n ≤ 67`, the function
    computes the standard binomial coefficient `Nat.choose`.  Captures the
    sweep tests `pascal_oracle_up_to_n67` and `agrees_with_source`, and
    subsumes the specific instances in `test_binomial_u64`. -/
theorem binomial_postcondition (n k : u64) (hn : n.toNat ≤ 67) :
    binomial_u64.binomial n k
      = RustM.ok (UInt64.ofNat (natChoose n.toNat k.toNat)) := by
  sorry

/-- Totality / no-panic: in the overflow-free range `n ≤ 67`, the function
    returns successfully for every `k`.  Together with the property tests
    (which all stay in the overflow-free range), this is the explicit
    "no failure mode" clause of the contract. -/
theorem binomial_total (n k : u64) (hn : n.toNat ≤ 67) :
    ∃ v : u64, binomial_u64.binomial n k = RustM.ok v :=
  ⟨_, binomial_postcondition n k hn⟩

end Binomial_u64Obligations
