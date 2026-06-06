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

/-- `natChoose n 0 = 1` regardless of `n`. The function's first pattern
    clause `_, 0 => 1` only fires definitionally when the first argument
    is in WHNF; a `cases n <;> rfl` discharges both cases. -/
private theorem natChoose_zero_right (n : Nat) : natChoose n 0 = 1 := by
  cases n <;> rfl

/-- Out-of-triangle zero clause: `natChoose n k = 0` whenever `n < k`.
    Proof by induction on `n`, mirroring the recursion of `natChoose`. -/
private theorem natChoose_eq_zero_of_lt (n k : Nat) (h : n < k) :
    natChoose n k = 0 := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => omega
    | succ _ => rfl
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k =>
      show natChoose n k + natChoose n (k + 1) = 0
      rw [ih k (by omega), ih (k + 1) (by omega)]

/-- Row-sum bound on `natChoose`: every entry is at most `2 ^ n`.
    Used to derive `natChoose n k < 2 ^ 64` whenever `n ≤ 49`, which keeps
    Pascal's recurrence overflow-free at the `u64` level inside the
    `n ≤ 50` range. -/
private theorem natChoose_le_two_pow (n k : Nat) : natChoose n k ≤ 2 ^ n := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => exact Nat.le_refl _
    | succ _ => exact Nat.zero_le _
  | succ n ih =>
    cases k with
    | zero =>
      show 1 ≤ 2 ^ (n + 1)
      have h_pos : 0 < 2 ^ (n + 1) := Nat.two_pow_pos _
      omega
    | succ k =>
      show natChoose n k + natChoose n (k + 1) ≤ 2 ^ (n + 1)
      have h1 := ih k
      have h2 := ih (k + 1)
      have h_pow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
        have := Nat.pow_succ 2 n
        omega
      omega

/-- Symmetry of `natChoose`: `natChoose n k = natChoose n (n - k)` for
    `k ≤ n`.  Used in the case-split of `binomial_postcondition` to
    relate the recursive (`k > n - k`) branch's result back to the
    canonical form, and to discharge the `k = n` boundary via
    `natChoose n n = natChoose n 0 = 1`.

    Proof: induction on `n`, mirroring the recursion of `natChoose`.
    The boundary `natChoose n n = 1` is itself derived from the IH at
    `k = n` (`natChoose n n = natChoose n 0 = 1`). Interior cells use
    Pascal's recurrence on both sides combined with two IH applications
    (at `k = j` and `k = j + 1`). -/
private theorem natChoose_symmetry (n k : Nat) (h : k ≤ n) :
    natChoose n k = natChoose n (n - k) := by
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := Nat.le_zero.mp h
    subst hk0
    rfl
  | succ n ih =>
    have h_nn : natChoose n n = 1 := by
      rw [ih n (Nat.le_refl n), Nat.sub_self]
      exact natChoose_zero_right n
    cases k with
    | zero =>
      show 1 = natChoose (n + 1) (n + 1 - 0)
      rw [Nat.sub_zero]
      show 1 = natChoose n n + natChoose n (n + 1)
      rw [h_nn, natChoose_eq_zero_of_lt n (n + 1) (Nat.lt_succ_self n)]
    | succ j =>
      have hj : j ≤ n := Nat.le_of_succ_le_succ h
      have h_sub : n + 1 - (j + 1) = n - j := by omega
      rw [h_sub]
      show natChoose n j + natChoose n (j + 1) = natChoose (n + 1) (n - j)
      by_cases hjn : j < n
      · obtain ⟨m, hm⟩ : ∃ m, n - j = m + 1 := ⟨n - j - 1, by omega⟩
        rw [hm]
        show natChoose n j + natChoose n (j + 1) = natChoose n m + natChoose n (m + 1)
        rw [ih j hj, ih (j + 1) hjn, hm]
        have h_m : n - (j + 1) = m := by omega
        rw [h_m]
        omega
      · have h_j_eq : j = n := by omega
        rw [h_j_eq, Nat.sub_self]
        show natChoose n n + natChoose n (n + 1) = 1
        rw [h_nn, natChoose_eq_zero_of_lt n (n + 1) (Nat.lt_succ_self n)]

/-- Tight overflow bound for the documented safe range.  The largest entry
    when `n ≤ 67` is `natChoose 67 33 ≈ 1.42 × 10^19`, strictly below
    `2 ^ 64 ≈ 1.84 × 10^19`.  The available row-sum bound `2 ^ n` is too
    weak (it exceeds `2 ^ 64` for `n ≥ 64`); we use `native_decide` over
    the finite table `n ≤ 67`, `k ≤ n`. -/
private theorem natChoose_lt_two_pow_64 (n k : Nat) (hn : n ≤ 67) :
    natChoose n k < 2 ^ 64 := by
  by_cases hk : k ≤ n
  · have key : ∀ n' ≤ 67, ∀ k' ≤ n', natChoose n' k' < 2 ^ 64 := by
      native_decide
    exact key n hn k hk
  · push_neg at hk
    rw [natChoose_eq_zero_of_lt n k hk]
    decide

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
    with a strengthened invariant `s._0.toNat = 1 ∧ s._2.toNat = 1`.
    Because the loop guard requires `d.toNat ≤ 0` but the invariant pins
    `d.toNat = 1`, the body step is vacuously satisfied (`cond b = true ∧
    inv b` is contradictory).  Stage 2 then converts the resulting Hoare
    triple to the equational form via `RustM.Triple_iff_BitVec`. -/
theorem binomial_k_zero (n : u64) :
    binomial_u64.binomial n 0 = RustM.ok 1 := by
  -- Stage 1: Hoare triple stating the return value is 1.
  have h_triple :
      ⦃⌜ True ⌝⦄ binomial_u64.binomial n 0 ⦃⇓ r => ⌜ r = 1 ⌝⦄ := by
    unfold binomial_u64.binomial
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
    -- Reduce the early-return guards and the n - 0 subtraction.
    simp only [show ((0 : u64) >? n) = (pure (decide ((0 : u64) > n)) : RustM Bool) from rfl,
               h_gt_false, h_sub_zero, pure_bind,
               Bool.false_eq_true, ↓reduceIte]
    -- The remaining goal is a triple about the do-block:
    --   do { let ⟨d, n', r'⟩ ← while_loop ... ⟨1, n, 1⟩; pure r' }
    unfold rust_primitives.hax.while_loop
    -- The loop result is bound, then `pure r` returns the third tuple component.
    -- Step 1: build the loop triple with our strengthened invariant.
    have h_loop :
        ⦃⌜ ((1 : u64).toNat = 1 ∧ (1 : u64).toNat = 1) ⌝⦄
          Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk
            (fun b : rust_primitives.hax.Tuple3 u64 u64 u64 =>
                decide (b._0.toNat ≤ UInt64.toNat (0 : u64)))
            (rust_primitives.hax.Tuple3.mk (1 : u64) n (1 : u64))
            (fun x : rust_primitives.hax.Tuple3 u64 u64 u64 => do
              let r ← binomial_u64.multiply_and_divide x._2 x._1 x._0
              let n ← x._1 -? 1
              let d ← x._0 +? 1
              pure (rust_primitives.hax.Tuple3.mk d n r))
        ⦃⇓ b => ⌜ (b._0.toNat = 1 ∧ b._2.toNat = 1) ∧
                  ¬ decide (b._0.toNat ≤ UInt64.toNat (0 : u64)) = true ⌝⦄ := by
      apply Std.Do.Spec.MonoLoopCombinator.while_loop
        (rust_primitives.hax.Tuple3.mk (1 : u64) n (1 : u64))
        Lean.Loop.mk
        (fun b => decide (b._0.toNat ≤ UInt64.toNat (0 : u64)))
        _
        (fun s : rust_primitives.hax.Tuple3 u64 u64 u64 =>
            s._0.toNat = 1 ∧ s._2.toNat = 1)
        (fun _ => 0)
      intro b hcond hinv
      exfalso
      obtain ⟨h_d_eq, _⟩ := hinv
      have h_cond_le : b._0.toNat ≤ UInt64.toNat (0 : u64) := of_decide_eq_true hcond
      simp at h_cond_le
      omega
    -- Step 2: strengthen post to `b._2 = 1`.
    have h_loop' :
        ⦃⌜ ((1 : u64).toNat = 1 ∧ (1 : u64).toNat = 1) ⌝⦄
          Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk
            (fun b : rust_primitives.hax.Tuple3 u64 u64 u64 =>
                decide (b._0.toNat ≤ UInt64.toNat (0 : u64)))
            (rust_primitives.hax.Tuple3.mk (1 : u64) n (1 : u64))
            (fun x : rust_primitives.hax.Tuple3 u64 u64 u64 => do
              let r ← binomial_u64.multiply_and_divide x._2 x._1 x._0
              let n ← x._1 -? 1
              let d ← x._0 +? 1
              pure (rust_primitives.hax.Tuple3.mk d n r))
        ⦃⇓ b => ⌜ b._2 = (1 : u64) ⌝⦄ := by
      apply Triple.of_entails_right _ _ _ _ h_loop
      apply PostCond.entails.of_left_entails
      intro r ⟨⟨_, h_r2_eq⟩, _⟩
      apply UInt64.toNat_inj.mp
      rw [h_r2_eq]; rfl
    -- Step 3: weaken pre to True.
    have h_loop'' :
        ⦃⌜ True ⌝⦄
          Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk
            (fun b : rust_primitives.hax.Tuple3 u64 u64 u64 =>
                decide (b._0.toNat ≤ UInt64.toNat (0 : u64)))
            (rust_primitives.hax.Tuple3.mk (1 : u64) n (1 : u64))
            (fun x : rust_primitives.hax.Tuple3 u64 u64 u64 => do
              let r ← binomial_u64.multiply_and_divide x._2 x._1 x._0
              let n ← x._1 -? 1
              let d ← x._0 +? 1
              pure (rust_primitives.hax.Tuple3.mk d n r))
        ⦃⇓ b => ⌜ b._2 = (1 : u64) ⌝⦄ := by
      apply Triple.of_entails_left _ _ _ _ h_loop'
      intro _
      exact ⟨rfl, rfl⟩
    -- Step 4: bind the loop with `pure r` to get the function postcondition.
    apply Triple.bind _ _ h_loop''
    intro s
    cases s with
    | mk d n' r' =>
      refine Triple.pure r' ?_
      intro h
      exact h
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

/-- Boundary case `k = n`: `C(n, n) = 1` for every `n`.  Other half of the
    property test `boundary_k_zero_and_k_eq_n`.

    Proved via symmetry: `binomial n n = binomial n (n - n) = binomial n 0 = 1`. -/
theorem binomial_k_eq_n (n : u64) :
    binomial_u64.binomial n n = RustM.ok 1 := by
  have h_sym := binomial_symmetry n n (Nat.le_refl _)
  have h_sub : n - n = (0 : u64) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le' (Nat.le_refl _)]
    simp
  rw [h_sym, h_sub]
  exact binomial_k_zero n

/-- The loop case of `binomial_postcondition`: when `0 < k` and
    `2 * k ≤ n` (so the function takes the non-recursive branch with the
    inner `while d ≤ k` loop), the result is `UInt64.ofNat (natChoose n k)`.

    `binomial_postcondition` reduces every other case to this one — case
    `k > n` is closed by `binomial_k_gt_n`, case `k = 0` by
    `binomial_k_zero`, case `k = n` by `binomial_k_eq_n` +
    `natChoose_symmetry`, and case `n - k < k < n` by `binomial_symmetry`
    applied to swap arguments to `(n, n - k)` (which then satisfies
    `2 * (n - k) ≤ n`) plus `natChoose_symmetry`.

    Stage 1 of the proof (the Hoare triple) is scaffolded below: we
    `unfold binomial_u64.binomial`, reduce the `k > n` and `k > n - k`
    guards to false via `sub_pure` + `decide_eq_false`, and arrive at a
    triple about the underlying `Loop.MonoLoopCombinator.while_loop`.
    Stage 2 (the triple-to-equation conversion via
    `RustM.Triple_iff_BitVec`) is fully written out and reused verbatim
    from `binomial_k_zero`.

    Stuck sub-goal: after the simp reduces the early-return guards, the
    remaining triple is about the loop with initial state `⟨1, n, 1⟩`
    and body `fun ⟨d, n', r⟩ => do
      let r ← multiply_and_divide r n' d
      let n' ← n' -? 1
      let d ← d +? 1
      pure ⟨d, n', r⟩`. Applying `Spec.MonoLoopCombinator.while_loop`
    with the natural invariant
      `loopInv ⟨d, n', r⟩ ≡ 1 ≤ d.toNat ∧ d.toNat ≤ k.toNat + 1
                         ∧ n'.toNat = n.toNat - (d.toNat - 1)
                         ∧ r.toNat = natChoose n.toNat (d.toNat - 1)`
    and termination measure `k.toNat + 1 - d.toNat` reduces the goal to
    a body-step obligation. The body-step obligation requires:
      (a) `multiply_and_divide r n' d = RustM.ok r_new` with
          `r_new.toNat = natChoose n.toNat d.toNat`. This unfolds to a
          Hoare triple for `multiply_and_divide`, which in turn requires
          `gcd_u64 r d = RustM.ok (UInt64.ofNat (Nat.gcd r.toNat d.toNat))`.
      (b) Exact-divisibility: `(d / Nat.gcd r d) ∣ n'` so the
          `a / (b / g)` step inside `multiply_and_divide` produces no
          remainder. This holds because by the invariant
          `r.toNat * d.toNat / Nat.gcd ... = natChoose n.toNat (d.toNat - 1) * (n.toNat - (d.toNat - 1))`
          and the Nat-level identity
          `natChoose n.toNat d.toNat * d.toNat = natChoose n.toNat (d.toNat - 1) * (n.toNat - (d.toNat - 1))`.
      (c) New `r.toNat = natChoose n.toNat d.toNat`, which follows from
          (a) + (b) once `multiply_and_divide` is verified.

    Structural unblock: a separately-verified
      `gcd_u64_postcondition : ∀ x y : u64,
         binomial_u64.gcd_u64 x y =
           RustM.ok (UInt64.ofNat (Nat.gcd x.toNat y.toNat))`
    Stein's binary GCD correctness, proved as its own pipeline target
    (the Rust source already exposes `gcd_u64` and `trailing_zeros_u64`
    as top-level functions, so this is a single additional target). With
    that lemma in hand, the body-step obligation reduces to the Nat-level
    multiplicative-recurrence identity above, which is a routine
    inductive argument from `Nat.div_mul_div_comm`, `Nat.gcd_dvd_left/right`,
    and the unfolded definition of `natChoose` — no Mathlib import
    required. The work splits cleanly into: (i) `gcd_u64` Stein-algorithm
    correctness (own target), (ii) `multiply_and_divide` correctness
    (derived from gcd), (iii) the binomial loop invariant (derived from
    multiply_and_divide). -/
private theorem binomial_loop_case (n k : u64)
    (hn : n.toNat ≤ 67) (h_k_pos : 0 < k.toNat) (h_2k_le_n : 2 * k.toNat ≤ n.toNat) :
    binomial_u64.binomial n k = RustM.ok (UInt64.ofNat (natChoose n.toNat k.toNat)) := by
  have h_kn : k.toNat ≤ n.toNat := by omega
  have h_sub_eq : (n - k).toNat = n.toNat - k.toNat := UInt64.toNat_sub_of_le' h_kn
  have h_k_le_nk : k.toNat ≤ (n - k).toNat := by rw [h_sub_eq]; omega
  -- Stage 1: Hoare triple over `binomial_u64.binomial n k`.
  have h_triple :
      ⦃⌜ True ⌝⦄
        binomial_u64.binomial n k
      ⦃⇓ r => ⌜ r = UInt64.ofNat (natChoose n.toNat k.toNat) ⌝⦄ := by
    unfold binomial_u64.binomial
    have h_kn_gt_false : decide (k > n) = false := by
      apply decide_eq_false
      intro h
      exact absurd (UInt64.lt_iff_toNat_lt.mp h) (Nat.not_lt.mpr h_kn)
    have h_sub_pure : (n -? k : RustM u64) = pure (n - k) := sub_pure h_kn
    have h_k_gt_nk_false : decide (k > (n - k)) = false := by
      apply decide_eq_false
      intro h
      exact absurd (UInt64.lt_iff_toNat_lt.mp h) (Nat.not_lt.mpr h_k_le_nk)
    simp only [show (k >? n) = (pure (decide (k > n)) : RustM Bool) from rfl,
               show (k >? (n - k)) = (pure (decide (k > (n - k))) : RustM Bool) from rfl,
               h_kn_gt_false, h_sub_pure, h_k_gt_nk_false, pure_bind,
               Bool.false_eq_true, ↓reduceIte]
    -- After these reductions, the goal is a Hoare triple about
    -- `do let ⟨d, n', r'⟩ ← Loop.MonoLoopCombinator.while_loop … ⟨1, n, 1⟩ …; pure r'`.
    -- A first attempt at pushing further unfolded
    -- `rust_primitives.hax.while_loop` and tried to extract `r` from the
    -- final Tuple3 by binding through `pure r`. That attempt surfaced a
    -- second concrete blocker beyond the body-step itself: the overflow
    -- bound. The available `natChoose_le_two_pow` gives only
    -- `natChoose n k ≤ 2^n`, which for `n ≤ 67` exceeds `2^64` (since
    -- `2^67 > 2^64`). The actual fact we need —
    --   `∀ k, n.toNat ≤ 67 → natChoose n.toNat k < 2^64`
    -- — is true (since `natChoose 67 33 ≈ 1.42 * 10^19 < 2^64 ≈ 1.84 * 10^19`),
    -- but requires a different argument than the symmetric row-sum bound.
    -- That argument is itself part of the structural unblock listed in the
    -- docstring: a tight `natChoose_lt_two_pow_64` lemma (provable by
    -- `decide` on the finite table for `n ≤ 67`, or by Pascal-recurrence
    -- induction with the explicit `1.42 * 10^19 < 2^64` bound) plus the
    -- gcd / multiply_and_divide correctness chain together discharge the
    -- loop. See docstring for the full unblock path.
    sorry
  -- Stage 2: convert the triple to an equation. Same template as
  -- `binomial_k_zero` / `gcd_while_postcondition`.
  rw [RustM.Triple_iff_BitVec] at h_triple
  simp only [decide_true, Bool.not_true, Bool.false_or,
             Bool.and_eq_true, decide_eq_true_eq] at h_triple
  obtain ⟨hok, hval⟩ := h_triple
  cases hf : binomial_u64.binomial n k with
  | none => rw [hf] at hok; simp [RustM.toBVRustM] at hok
  | some result =>
    cases result with
    | ok v =>
      rw [hf] at hval; simp [RustM.toBVRustM] at hval
      exact congrArg RustM.ok hval
    | error e =>
      rw [hf] at hok; cases e <;> simp [RustM.toBVRustM] at hok

/-- Main postcondition: in the overflow-free range `n ≤ 67`, the function
    computes the standard binomial coefficient `natChoose`.  Captures the
    sweep tests `pascal_oracle_up_to_n67` and `agrees_with_source`, and
    subsumes the specific instances in `test_binomial_u64`.

    The proof case-splits on the outer guards of `binomial_u64.binomial`:
    * `k > n` → closed by `binomial_k_gt_n` + `natChoose_eq_zero_of_lt`.
    * `k = 0` → closed by `binomial_k_zero` + `natChoose_zero_right`.
    * `k = n` (with `n > 0`) → closed by `binomial_k_eq_n` +
      `natChoose_symmetry` (collapsing `natChoose n n` to
      `natChoose n 0 = 1`).
    * `n - k < k < n` (the symmetric loop branch) → use
      `binomial_symmetry` to swap arguments to `(n, n - k)` which then
      satisfies `2 * (n - k) ≤ n`, apply `binomial_loop_case` to the
      swapped arguments, then rewrite the resulting
      `natChoose n (n - k)` to `natChoose n k` via `natChoose_symmetry`.
    * `0 < k ≤ n - k` (the direct loop branch) → use `binomial_loop_case`
      directly.

    All structural / case-analysis work is done here; the remaining
    unproven content is the loop case itself (`binomial_loop_case`),
    whose docstring lays out the body-step obligation and the
    `gcd_u64`-correctness structural unblock. -/
theorem binomial_postcondition (n k : u64) (hn : n.toNat ≤ 67) :
    binomial_u64.binomial n k
      = RustM.ok (UInt64.ofNat (natChoose n.toNat k.toNat)) := by
  -- Case 1: `k > n`.
  by_cases h_k_gt_n : n.toNat < k.toNat
  · rw [binomial_k_gt_n n k h_k_gt_n]
    apply congrArg RustM.ok
    rw [natChoose_eq_zero_of_lt n.toNat k.toNat h_k_gt_n]
    rfl
  have h_kn : k.toNat ≤ n.toNat := Nat.not_lt.mp h_k_gt_n
  -- Case 2: `k = 0`.
  by_cases h_k_eq : k = 0
  · subst h_k_eq
    rw [binomial_k_zero n]
    show RustM.ok 1 = RustM.ok (UInt64.ofNat (natChoose n.toNat 0))
    rw [natChoose_zero_right n.toNat]
    rfl
  have h_k_pos : 0 < k.toNat := by
    rcases Nat.eq_zero_or_pos k.toNat with h | h
    · exfalso; apply h_k_eq; apply UInt64.toNat_inj.mp; rw [h]; rfl
    · exact h
  have h_sub_eq : (n - k).toNat = n.toNat - k.toNat := UInt64.toNat_sub_of_le' h_kn
  -- Case 3: `k = n`. Use `binomial_k_eq_n` + `natChoose_symmetry`.
  by_cases h_k_eq_n_nat : k.toNat = n.toNat
  · have h_k_eq_n_u64 : k = n := UInt64.toNat_inj.mp h_k_eq_n_nat
    rw [h_k_eq_n_u64, binomial_k_eq_n n]
    show RustM.ok 1 = RustM.ok (UInt64.ofNat (natChoose n.toNat n.toNat))
    have h_nc_nn : natChoose n.toNat n.toNat = 1 := by
      rw [natChoose_symmetry n.toNat n.toNat (Nat.le_refl _), Nat.sub_self]
      exact natChoose_zero_right n.toNat
    rw [h_nc_nn]
    rfl
  have h_k_lt_n : k.toNat < n.toNat := Nat.lt_of_le_of_ne h_kn h_k_eq_n_nat
  -- Case 4: `0 < k < n`. Split on whether `k > n - k`.
  by_cases h_swap : (n - k).toNat < k.toNat
  · -- 4a: `k > n - k`. Use symmetry to swap, then loop_case on (n, n - k).
    have h_swap_nat : n.toNat - k.toNat < k.toNat := by
      rw [h_sub_eq] at h_swap; exact h_swap
    have h_nk_pos : 0 < (n - k).toNat := by rw [h_sub_eq]; omega
    have h_2nk_le_n : 2 * (n - k).toNat ≤ n.toNat := by
      rw [h_sub_eq]; omega
    rw [binomial_symmetry n k h_kn]
    rw [binomial_loop_case n (n - k) hn h_nk_pos h_2nk_le_n]
    apply congrArg RustM.ok
    apply congrArg UInt64.ofNat
    rw [h_sub_eq]
    exact (natChoose_symmetry n.toNat k.toNat h_kn).symm
  · -- 4b: `k ≤ n - k`. Direct loop case.
    have h_swap_nat : k.toNat ≤ n.toNat - k.toNat := by
      rw [h_sub_eq] at h_swap
      omega
    have h_2k_le_n : 2 * k.toNat ≤ n.toNat := by omega
    exact binomial_loop_case n k hn h_k_pos h_2k_le_n

/-- Pascal's recurrence: for `1 ≤ k ≤ n` (and within the overflow-free range
    `n ≤ 50` used by the property test `pascal_recurrence`),
    `C(n, k) = C(n - 1, k - 1) + C(n - 1, k)` at the `u64` level.
    The existential bundles the three successful results so the equality
    can be stated on plain `u64` values; for `n ≤ 50` every term fits in
    `u64` (`C(50, 25) ≈ 1.26 × 10^14 ≪ 2^64`) so the `u64` addition does
    not overflow.

    Proved as a corollary of `binomial_postcondition` applied three times,
    plus the definitional identity `natChoose (m+1) (j+1) = natChoose m j
    + natChoose m (j+1)` and a row-sum bound `natChoose m _ ≤ 2 ^ m` that
    rules out overflow on the `u64` addition. `binomial_postcondition`
    itself is fully closed (full case-split + `binomial_loop_case` helper);
    the only `sorry` it depends on is the body-step of the inner
    `while d ≤ k` loop inside `binomial_loop_case` — see its docstring
    for the precise stuck sub-goal and the `gcd_u64`-correctness +
    `natChoose_lt_two_pow_64` structural unblock that would close it. -/
theorem binomial_pascal_recurrence (n k : u64)
    (hk_pos : 0 < k.toNat) (hkn : k.toNat ≤ n.toNat) (hn : n.toNat ≤ 50) :
    ∃ v vsub1 vsub2 : u64,
      binomial_u64.binomial n k = RustM.ok v ∧
      binomial_u64.binomial (n - 1) (k - 1) = RustM.ok vsub1 ∧
      binomial_u64.binomial (n - 1) k = RustM.ok vsub2 ∧
      v = vsub1 + vsub2 := by
  have hn_pos : 0 < n.toNat := Nat.lt_of_lt_of_le hk_pos hkn
  have hn67 : n.toNat ≤ 67 := by omega
  have h_one_le_n : (1 : u64).toNat ≤ n.toNat := by
    show 1 ≤ n.toNat; omega
  have h_one_le_k : (1 : u64).toNat ≤ k.toNat := by
    show 1 ≤ k.toNat; omega
  have hn1_eq : (n - 1).toNat = n.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le' h_one_le_n]; rfl
  have hk1_eq : (k - 1).toNat = k.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le' h_one_le_k]; rfl
  have hn1_67 : (n - 1).toNat ≤ 67 := by rw [hn1_eq]; omega
  -- Pull the three successful values out of `binomial_postcondition`.
  refine ⟨_, _, _,
          binomial_postcondition n k hn67,
          binomial_postcondition (n - 1) (k - 1) hn1_67,
          binomial_postcondition (n - 1) k hn1_67, ?_⟩
  -- Reduce the `(n-1)` / `(k-1)` toNats to `n.toNat - 1` / `k.toNat - 1`.
  rw [hn1_eq, hk1_eq]
  -- Pattern: `n.toNat = m + 1`, `k.toNat = j + 1`.
  obtain ⟨m, hm⟩ : ∃ m, n.toNat = m + 1 := ⟨n.toNat - 1, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, k.toNat = j + 1 := ⟨k.toNat - 1, by omega⟩
  rw [hm, hj]
  rw [show m + 1 - 1 = m from rfl, show j + 1 - 1 = j from rfl]
  -- Definitional unfold of `natChoose (m+1) (j+1)`.
  show UInt64.ofNat (natChoose m j + natChoose m (j + 1)) =
       UInt64.ofNat (natChoose m j) + UInt64.ofNat (natChoose m (j + 1))
  -- Bounds: with `n.toNat = m + 1 ≤ 50`, we have `m ≤ 49`, so every
  -- `natChoose m _ ≤ 2 ^ 49`, hence the sum and either summand fit in `u64`.
  have hm_le_49 : m ≤ 49 := by omega
  have h1_bound : natChoose m j ≤ 2 ^ m := natChoose_le_two_pow m j
  have h2_bound : natChoose m (j + 1) ≤ 2 ^ m := natChoose_le_two_pow m (j + 1)
  have h_2m_le : 2 ^ m ≤ 2 ^ 49 :=
    Nat.pow_le_pow_right (by decide : 1 ≤ 2) hm_le_49
  have h_2_49_lt : 2 ^ 49 + 2 ^ 49 < 2 ^ 64 := by decide
  have h_sum_lt : natChoose m j + natChoose m (j + 1) < 2 ^ 64 := by omega
  have h1_lt : natChoose m j < 2 ^ 64 := by omega
  have h2_lt : natChoose m (j + 1) < 2 ^ 64 := by omega
  have h_no_overflow :
      (UInt64.ofNat (natChoose m j)).toNat
        + (UInt64.ofNat (natChoose m (j + 1))).toNat < 2 ^ 64 := by
    rw [UInt64.toNat_ofNat_of_lt' h1_lt, UInt64.toNat_ofNat_of_lt' h2_lt]
    exact h_sum_lt
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add_of_lt h_no_overflow]
  rw [UInt64.toNat_ofNat_of_lt' h_sum_lt,
      UInt64.toNat_ofNat_of_lt' h1_lt,
      UInt64.toNat_ofNat_of_lt' h2_lt]

/-- Totality / no-panic: in the overflow-free range `n ≤ 67`, the function
    returns successfully for every `k`.  Together with the property tests
    (which all stay in the overflow-free range), this is the explicit
    "no failure mode" clause of the contract. -/
theorem binomial_total (n k : u64) (hn : n.toNat ≤ 67) :
    ∃ v : u64, binomial_u64.binomial n k = RustM.ok v :=
  ⟨_, binomial_postcondition n k hn⟩

end Binomial_u64Obligations
