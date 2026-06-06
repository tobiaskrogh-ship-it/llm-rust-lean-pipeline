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

/-! ## Mathematical binomial coefficient on `Nat`.

Lean core does not provide `Nat.choose` (only Mathlib does); define one locally
so the master postcondition can state the closed form `binomial n k = ofNat (C n k)`. -/

/-- Mathematical binomial coefficient. Standard Pascal-triangle definition. -/
def nchoose : Nat → Nat → Nat
  | _,     0     => 1
  | 0,     _ + 1 => 0
  | n + 1, k + 1 => nchoose n k + nchoose n (k + 1)

/-! ## Nat-level helpers for `nchoose`.

These are purely-mathematical facts about the locally-defined binomial
coefficient `nchoose`. They are independent of the Rust extraction; the
two non-trivial ones (`nchoose_eq_zero_of_lt` and `nchoose_pascal`)
do not require a finite-case check and discharge straightforwardly. -/

/-- `nchoose n k = 0` for `n < k`. The induction follows the standard
    Pascal-triangle definition. -/
private theorem nchoose_eq_zero_of_lt : ∀ n k, n < k → nchoose n k = 0
  | _, 0, h => by omega
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    show nchoose n k + nchoose n (k + 1) = 0
    have h1 : n < k := by omega
    have h2 : n < k + 1 := by omega
    rw [nchoose_eq_zero_of_lt n k h1, nchoose_eq_zero_of_lt n (k + 1) h2]

/-- Pascal's recurrence on `nchoose` (definitional). -/
private theorem nchoose_pascal (m j : Nat) :
    nchoose (m + 1) (j + 1) = nchoose m j + nchoose m (j + 1) := rfl

/-- `nchoose n n = 1` for all `n`. Induction with `nchoose_eq_zero_of_lt`
    discharging the second summand at each step. -/
private theorem nchoose_self : ∀ n, nchoose n n = 1
  | 0 => rfl
  | n + 1 => by
    show nchoose n n + nchoose n (n + 1) = 1
    rw [nchoose_self n, nchoose_eq_zero_of_lt n (n + 1) (Nat.lt_succ_self n)]

/-! ### Efficient Pascal-row computation for finite bound checks.

`nchoose` is recursive with exponential branching, so any concrete bound
(`nchoose 67 33 < 2 ^ 64`) is intractable to reduce via `decide`/`native_decide`.
We instead define `pascalRow n` as a list of length `n + 1` whose `k`-th entry
equals `nchoose n k`, computed iteratively in O(n²) operations. Then
`native_decide` on the bound check via `pascalRow` is fast. -/

/-- Compute the next Pascal row by summing shifted copies. -/
private def pascalNext (row : List Nat) : List Nat :=
  List.zipWith (· + ·) (0 :: row) (row ++ [0])

/-- `pascalRow n = [nchoose n 0, nchoose n 1, ..., nchoose n n]`. -/
private def pascalRow : Nat → List Nat
  | 0 => [1]
  | n + 1 => pascalNext (pascalRow n)

/-- Look up `nchoose n k` through the efficient row computation. -/
private def nchooseFast (n k : Nat) : Nat := (pascalRow n).getD k 0

/-- `(row ++ [0]).getD k 0 = row.getD k 0` — appending a default value to
    a list does not change `getD k 0`. -/
private theorem getD_append_zero (row : List Nat) (k : Nat) :
    (row ++ [0]).getD k 0 = row.getD k 0 := by
  induction row generalizing k with
  | nil =>
    show ([0] : List Nat).getD k 0 = 0
    cases k with
    | zero => rfl
    | succ k =>
      show ([] : List Nat).getD k 0 = 0
      rfl
  | cons h t ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih k

/-- `getD` of `zipWith (· + ·)` on equal-length lists distributes elementwise
    when the default is `0`. -/
private theorem zipWith_add_getD (l1 l2 : List Nat) (h : l1.length = l2.length)
    (k : Nat) :
    (List.zipWith (· + ·) l1 l2).getD k 0 = l1.getD k 0 + l2.getD k 0 := by
  induction l1 generalizing l2 k with
  | nil =>
    have hl2 : l2 = [] := by
      cases l2 with
      | nil => rfl
      | cons _ _ => simp at h
    subst hl2
    rfl
  | cons h1 t1 ih1 =>
    cases l2 with
    | nil => simp at h
    | cons h2 t2 =>
      have ht : t1.length = t2.length := by simpa using h
      cases k with
      | zero => rfl
      | succ k => exact ih1 t2 ht k

/-- The Pascal-row recurrence at index `k`. -/
private theorem pascalNext_getD (row : List Nat) (k : Nat) :
    (pascalNext row).getD k 0 =
      (match k with | 0 => 0 | j + 1 => row.getD j 0) + row.getD k 0 := by
  show (List.zipWith (· + ·) (0 :: row) (row ++ [0])).getD k 0 = _
  have hlen : (0 :: row).length = (row ++ [0]).length := by
    simp [List.length_cons, List.length_append]
  rw [zipWith_add_getD _ _ hlen]
  rw [getD_append_zero]
  cases k with
  | zero => rfl
  | succ k => rfl

/-- `pascalRow n` looks up to `nchoose n k`. The fundamental equivalence. -/
private theorem pascalRow_getD : ∀ n k, (pascalRow n).getD k 0 = nchoose n k
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | n + 1, 0 => by
    show (pascalNext (pascalRow n)).getD 0 0 = 1
    rw [pascalNext_getD]
    show 0 + (pascalRow n).getD 0 0 = 1
    rw [pascalRow_getD n 0]
    -- nchoose n 0 = 1 by case split on n
    have h : nchoose n 0 = 1 := by
      cases n with
      | zero => rfl
      | succ _ => rfl
    rw [h]
  | n + 1, k + 1 => by
    show (pascalNext (pascalRow n)).getD (k + 1) 0 = nchoose (n + 1) (k + 1)
    rw [pascalNext_getD]
    show (pascalRow n).getD k 0 + (pascalRow n).getD (k + 1) 0 = nchoose n k + nchoose n (k + 1)
    rw [pascalRow_getD n k, pascalRow_getD n (k + 1)]

/-- `nchooseFast = nchoose` (corollary). -/
private theorem nchooseFast_eq (n k : Nat) : nchooseFast n k = nchoose n k :=
  pascalRow_getD n k

/-- Bound check via the efficient `nchooseFast`: `native_decide` on the
    finite 68 × 68 cases (n ≤ 67, k ≤ 67) reduces to evaluating a
    quadratic-time computation. -/
private theorem nchooseFast_lt_2_64_aux :
    ∀ (n k : Fin 68), nchooseFast n.val k.val < 2 ^ 64 := by native_decide

/-- The main bound: `nchoose n k < 2 ^ 64` for `n ≤ 67`. Routes through
    the efficient `nchooseFast`. -/
private theorem nchoose_lt_2_64 (n k : Nat) (hn : n ≤ 67) :
    nchoose n k < 2 ^ 64 := by
  rcases Nat.lt_or_ge n k with h | h
  · rw [nchoose_eq_zero_of_lt n k h]; exact Nat.two_pow_pos _
  · have hk : k ≤ 67 := Nat.le_trans h hn
    have := nchooseFast_lt_2_64_aux ⟨n, by omega⟩ ⟨k, by omega⟩
    rw [nchooseFast_eq] at this
    exact this

/-- Symmetry of `nchoose`: `nchoose n k = nchoose n (n - k)` for `k ≤ n`.
    Pure Nat-level fact, proved by structural induction. -/
private theorem nchoose_symm : ∀ n k, k ≤ n → nchoose n k = nchoose n (n - k)
  | 0,     0,     _ => rfl
  | 0,     _ + 1, h => by omega
  | n + 1, 0,     _ => by
    show 1 = nchoose (n + 1) (n + 1 - 0)
    rw [Nat.sub_zero]
    exact (nchoose_self (n + 1)).symm
  | n + 1, k + 1, h => by
    have hk : k ≤ n := by omega
    -- LHS: nchoose (n+1) (k+1) = nchoose n k + nchoose n (k+1)
    show nchoose n k + nchoose n (k + 1) = nchoose (n + 1) (n + 1 - (k + 1))
    have h_rhs_sub : n + 1 - (k + 1) = n - k := by omega
    rw [h_rhs_sub]
    by_cases hk_lt_n : k + 1 ≤ n
    · -- k + 1 ≤ n: use IH on both summands of LHS.
      have h_ih1 : nchoose n k = nchoose n (n - k) := nchoose_symm n k hk
      have h_ih2 : nchoose n (k + 1) = nchoose n (n - (k + 1)) :=
        nchoose_symm n (k + 1) hk_lt_n
      rw [h_ih1, h_ih2]
      -- Goal: nchoose n (n - k) + nchoose n (n - (k + 1)) = nchoose (n + 1) (n - k)
      -- n - k = (n - k - 1) + 1 = ((n - (k+1))) + 1.
      have hj_eq : ∃ j, n - k = j + 1 := ⟨n - k - 1, by omega⟩
      obtain ⟨j, hj⟩ := hj_eq
      have hj' : n - (k + 1) = j := by omega
      rw [hj, hj']
      -- Goal: nchoose n (j + 1) + nchoose n j = nchoose (n + 1) (j + 1)
      show nchoose n (j + 1) + nchoose n j = nchoose n j + nchoose n (j + 1)
      omega
    · -- k + 1 > n; combined with k + 1 ≤ n + 1, this forces k = n.
      have hk_eq_n : k = n := by omega
      rw [hk_eq_n, Nat.sub_self]
      -- Goal: nchoose n n + nchoose n (n + 1) = nchoose (n + 1) 0
      show nchoose n n + nchoose n (n + 1) = 1
      rw [nchoose_self n, nchoose_eq_zero_of_lt n (n + 1) (Nat.lt_succ_self n)]

/-! ## Trailing-zeros infrastructure (port from `trailing_zeros_u64_modified`).

The local `binomial_u64.trailing_zeros_u64` has the same body as the
reference target's `trailing_zeros_u64`, so the proof carries verbatim —
only the namespace prefix changes. -/

open rust_primitives.hax (Tuple2)

/-- `RustM.ok`-headed bind reduction (`RustM.ok` is `pure` for `RustM`). -/
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private def tzInv (x₀ : u64) (s : Tuple2 u32 u64) : Prop :=
  x₀.toNat = s._1.toNat * 2 ^ s._0.toNat ∧ 0 < s._1.toNat ∧ s._0.toNat < 64

private def tzTerm (s : Tuple2 u32 u64) : Nat := s._1.toNat

private abbrev tzCond : Tuple2 u32 u64 → Bool :=
  fun b => UInt64.toNat (b._1 &&& 1) == UInt64.toNat 0

private abbrev tzBody : Tuple2 u32 u64 → RustM (Tuple2 u32 u64) :=
  fun x =>
    match x with
    | ⟨count, y⟩ =>
      (do
        let y : u64 ← (y >>>? (1 : i32))
        let count : u32 ← (count +? (1 : u32))
        pure (rust_primitives.hax.Tuple2.mk count y) :
        RustM (rust_primitives.hax.Tuple2 u32 u64))

private abbrev tzLoop (x : u64) : RustM (Tuple2 u32 u64) :=
  Lean.Loop.MonoLoopCombinator.while_loop Lean.Loop.mk tzCond
    (rust_primitives.hax.Tuple2.mk (0 : u32) x) tzBody

private theorem tz_body_step_nat (x₀ : u64) (c : u32) (y : u64)
    (hinv : tzInv x₀ ⟨c, y⟩) (hcond : tzCond ⟨c, y⟩ = true) :
    c.toNat + 1 < 2 ^ 32 ∧
    (y >>> (1 : UInt64)).toNat < y.toNat ∧
    tzInv x₀ ⟨c + 1, y >>> (1 : UInt64)⟩ := by
  unfold tzInv at hinv
  simp only at hinv
  obtain ⟨hx, hy_pos, hc_lt⟩ := hinv
  have h_y_and : (y &&& 1).toNat = 0 := by
    have hb : (UInt64.toNat (y &&& 1) == UInt64.toNat 0) = true := hcond
    have : UInt64.toNat (y &&& 1) = UInt64.toNat 0 := beq_iff_eq.mp hb
    simpa using this
  have h_y_even : y.toNat % 2 = 0 := by
    have : y.toNat &&& 1 = 0 := by
      have := h_y_and
      rw [UInt64.toNat_and] at this
      rw [UInt64.toNat_one] at this
      exact this
    rw [← Nat.and_one_is_mod]; exact this
  have h_y_ge_2 : y.toNat ≥ 2 := by omega
  refine ⟨by omega, ?_, ?_⟩
  · rw [UInt64.toNat_shiftRight, UInt64.toNat_one]
    show y.toNat >>> (1 % 64) < y.toNat
    rw [show (1 % 64 : Nat) = 1 from rfl, Nat.shiftRight_eq_div_pow,
        show (2 ^ 1 : Nat) = 2 from rfl]
    exact Nat.div_lt_self (by omega) (by decide)
  · have h_cplus : (c + (1 : u32)).toNat = c.toNat + 1 := by
      apply UInt32.toNat_add_of_lt
      have h1 : (1 : UInt32).toNat = 1 := rfl
      rw [h1]; omega
    have h_yshr : (y >>> (1 : UInt64)).toNat = y.toNat / 2 := by
      rw [UInt64.toNat_shiftRight, UInt64.toNat_one]
      show y.toNat >>> (1 % 64) = _
      rw [show (1 % 64 : Nat) = 1 from rfl, Nat.shiftRight_eq_div_pow,
          show (2 ^ 1 : Nat) = 2 from rfl]
    have h_new_y_pos : 0 < y.toNat / 2 := Nat.div_pos h_y_ge_2 (by decide)
    have h_y_div_mul : y.toNat / 2 * 2 = y.toNat := by
      have := Nat.div_add_mod y.toNat 2
      omega
    have h_x_eq : x₀.toNat = y.toNat / 2 * 2 ^ (c.toNat + 1) := by
      have key : y.toNat * 2 ^ c.toNat = y.toNat / 2 * 2 ^ (c.toNat + 1) := by
        rw [Nat.pow_succ,
            show 2 ^ c.toNat * 2 = 2 * 2 ^ c.toNat from Nat.mul_comm _ _,
            ← Nat.mul_assoc, h_y_div_mul]
      rw [← key]; exact hx
    have h_cplus_lt_64 : c.toNat + 1 < 64 := by
      have h_x_lt : x₀.toNat < 2 ^ 64 := UInt64.toNat_lt x₀
      have h_pow_le : 2 ^ (c.toNat + 1) ≤ x₀.toNat := by
        rw [h_x_eq]; exact Nat.le_mul_of_pos_left _ h_new_y_pos
      have h_pow_lt : 2 ^ (c.toNat + 1) < 2 ^ 64 :=
        Nat.lt_of_le_of_lt h_pow_le h_x_lt
      exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h_pow_lt
    refine ⟨?_, ?_, ?_⟩
    · show x₀.toNat = (y >>> (1 : UInt64)).toNat * 2 ^ (c + (1 : u32)).toNat
      rw [h_yshr, h_cplus]; exact h_x_eq
    · show 0 < (y >>> (1 : UInt64)).toNat
      rw [h_yshr]; exact h_new_y_pos
    · show (c + (1 : u32)).toNat < 64
      rw [h_cplus]; exact h_cplus_lt_64

private theorem tz_loop_triple (x₀ : u64) :
    ⦃⌜ tzInv x₀ ⟨(0 : u32), x₀⟩ ⌝⦄
      tzLoop x₀
    ⦃⇓ r => ⌜ tzInv x₀ r ∧ ¬ tzCond r = true ⌝⦄ := by
  apply Std.Do.Spec.MonoLoopCombinator.while_loop
    (rust_primitives.hax.Tuple2.mk (0 : u32) x₀) Lean.Loop.mk
    tzCond tzBody (tzInv x₀) tzTerm
  intro s hcond hinv
  cases s with
  | mk c y =>
    have hstep := tz_body_step_nat x₀ c y hinv hcond
    obtain ⟨h_no_add_ovf, h_term_dec, h_inv'⟩ := hstep
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
    have h_add : (c +? (1 : u32) : RustM u32) = pure (c + 1) := by
      show (rust_primitives.ops.arith.Add.add c (1 : u32) : RustM u32) =
           pure (c + 1)
      show (if BitVec.uaddOverflow c.toBitVec (1 : u32).toBitVec then
              (.fail .integerOverflow : RustM u32)
            else pure (c + 1)) = pure (c + 1)
      have h_no_ovf : BitVec.uaddOverflow c.toBitVec ((1 : u32).toBitVec) = false := by
        cases h_eq : BitVec.uaddOverflow c.toBitVec ((1 : u32).toBitVec) with
        | false => rfl
        | true =>
          exfalso
          have : UInt32.addOverflow c (1 : u32) = true := h_eq
          rw [UInt32.addOverflow_iff] at this
          have h1 : (1 : UInt32).toNat = 1 := rfl
          rw [h1] at this; omega
      rw [h_no_ovf]; rfl
    dsimp only [tzBody]
    rw [h_shr]
    simp only [pure_bind]
    rw [h_add]
    simp only [pure_bind]
    refine ⟨?_, h_inv'⟩
    show tzTerm ⟨c + 1, y >>> 1⟩ < tzTerm ⟨c, y⟩
    show (y >>> (1 : UInt64)).toNat < y.toNat
    exact h_term_dec

private theorem tz_function_nonzero_triple (x : u64) (hx : x ≠ 0) :
    ⦃⌜ True ⌝⦄
      binomial_u64.trailing_zeros_u64 x
    ⦃⇓ r => ⌜ r.toNat < 64 ∧ 2 ^ r.toNat ∣ x.toNat ∧
              (x.toNat >>> r.toNat) &&& 1 = 1 ⌝⦄ := by
  have h_loop := tz_loop_triple x
  have h_loop' :
      ⦃⌜ tzInv x ⟨(0 : u32), x⟩ ⌝⦄
        tzLoop x
      ⦃⇓ r => ⌜ r._0.toNat < 64 ∧ 2 ^ r._0.toNat ∣ x.toNat ∧
                (x.toNat >>> r._0.toNat) &&& 1 = 1 ⌝⦄ := by
    apply Triple.of_entails_right _ _ _ _ h_loop
    apply PostCond.entails.of_left_entails
    intro r ⟨hinv, hncond⟩
    unfold tzInv at hinv
    obtain ⟨hx_eq, hy_pos, hc_lt⟩ := hinv
    have h_y_odd : r._1.toNat % 2 = 1 := by
      have h_ne_zero : ¬ ((UInt64.toNat (r._1 &&& 1)) == UInt64.toNat 0) = true := hncond
      rw [beq_iff_eq] at h_ne_zero
      have h_neq : UInt64.toNat (r._1 &&& 1) ≠ UInt64.toNat 0 := h_ne_zero
      rw [UInt64.toNat_and, UInt64.toNat_one] at h_neq
      have h0 : (UInt64.toNat 0 : Nat) = 0 := rfl
      rw [h0] at h_neq
      rw [← Nat.and_one_is_mod]
      have h_bound : r._1.toNat &&& 1 ≤ 1 := Nat.and_le_right
      omega
    refine ⟨hc_lt, ?_, ?_⟩
    · rw [hx_eq]
      exact ⟨r._1.toNat, by rw [Nat.mul_comm]⟩
    · rw [hx_eq]
      have h_div : (r._1.toNat * 2 ^ r._0.toNat) >>> r._0.toNat = r._1.toNat := by
        rw [Nat.shiftRight_eq_div_pow]
        have hpos : 0 < 2 ^ r._0.toNat := Nat.two_pow_pos r._0.toNat
        exact Nat.mul_div_cancel _ hpos
      rw [h_div, Nat.and_one_is_mod]
      exact h_y_odd
  have h_loop'' :
      ⦃⌜ True ⌝⦄
        tzLoop x
      ⦃⇓ r => ⌜ r._0.toNat < 64 ∧ 2 ^ r._0.toNat ∣ x.toNat ∧
                (x.toNat >>> r._0.toNat) &&& 1 = 1 ⌝⦄ := by
    apply Triple.of_entails_left _ _ _ _ h_loop'
    intro _
    show tzInv x ⟨(0 : u32), x⟩
    refine ⟨?_, ?_, ?_⟩
    · show x.toNat = x.toNat * 2 ^ ((0 : u32).toNat)
      rw [show ((0 : u32).toNat) = 0 from rfl, Nat.pow_zero, Nat.mul_one]
    · show 0 < x.toNat
      rcases Nat.eq_zero_or_pos x.toNat with h | h
      · exfalso; apply hx; apply UInt64.toNat_inj.mp; rw [h]; rfl
      · exact h
    · show (0 : u32).toNat < 64; decide
  unfold binomial_u64.trailing_zeros_u64
  unfold rust_primitives.hax.while_loop
  show ⦃⌜True⌝⦄
        ((x ==? (0 : u64)) >>= fun b =>
          if b = true then pure (64 : u32)
          else (tzLoop x >>= fun __discr =>
                  match __discr with | ⟨c, _⟩ => pure c))
        ⦃⇓ r => ⌜r.toNat < 64 ∧ 2 ^ r.toNat ∣ x.toNat ∧ (x.toNat >>> r.toNat) &&& 1 = 1⌝⦄
  show ⦃⌜True⌝⦄
        ((pure (x == (0 : u64)) : RustM Bool) >>= fun b =>
          if b = true then pure (64 : u32)
          else (tzLoop x >>= fun __discr =>
                  match __discr with | ⟨c, _⟩ => pure c))
        ⦃⇓ r => ⌜r.toNat < 64 ∧ 2 ^ r.toNat ∣ x.toNat ∧ (x.toNat >>> r.toNat) &&& 1 = 1⌝⦄
  simp only [pure_bind]
  have h_eq_false : (x == (0 : u64)) = false := by
    rw [beq_eq_false_iff_ne]; exact hx
  rw [h_eq_false]
  simp only [if_false, Bool.false_eq_true]
  apply Triple.bind _ _ h_loop''
  intro s
  cases s with
  | mk c y =>
    refine Triple.pure c ?_
    intro h
    exact h

/-- Trailing-zeros master existential on the local `binomial_u64.trailing_zeros_u64`. -/
private theorem tz_nonzero_spec (x : u64) (hx : x ≠ 0) :
    ∃ r : u32, binomial_u64.trailing_zeros_u64 x = RustM.ok r ∧
                r.toNat < 64 ∧
                2 ^ r.toNat ∣ x.toNat ∧
                (x.toNat >>> r.toNat) &&& 1 = 1 := by
  have h := tz_function_nonzero_triple x hx
  rw [RustM.Triple_iff_BitVec] at h
  simp only [decide_true, Bool.not_true, Bool.false_or,
             Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hok, hpost⟩ := h
  cases hf : binomial_u64.trailing_zeros_u64 x with
  | none => rw [hf] at hok; simp [RustM.toBVRustM] at hok
  | some result =>
    cases result with
    | ok v =>
      rw [hf] at hpost
      simp only [RustM.toBVRustM] at hpost
      exact ⟨v, rfl, hpost.1, hpost.2.1, hpost.2.2⟩
    | error e =>
      rw [hf] at hok
      cases e <;> simp [RustM.toBVRustM] at hok

/-- Trailing-zeros at zero: definitional. -/
private theorem tz_zero :
    binomial_u64.trailing_zeros_u64 (0 : u64) = RustM.ok (64 : u32) := by
  unfold binomial_u64.trailing_zeros_u64
  rfl

/-! ## Nat-level Stein identities (helpers for `gcd_stein_loop` and `gcd_u64`). -/

/-- `gcd(2m, 2n) = 2 * gcd(m, n)`. Stein's halving identity. -/
private theorem nat_gcd_double_both (m n : Nat) :
    Nat.gcd (2 * m) (2 * n) = 2 * Nat.gcd m n :=
  Nat.gcd_mul_left 2 m n

/-- Key auxiliary: odd `d` divides `2 * m` implies `d` divides `m`. -/
private theorem odd_dvd_two_mul {d m : Nat} (hd : d % 2 = 1) (h : d ∣ 2 * m) :
    d ∣ m := by
  obtain ⟨k, hk⟩ := h
  have hk_even : k % 2 = 0 := by
    have h_zero : (2 * m) % 2 = 0 := Nat.mul_mod_right 2 m
    rw [hk, Nat.mul_mod, hd, Nat.one_mul, Nat.mod_mod] at h_zero
    exact h_zero
  obtain ⟨k', hk'⟩ : 2 ∣ k := Nat.dvd_of_mod_eq_zero hk_even
  refine ⟨k', ?_⟩
  have h1 : 2 * m = d * (2 * k') := by rw [hk, hk']
  have h2 : 2 * m = 2 * (d * k') := by
    rw [h1, ← Nat.mul_assoc, Nat.mul_comm d 2, Nat.mul_assoc]
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h2

/-- `gcd(2m, n) = gcd(m, n)` when `n` is odd. -/
private theorem nat_gcd_two_left_odd_right (m n : Nat) (hn : n % 2 = 1) :
    Nat.gcd (2 * m) n = Nat.gcd m n := by
  refine Nat.dvd_antisymm ?_ ?_
  · apply Nat.dvd_gcd
    · have h_dvd_2m : Nat.gcd (2 * m) n ∣ 2 * m := Nat.gcd_dvd_left _ _
      have h_dvd_n : Nat.gcd (2 * m) n ∣ n := Nat.gcd_dvd_right _ _
      have h_g_odd : Nat.gcd (2 * m) n % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one (Nat.gcd (2 * m) n) with hg | hg
        · exfalso
          have h_2_dvd_g : 2 ∣ Nat.gcd (2 * m) n := Nat.dvd_of_mod_eq_zero hg
          have h_2_dvd_n : 2 ∣ n := Nat.dvd_trans h_2_dvd_g h_dvd_n
          have h_n_mod : n % 2 = 0 := Nat.mod_eq_zero_of_dvd h_2_dvd_n
          omega
        · exact hg
      exact odd_dvd_two_mul h_g_odd h_dvd_2m
    · exact Nat.gcd_dvd_right _ _
  · apply Nat.dvd_gcd
    · exact Nat.dvd_trans (Nat.gcd_dvd_left _ _) ⟨2, by rw [Nat.mul_comm]⟩
    · exact Nat.gcd_dvd_right _ _

/-- `gcd(m, n) = gcd(m - n, n)` for `m ≥ n`. Stein's subtract step. -/
private theorem nat_gcd_sub_right (m n : Nat) (h : n ≤ m) :
    Nat.gcd m n = Nat.gcd (m - n) n := by
  have h_eq : Nat.gcd m n = Nat.gcd ((m - n) + n) n := by
    rw [Nat.sub_add_cancel h]
  rw [h_eq, Nat.gcd_add_self_left]

/-- Power-of-two extension of `nat_gcd_two_left_odd_right`. -/
private theorem nat_gcd_mul_pow_two_left_odd_right (a n : Nat) (hn : n % 2 = 1) :
    ∀ k, Nat.gcd (a * 2 ^ k) n = Nat.gcd a n
  | 0 => by rw [Nat.pow_zero, Nat.mul_one]
  | k + 1 => by
    have ih := nat_gcd_mul_pow_two_left_odd_right a n hn k
    have h_eq : a * 2 ^ (k + 1) = 2 * (a * 2 ^ k) := by
      rw [Nat.pow_succ]
      rw [← Nat.mul_assoc, Nat.mul_comm (a * 2 ^ k) 2]
    rw [h_eq, nat_gcd_two_left_odd_right _ _ hn, ih]

/-! ## `gcd_stein_loop` closed form for odd, nonzero inputs. -/

/-- Helper Nat bound: `Nat.gcd a b < 2 ^ 64` for `a b : u64`. -/
private theorem gcd_lt_2_64 (a b : u64) : Nat.gcd a.toNat b.toNat < 2 ^ 64 := by
  by_cases hb : b.toNat = 0
  · rw [hb, Nat.gcd_zero_right]
    exact a.toNat_lt
  · have h_le : Nat.gcd a.toNat b.toNat ≤ b.toNat :=
      Nat.gcd_le_right a.toNat (Nat.pos_of_ne_zero hb)
    exact Nat.lt_of_le_of_lt h_le b.toNat_lt

/-- `Nat.gcd a b` lifted to `u64` round-trips through `ofNat`. -/
private theorem gcd_toNat_ofNat (a b : u64) :
    (UInt64.ofNat (Nat.gcd a.toNat b.toNat)).toNat = Nat.gcd a.toNat b.toNat :=
  UInt64.toNat_ofNat_of_lt' (gcd_lt_2_64 a b)

private theorem gcd_stein_loop_spec (m n : u64)
    (hm_odd : m.toNat % 2 = 1) (hn_odd : n.toNat % 2 = 1) :
    binomial_u64.gcd_stein_loop m n
      = RustM.ok (UInt64.ofNat (Nat.gcd m.toNat n.toNat)) := by
  have hm_pos : 0 < m.toNat := by omega
  have hn_pos : 0 < n.toNat := by omega
  induction hk : (m.toNat + n.toNat) using Nat.strongRecOn generalizing m n with
  | _ k ih =>
    unfold binomial_u64.gcd_stein_loop
    have h_mn_eqq : (m ==? n : RustM Bool) = pure (m == n) := rfl
    rw [h_mn_eqq]
    simp only [pure_bind]
    by_cases hmn : m = n
    · subst hmn
      have h_dec : (m == m) = true := beq_self_eq_true m
      rw [h_dec]
      simp only [if_true]
      show RustM.ok m = RustM.ok (UInt64.ofNat (Nat.gcd m.toNat m.toNat))
      congr 1
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_ofNat_of_lt' (by rw [Nat.gcd_self]; exact m.toNat_lt),
          Nat.gcd_self]
    · have h_mn_false : (m == n) = false := by
        rw [beq_eq_false_iff_ne]; exact hmn
      rw [h_mn_false]
      simp only [Bool.false_eq_true, if_false]
      have h_gt_eqq : (m >? n : RustM Bool) = pure (decide (m > n)) := rfl
      rw [h_gt_eqq]
      simp only [pure_bind]
      by_cases hgt : m > n
      · rw [decide_eq_true hgt]
        simp only [if_true]
        have hnm : n.toNat < m.toNat := UInt64.lt_iff_toNat_lt.mp hgt
        have h_sub : (m -? n : RustM u64) = pure (m - n) := by
          have h_no_underflow : UInt64.subOverflow m n = false := by
            generalize hbo : UInt64.subOverflow m n = bo
            cases bo with
            | false => rfl
            | true => exfalso; rw [UInt64.subOverflow_iff] at hbo; omega
          show (rust_primitives.ops.arith.Sub.sub m n : RustM u64) = pure (m - n)
          show (if BitVec.usubOverflow m.toBitVec n.toBitVec then
                  (.fail .integerOverflow : RustM u64) else pure (m - n)) = pure (m - n)
          rw [show BitVec.usubOverflow m.toBitVec n.toBitVec = false from h_no_underflow]
          rfl
        rw [h_sub]
        simp only [pure_bind]
        have hd_toNat : (m - n).toNat = m.toNat - n.toNat :=
          UInt64.toNat_sub_of_le' (Nat.le_of_lt hnm)
        have hd_ne : (m - n) ≠ 0 := by
          intro h
          have hz : (m - n).toNat = 0 := by rw [h]; rfl
          omega
        obtain ⟨r, h_tz, hr_lt, hr_dvd, hr_bit⟩ := tz_nonzero_spec (m - n) hd_ne
        rw [h_tz]
        simp only [RustM_ok_bind]
        have hr_lt_2_64 : r.toNat < 2 ^ 64 := by
          have h32 : r.toNat < 2 ^ 32 := UInt32.toNat_lt r
          omega
        have hr_uint64_toNat : (r.toNat.toUInt64).toNat = r.toNat :=
          UInt64.toNat_ofNat_of_lt' hr_lt_2_64
        have h_0_le : (0 : UInt32) ≤ r := by
          rw [UInt32.le_iff_toNat_le]
          show (0 : UInt32).toNat ≤ r.toNat
          have h0 : (0 : UInt32).toNat = 0 := rfl
          omega
        have h_lt_64 : r < (64 : UInt32) := by
          rw [UInt32.lt_iff_toNat_lt]
          show r.toNat < (64 : UInt32).toNat
          have h64 : (64 : UInt32).toNat = 64 := rfl
          omega
        have h_shr : ((m - n) >>>? r : RustM u64)
            = RustM.ok ((m - n) >>> r.toNat.toUInt64) := by
          show (rust_primitives.ops.bit.Shr.shr (m - n) r : RustM u64)
              = RustM.ok ((m - n) >>> r.toNat.toUInt64)
          show (if ((0 : UInt32) ≤ r && r < (64 : UInt32)) then
                  pure ((m - n) >>> r.toNat.toUInt64)
                else .fail .integerOverflow) = RustM.ok ((m - n) >>> r.toNat.toUInt64)
          have h_cond_eq : ((0 : UInt32) ≤ r && r < (64 : UInt32)) = true := by
            simp [h_0_le, h_lt_64]
          rw [h_cond_eq]; rfl
        rw [h_shr]
        simp only [RustM_ok_bind]
        have h_m'_toNat : ((m - n) >>> r.toNat.toUInt64).toNat
            = (m - n).toNat >>> r.toNat := by
          rw [UInt64.toNat_shiftRight, hr_uint64_toNat, Nat.mod_eq_of_lt hr_lt]
        have h_m'_div : ((m - n) >>> r.toNat.toUInt64).toNat
            = (m - n).toNat / 2 ^ r.toNat := by
          rw [h_m'_toNat, Nat.shiftRight_eq_div_pow]
        have h_m'_mul : ((m - n) >>> r.toNat.toUInt64).toNat * 2 ^ r.toNat
            = (m - n).toNat := by
          rw [h_m'_div]; exact Nat.div_mul_cancel hr_dvd
        have h_m'_odd : ((m - n) >>> r.toNat.toUInt64).toNat % 2 = 1 := by
          rw [h_m'_toNat, ← Nat.and_one_is_mod]; exact hr_bit
        have h_m'_pos : 0 < ((m - n) >>> r.toNat.toUInt64).toNat := by omega
        have h_meas : ((m - n) >>> r.toNat.toUInt64).toNat + n.toNat < k := by
          have h_le : ((m - n) >>> r.toNat.toUInt64).toNat ≤ (m - n).toNat := by
            rw [h_m'_div]; exact Nat.div_le_self _ _
          omega
        rw [ih (((m - n) >>> r.toNat.toUInt64).toNat + n.toNat) h_meas
              ((m - n) >>> r.toNat.toUInt64) n h_m'_odd hn_odd h_m'_pos hn_pos rfl]
        apply congrArg RustM.ok
        apply congrArg UInt64.ofNat
        rw [nat_gcd_sub_right m.toNat n.toNat (Nat.le_of_lt hnm), ← hd_toNat,
            ← h_m'_mul, nat_gcd_mul_pow_two_left_odd_right _ _ hn_odd]
      · rw [decide_eq_false hgt]
        simp only [Bool.false_eq_true, if_false]
        have hnm : m.toNat < n.toNat := by
          rcases Nat.lt_trichotomy m.toNat n.toNat with h | h | h
          · exact h
          · exfalso; exact hmn (UInt64.toNat_inj.mp h)
          · exfalso; exact hgt (UInt64.lt_iff_toNat_lt.mpr h)
        have h_sub : (n -? m : RustM u64) = pure (n - m) := by
          have h_no_underflow : UInt64.subOverflow n m = false := by
            generalize hbo : UInt64.subOverflow n m = bo
            cases bo with
            | false => rfl
            | true => exfalso; rw [UInt64.subOverflow_iff] at hbo; omega
          show (rust_primitives.ops.arith.Sub.sub n m : RustM u64) = pure (n - m)
          show (if BitVec.usubOverflow n.toBitVec m.toBitVec then
                  (.fail .integerOverflow : RustM u64) else pure (n - m)) = pure (n - m)
          rw [show BitVec.usubOverflow n.toBitVec m.toBitVec = false from h_no_underflow]
          rfl
        rw [h_sub]
        simp only [pure_bind]
        have hd_toNat : (n - m).toNat = n.toNat - m.toNat :=
          UInt64.toNat_sub_of_le' (Nat.le_of_lt hnm)
        have hd_ne : (n - m) ≠ 0 := by
          intro h
          have hz : (n - m).toNat = 0 := by rw [h]; rfl
          omega
        obtain ⟨r, h_tz, hr_lt, hr_dvd, hr_bit⟩ := tz_nonzero_spec (n - m) hd_ne
        rw [h_tz]
        simp only [RustM_ok_bind]
        have hr_lt_2_64 : r.toNat < 2 ^ 64 := by
          have h32 : r.toNat < 2 ^ 32 := UInt32.toNat_lt r
          omega
        have hr_uint64_toNat : (r.toNat.toUInt64).toNat = r.toNat :=
          UInt64.toNat_ofNat_of_lt' hr_lt_2_64
        have h_0_le : (0 : UInt32) ≤ r := by
          rw [UInt32.le_iff_toNat_le]
          show (0 : UInt32).toNat ≤ r.toNat
          have h0 : (0 : UInt32).toNat = 0 := rfl
          omega
        have h_lt_64 : r < (64 : UInt32) := by
          rw [UInt32.lt_iff_toNat_lt]
          show r.toNat < (64 : UInt32).toNat
          have h64 : (64 : UInt32).toNat = 64 := rfl
          omega
        have h_shr : ((n - m) >>>? r : RustM u64)
            = RustM.ok ((n - m) >>> r.toNat.toUInt64) := by
          show (rust_primitives.ops.bit.Shr.shr (n - m) r : RustM u64)
              = RustM.ok ((n - m) >>> r.toNat.toUInt64)
          show (if ((0 : UInt32) ≤ r && r < (64 : UInt32)) then
                  pure ((n - m) >>> r.toNat.toUInt64)
                else .fail .integerOverflow) = RustM.ok ((n - m) >>> r.toNat.toUInt64)
          have h_cond_eq : ((0 : UInt32) ≤ r && r < (64 : UInt32)) = true := by
            simp [h_0_le, h_lt_64]
          rw [h_cond_eq]; rfl
        rw [h_shr]
        simp only [RustM_ok_bind]
        have h_n'_toNat : ((n - m) >>> r.toNat.toUInt64).toNat
            = (n - m).toNat >>> r.toNat := by
          rw [UInt64.toNat_shiftRight, hr_uint64_toNat, Nat.mod_eq_of_lt hr_lt]
        have h_n'_div : ((n - m) >>> r.toNat.toUInt64).toNat
            = (n - m).toNat / 2 ^ r.toNat := by
          rw [h_n'_toNat, Nat.shiftRight_eq_div_pow]
        have h_n'_mul : ((n - m) >>> r.toNat.toUInt64).toNat * 2 ^ r.toNat
            = (n - m).toNat := by
          rw [h_n'_div]; exact Nat.div_mul_cancel hr_dvd
        have h_n'_odd : ((n - m) >>> r.toNat.toUInt64).toNat % 2 = 1 := by
          rw [h_n'_toNat, ← Nat.and_one_is_mod]; exact hr_bit
        have h_n'_pos : 0 < ((n - m) >>> r.toNat.toUInt64).toNat := by omega
        have h_meas : m.toNat + ((n - m) >>> r.toNat.toUInt64).toNat < k := by
          have h_le : ((n - m) >>> r.toNat.toUInt64).toNat ≤ (n - m).toNat := by
            rw [h_n'_div]; exact Nat.div_le_self _ _
          omega
        rw [ih (m.toNat + ((n - m) >>> r.toNat.toUInt64).toNat) h_meas
              m ((n - m) >>> r.toNat.toUInt64) hm_odd h_n'_odd hm_pos h_n'_pos rfl]
        apply congrArg RustM.ok
        apply congrArg UInt64.ofNat
        rw [Nat.gcd_comm m.toNat n.toNat,
            nat_gcd_sub_right n.toNat m.toNat (Nat.le_of_lt hnm), ← hd_toNat,
            ← h_n'_mul, nat_gcd_mul_pow_two_left_odd_right _ _ hm_odd]
        exact Nat.gcd_comm m.toNat _

/-! ## Outer-wrapper Nat helpers for `gcd_u64`. -/

/-- For odd `m, n`, `gcd (m * 2^p) (n * 2^q) = 2^(min p q) * gcd m n`. -/
private theorem gcd_two_pow_combine (m n p q : Nat)
    (hm : m % 2 = 1) (hn : n % 2 = 1) :
    Nat.gcd (m * 2 ^ p) (n * 2 ^ q) = 2 ^ (min p q) * Nat.gcd m n := by
  rcases Nat.le_total p q with hpq | hqp
  · rw [Nat.min_eq_left hpq]
    have h2q : (2 : Nat) ^ q = 2 ^ (q - p) * 2 ^ p := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [h2q, ← Nat.mul_assoc, Nat.gcd_mul_right]
    have h_strip : Nat.gcd m (n * 2 ^ (q - p)) = Nat.gcd m n := by
      rw [Nat.gcd_comm m (n * 2 ^ (q - p)),
          nat_gcd_mul_pow_two_left_odd_right n m hm (q - p),
          Nat.gcd_comm n m]
    rw [h_strip, Nat.mul_comm]
  · rw [Nat.min_eq_right hqp]
    have h2p : (2 : Nat) ^ p = 2 ^ (p - q) * 2 ^ q := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [h2p, ← Nat.mul_assoc, Nat.gcd_mul_right,
        nat_gcd_mul_pow_two_left_odd_right m n hn (p - q), Nat.mul_comm]

/-- If `2^s ∣ m * 2^t` with `m` odd, then `s ≤ t`. -/
private theorem pow_two_dvd_odd_mul (s m t : Nat)
    (hdvd : 2 ^ s ∣ m * 2 ^ t) (hm : m % 2 = 1) : s ≤ t := by
  by_cases hcon : s ≤ t
  · exact hcon
  · exfalso
    have hts : t + 1 ≤ s := by omega
    have h_dvd' : 2 ^ (t + 1) ∣ m * 2 ^ t := Nat.dvd_trans (Nat.pow_dvd_pow 2 hts) hdvd
    rw [Nat.pow_succ, Nat.mul_comm m (2 ^ t)] at h_dvd'
    have h2m : 2 ∣ m := (Nat.mul_dvd_mul_iff_left (Nat.two_pow_pos t)).mp h_dvd'
    omega

/-- `2^k ∣ z` iff all of `z`'s low `k` bits are zero. -/
private theorem two_pow_dvd_iff_testBit (k z : Nat) :
    2 ^ k ∣ z ↔ ∀ i, i < k → Nat.testBit z i = false := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    have h2split : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
    constructor
    · intro hdvd i hik
      obtain ⟨c, hc⟩ := hdvd
      have hz_half : z / 2 = 2 ^ k * c := by
        rw [hc, h2split, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
      have hbits_half : ∀ j, j < k → Nat.testBit (z / 2) j = false :=
        (ih (z / 2)).mp ⟨c, hz_half⟩
      rcases Nat.eq_zero_or_pos i with hi0 | hipos
      · subst hi0
        have hz_even : z % 2 = 0 := by
          have hzc : z = 2 * (2 ^ k * c) := by rw [hc, h2split, Nat.mul_assoc]
          omega
        exact Nat.mod_two_eq_zero_iff_testBit_zero.mp hz_even
      · obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        subst hj
        rw [Nat.testBit_succ]
        exact hbits_half j (by omega)
    · intro hbits
      have hz_even : z % 2 = 0 :=
        Nat.mod_two_eq_zero_iff_testBit_zero.mpr (hbits 0 (by omega))
      have hbits_half : ∀ j, j < k → Nat.testBit (z / 2) j = false := by
        intro j hjk
        rw [← Nat.testBit_succ]
        exact hbits (j + 1) (by omega)
      obtain ⟨c, hc⟩ := (ih (z / 2)).mpr hbits_half
      refine ⟨c, ?_⟩
      have hz2 : z = 2 * (z / 2) := by omega
      rw [hz2, hc, h2split, Nat.mul_assoc]

/-- `2^k` divides a bitwise-or iff it divides each operand. -/
private theorem two_pow_dvd_or (k x y : Nat) :
    2 ^ k ∣ (x ||| y) ↔ 2 ^ k ∣ x ∧ 2 ^ k ∣ y := by
  rw [two_pow_dvd_iff_testBit, two_pow_dvd_iff_testBit, two_pow_dvd_iff_testBit]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have hi' := h i hi
      rw [Nat.testBit_or] at hi'
      exact (Bool.or_eq_false_iff.mp hi').1
    · have hi' := h i hi
      rw [Nat.testBit_or] at hi'
      exact (Bool.or_eq_false_iff.mp hi').2
  · intro ⟨hx, hy⟩ i hi
    rw [Nat.testBit_or, hx i hi, hy i hi]
    rfl

/-! ## `gcd_u64` closed form -/

private theorem gcd_u64_spec (a b : u64) :
    binomial_u64.gcd_u64 a b
      = RustM.ok (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) := by
  unfold binomial_u64.gcd_u64
  have h_a_eqq : (a ==? (0 : u64) : RustM Bool) = pure (a == (0 : u64)) := rfl
  have h_b_eqq : (b ==? (0 : u64) : RustM Bool) = pure (b == (0 : u64)) := rfl
  have h_or_def : ∀ (x y : Bool),
      (x ||? y : RustM Bool) = pure (x || y) := fun _ _ => rfl
  rw [h_a_eqq, h_b_eqq]
  simp only [pure_bind, h_or_def]
  by_cases ha : a = 0
  · subst ha
    have h_dec : ((0 : u64) == (0 : u64)) = true := rfl
    rw [h_dec]
    simp only [Bool.true_or, if_true]
    show RustM.ok (0 ||| b) = RustM.ok (UInt64.ofNat (Nat.gcd 0 b.toNat))
    congr 1
    rw [Nat.gcd_zero_left]
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_ofNat_of_lt' b.toNat_lt]
    show (0 ||| b).toNat = b.toNat
    rw [UInt64.toNat_or]
    show (0 : u64).toNat ||| b.toNat = b.toNat
    show 0 ||| b.toNat = b.toNat
    exact Nat.zero_or _
  · by_cases hb : b = 0
    · subst hb
      have h_a_dec : (a == (0 : u64)) = false := beq_eq_false_iff_ne.mpr ha
      have h_b_dec : ((0 : u64) == (0 : u64)) = true := rfl
      rw [h_a_dec, h_b_dec]
      simp only [Bool.false_or, if_true]
      show RustM.ok (a ||| 0) = RustM.ok (UInt64.ofNat (Nat.gcd a.toNat 0))
      congr 1
      rw [Nat.gcd_zero_right]
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_ofNat_of_lt' a.toNat_lt]
      show (a ||| 0).toNat = a.toNat
      rw [UInt64.toNat_or]
      show a.toNat ||| (0 : u64).toNat = a.toNat
      show a.toNat ||| 0 = a.toNat
      exact Nat.or_zero _
    · have h_a_dec : (a == (0 : u64)) = false := beq_eq_false_iff_ne.mpr ha
      have h_b_dec : (b == (0 : u64)) = false := beq_eq_false_iff_ne.mpr hb
      rw [h_a_dec, h_b_dec]
      simp only [Bool.false_or, Bool.false_eq_true, if_false]
      have h_ab_or : (a ||| b).toNat = a.toNat ||| b.toNat := UInt64.toNat_or a b
      have h_ab_ne : a ||| b ≠ 0 := by
        intro hcon
        apply ha
        apply UInt64.toNat_inj.mp
        show a.toNat = (0 : u64).toNat
        have h_or0 : a.toNat ||| b.toNat = 0 := by
          have h1 : (a ||| b).toNat = 0 := by rw [hcon]; rfl
          rwa [h_ab_or] at h1
        have h_dvd : (2 : Nat) ^ 64 ∣ (a.toNat ||| b.toNat) := by
          rw [h_or0]; exact Nat.dvd_zero _
        have h_a_dvd := ((two_pow_dvd_or 64 a.toNat b.toNat).mp h_dvd).1
        have h_a0 : a.toNat = 0 := Nat.eq_zero_of_dvd_of_lt h_a_dvd (UInt64.toNat_lt a)
        rw [h_a0]; rfl
      obtain ⟨shift, h_tz_ab, hsh_lt, hsh_dvd, hsh_bit⟩ :=
        tz_nonzero_spec (a ||| b) h_ab_ne
      obtain ⟨mTz, h_tz_a, hmTz_lt, hmTz_dvd, hmTz_bit⟩ := tz_nonzero_spec a ha
      obtain ⟨nTz, h_tz_b, hnTz_lt, hnTz_dvd, hnTz_bit⟩ := tz_nonzero_spec b hb
      have h_shr_a : (a >>>? mTz : RustM u64) = RustM.ok (a >>> mTz.toNat.toUInt64) := by
        show (rust_primitives.ops.bit.Shr.shr a mTz : RustM u64)
            = RustM.ok (a >>> mTz.toNat.toUInt64)
        show (if ((0 : UInt32) ≤ mTz && mTz < (64 : UInt32)) then
                pure (a >>> mTz.toNat.toUInt64)
              else .fail .integerOverflow) = RustM.ok (a >>> mTz.toNat.toUInt64)
        have h_c : ((0 : UInt32) ≤ mTz && mTz < (64 : UInt32)) = true := by
          have h_0le : (0 : UInt32) ≤ mTz := by
            rw [UInt32.le_iff_toNat_le]; show (0 : UInt32).toNat ≤ mTz.toNat
            have h0 : (0 : UInt32).toNat = 0 := rfl
            omega
          have h_lt : mTz < (64 : UInt32) := by
            rw [UInt32.lt_iff_toNat_lt]; show mTz.toNat < (64 : UInt32).toNat
            have h64 : (64 : UInt32).toNat = 64 := rfl
            omega
          simp [h_0le, h_lt]
        rw [h_c]; rfl
      have h_shr_b : (b >>>? nTz : RustM u64) = RustM.ok (b >>> nTz.toNat.toUInt64) := by
        show (rust_primitives.ops.bit.Shr.shr b nTz : RustM u64)
            = RustM.ok (b >>> nTz.toNat.toUInt64)
        show (if ((0 : UInt32) ≤ nTz && nTz < (64 : UInt32)) then
                pure (b >>> nTz.toNat.toUInt64)
              else .fail .integerOverflow) = RustM.ok (b >>> nTz.toNat.toUInt64)
        have h_c : ((0 : UInt32) ≤ nTz && nTz < (64 : UInt32)) = true := by
          have h_0le : (0 : UInt32) ≤ nTz := by
            rw [UInt32.le_iff_toNat_le]; show (0 : UInt32).toNat ≤ nTz.toNat
            have h0 : (0 : UInt32).toNat = 0 := rfl
            omega
          have h_lt : nTz < (64 : UInt32) := by
            rw [UInt32.lt_iff_toNat_lt]; show nTz.toNat < (64 : UInt32).toNat
            have h64 : (64 : UInt32).toNat = 64 := rfl
            omega
          simp [h_0le, h_lt]
        rw [h_c]; rfl
      have hmTz_lt64 : mTz.toNat < 2 ^ 64 := by omega
      have hmTz_u : mTz.toNat.toUInt64.toNat = mTz.toNat :=
        UInt64.toNat_ofNat_of_lt' hmTz_lt64
      have hnTz_lt64 : nTz.toNat < 2 ^ 64 := by omega
      have hnTz_u : nTz.toNat.toUInt64.toNat = nTz.toNat :=
        UInt64.toNat_ofNat_of_lt' hnTz_lt64
      have h_m_toNat : (a >>> mTz.toNat.toUInt64).toNat = a.toNat / 2 ^ mTz.toNat := by
        rw [UInt64.toNat_shiftRight, hmTz_u, Nat.mod_eq_of_lt hmTz_lt,
            Nat.shiftRight_eq_div_pow]
      have h_n_toNat : (b >>> nTz.toNat.toUInt64).toNat = b.toNat / 2 ^ nTz.toNat := by
        rw [UInt64.toNat_shiftRight, hnTz_u, Nat.mod_eq_of_lt hnTz_lt,
            Nat.shiftRight_eq_div_pow]
      have h_m_odd : (a >>> mTz.toNat.toUInt64).toNat % 2 = 1 := by
        rw [← Nat.and_one_is_mod, UInt64.toNat_shiftRight, hmTz_u,
            Nat.mod_eq_of_lt hmTz_lt]
        exact hmTz_bit
      have h_n_odd : (b >>> nTz.toNat.toUInt64).toNat % 2 = 1 := by
        rw [← Nat.and_one_is_mod, UInt64.toNat_shiftRight, hnTz_u,
            Nat.mod_eq_of_lt hnTz_lt]
        exact hnTz_bit
      have h_a_eq : a.toNat = (a >>> mTz.toNat.toUInt64).toNat * 2 ^ mTz.toNat := by
        rw [h_m_toNat]; exact (Nat.div_mul_cancel hmTz_dvd).symm
      have h_b_eq : b.toNat = (b >>> nTz.toNat.toUInt64).toNat * 2 ^ nTz.toNat := by
        rw [h_n_toNat]; exact (Nat.div_mul_cancel hnTz_dvd).symm
      have hsh_a : 2 ^ shift.toNat ∣ a.toNat := by
        have h := hsh_dvd; rw [h_ab_or] at h
        exact ((two_pow_dvd_or shift.toNat a.toNat b.toNat).mp h).1
      have hsh_b : 2 ^ shift.toNat ∣ b.toNat := by
        have h := hsh_dvd; rw [h_ab_or] at h
        exact ((two_pow_dvd_or shift.toNat a.toNat b.toNat).mp h).2
      have hsh_le_mTz : shift.toNat ≤ mTz.toNat := by
        rw [h_a_eq] at hsh_a
        exact pow_two_dvd_odd_mul shift.toNat _ mTz.toNat hsh_a h_m_odd
      have hsh_le_nTz : shift.toNat ≤ nTz.toNat := by
        rw [h_b_eq] at hsh_b
        exact pow_two_dvd_odd_mul shift.toNat _ nTz.toNat hsh_b h_n_odd
      have h_shift_eq : shift.toNat = min mTz.toNat nTz.toNat := by
        rcases Nat.lt_or_ge shift.toNat (min mTz.toNat nTz.toNat) with hlt | hge
        · exfalso
          have hd_a : 2 ^ (shift.toNat + 1) ∣ a.toNat :=
            Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hmTz_dvd
          have hd_b : 2 ^ (shift.toNat + 1) ∣ b.toNat :=
            Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hnTz_dvd
          have hd_ab : 2 ^ (shift.toNat + 1) ∣ (a.toNat ||| b.toNat) :=
            (two_pow_dvd_or (shift.toNat + 1) a.toNat b.toNat).mpr ⟨hd_a, hd_b⟩
          rw [← h_ab_or] at hd_ab
          obtain ⟨c, hc⟩ := hd_ab
          have hbit0 : ((a ||| b).toNat >>> shift.toNat) &&& 1 = 0 := by
            rw [hc, Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.mul_assoc,
                Nat.mul_div_cancel_left _ (Nat.two_pow_pos shift.toNat),
                Nat.and_one_is_mod]
            exact Nat.mul_mod_right 2 c
          rw [hbit0] at hsh_bit
          exact absurd hsh_bit (by decide)
        · omega
      rw [h_tz_ab]
      simp only [RustM_ok_bind]
      rw [h_tz_a]
      simp only [RustM_ok_bind]
      rw [h_shr_a]
      simp only [RustM_ok_bind]
      rw [h_tz_b]
      simp only [RustM_ok_bind]
      rw [h_shr_b]
      simp only [RustM_ok_bind]
      rw [gcd_stein_loop_spec (a >>> mTz.toNat.toUInt64) (b >>> nTz.toNat.toUInt64)
            h_m_odd h_n_odd]
      simp only [RustM_ok_bind]
      have h_combine : Nat.gcd a.toNat b.toNat
            = 2 ^ shift.toNat * Nat.gcd (a >>> mTz.toNat.toUInt64).toNat
                (b >>> nTz.toNat.toUInt64).toNat := by
        rw [h_a_eq, h_b_eq, gcd_two_pow_combine _ _ _ _ h_m_odd h_n_odd, h_shift_eq]
      have hsh_lt64 : shift.toNat < 2 ^ 64 := by omega
      have hsh_u : shift.toNat.toUInt64.toNat = shift.toNat :=
        UInt64.toNat_ofNat_of_lt' hsh_lt64
      have h_shl : ((UInt64.ofNat (Nat.gcd (a >>> mTz.toNat.toUInt64).toNat
            (b >>> nTz.toNat.toUInt64).toNat)) <<<? shift : RustM u64)
          = RustM.ok ((UInt64.ofNat (Nat.gcd (a >>> mTz.toNat.toUInt64).toNat
              (b >>> nTz.toNat.toUInt64).toNat)) <<< shift.toNat.toUInt64) := by
        show (rust_primitives.ops.bit.Shl.shl _ shift : RustM u64) = RustM.ok _
        show (if ((0 : UInt32) ≤ shift && shift < (64 : UInt32)) then
                pure (_ <<< shift.toNat.toUInt64)
              else .fail .integerOverflow) = RustM.ok _
        have h_c : ((0 : UInt32) ≤ shift && shift < (64 : UInt32)) = true := by
          have h_0le : (0 : UInt32) ≤ shift := by
            rw [UInt32.le_iff_toNat_le]; show (0 : UInt32).toNat ≤ shift.toNat
            have h0 : (0 : UInt32).toNat = 0 := rfl
            omega
          have h_lt : shift < (64 : UInt32) := by
            rw [UInt32.lt_iff_toNat_lt]; show shift.toNat < (64 : UInt32).toNat
            have h64 : (64 : UInt32).toNat = 64 := rfl
            omega
          simp [h_0le, h_lt]
        rw [h_c]; rfl
      rw [h_shl]
      apply congrArg RustM.ok
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_ofNat_of_lt' (gcd_lt_2_64 a b), UInt64.toNat_shiftLeft,
          UInt64.toNat_ofNat_of_lt' (gcd_lt_2_64 _ _), hsh_u,
          Nat.mod_eq_of_lt (show shift.toNat < 64 by omega), Nat.shiftLeft_eq,
          Nat.mul_comm, ← h_combine]
      exact Nat.mod_eq_of_lt (gcd_lt_2_64 a b)

/-! ## `multiply_and_divide` closed form.

For `b > 0` and `b ∣ r * a` (the divisibility precondition stated in the
Rust source: "Assumes that `b` divides `r * a` evenly"), and assuming the
true result `r * a / b` fits in `u64`, the helper returns it exactly. -/

/-- Parametric version of the algebraic identity.  Treating `g` as a
    free variable avoids the recursive substitution problem when `g`
    would otherwise be `Nat.gcd r b` (rewriting `r` or `b` would
    cascade through `Nat.gcd r b`). -/
private theorem mad_value_param (r a b g : Nat) (hb : 0 < b) (hdvd : b ∣ r * a)
    (hg_pos : 0 < g) (hg_dvd_r : g ∣ r) (hg_dvd_b : g ∣ b)
    (h_coprime : Nat.Coprime (r / g) (b / g)) :
    (r / g) * (a / (b / g)) = r * a / b := by
  have h_b_eq : g * (b / g) = b := Nat.mul_div_cancel' hg_dvd_b
  have h_r_eq : g * (r / g) = r := Nat.mul_div_cancel' hg_dvd_r
  have h_bg_dvd_ra : (b / g) ∣ (r / g) * a := by
    have h1 : g * (b / g) ∣ g * ((r / g) * a) := by
      rw [h_b_eq]
      rw [show g * ((r / g) * a) = g * (r / g) * a from
            (Nat.mul_assoc _ _ _).symm]
      rw [h_r_eq]
      exact hdvd
    exact (Nat.mul_dvd_mul_iff_left hg_pos).mp h1
  have h_coprime_sym : Nat.Coprime (b / g) (r / g) := h_coprime.symm
  have h_bg_dvd_a : (b / g) ∣ a :=
    h_coprime_sym.dvd_of_dvd_mul_left h_bg_dvd_ra
  have h_a_eq : (b / g) * (a / (b / g)) = a := Nat.mul_div_cancel' h_bg_dvd_a
  -- Now multiply both sides by b and cancel.
  have h_lhs_b : (r / g) * (a / (b / g)) * b = r * a := by
    calc (r / g) * (a / (b / g)) * b
        = (r / g) * (a / (b / g)) * (g * (b / g)) := by rw [h_b_eq]
      _ = (r / g) * (a / (b / g)) * g * (b / g) := by
          rw [← Nat.mul_assoc]
      _ = (r / g) * ((a / (b / g)) * g) * (b / g) := by
          rw [Nat.mul_assoc (r / g) (a / (b / g)) g]
      _ = (r / g) * (g * (a / (b / g))) * (b / g) := by
          rw [Nat.mul_comm (a / (b / g)) g]
      _ = (r / g) * g * (a / (b / g)) * (b / g) := by
          rw [← Nat.mul_assoc (r / g) g (a / (b / g))]
      _ = g * (r / g) * (a / (b / g)) * (b / g) := by
          rw [Nat.mul_comm (r / g) g]
      _ = g * (r / g) * ((a / (b / g)) * (b / g)) := by
          rw [Nat.mul_assoc (g * (r / g)) (a / (b / g)) (b / g)]
      _ = g * (r / g) * ((b / g) * (a / (b / g))) := by
          rw [Nat.mul_comm (a / (b / g)) (b / g)]
      _ = r * ((b / g) * (a / (b / g))) := by rw [h_r_eq]
      _ = r * a := by rw [h_a_eq]
  have h_rhs_b : (r * a / b) * b = r * a := Nat.div_mul_cancel hdvd
  exact Nat.eq_of_mul_eq_mul_right hb (h_lhs_b.trans h_rhs_b.symm)

/-- Algebraic identity behind `multiply_and_divide`. -/
private theorem mad_value (r a b : Nat) (hb : 0 < b) (hdvd : b ∣ r * a) :
    (r / Nat.gcd r b) * (a / (b / Nat.gcd r b)) = r * a / b := by
  have hg_pos : 0 < Nat.gcd r b := Nat.gcd_pos_of_pos_right r hb
  exact mad_value_param r a b (Nat.gcd r b) hb hdvd hg_pos
    (Nat.gcd_dvd_left r b) (Nat.gcd_dvd_right r b)
    (Nat.coprime_div_gcd_div_gcd hg_pos)

/-- `multiply_and_divide` returns `r * a / b` under the divisibility +
    no-overflow preconditions. -/
private theorem multiply_and_divide_spec (r a b : u64)
    (hb_pos : 0 < b.toNat)
    (hdvd : b.toNat ∣ r.toNat * a.toNat)
    (h_result_lt : r.toNat * a.toNat / b.toNat < 2 ^ 64) :
    binomial_u64.multiply_and_divide r a b
      = RustM.ok (UInt64.ofNat (r.toNat * a.toNat / b.toNat)) := by
  unfold binomial_u64.multiply_and_divide
  rw [gcd_u64_spec r b]
  simp only [RustM_ok_bind]
  -- Let g denote the u64 form of the gcd. We avoid `set` (not available).
  have hg_natpos : 0 < Nat.gcd r.toNat b.toNat :=
    Nat.gcd_pos_of_pos_right r.toNat hb_pos
  have hg_natlt : Nat.gcd r.toNat b.toNat < 2 ^ 64 := gcd_lt_2_64 r b
  have hg_toNat : (UInt64.ofNat (Nat.gcd r.toNat b.toNat)).toNat =
                  Nat.gcd r.toNat b.toNat :=
    UInt64.toNat_ofNat_of_lt' hg_natlt
  have hg_pos : 0 < (UInt64.ofNat (Nat.gcd r.toNat b.toNat)).toNat := by
    rw [hg_toNat]; exact hg_natpos
  have hg_ne : UInt64.ofNat (Nat.gcd r.toNat b.toNat) ≠ 0 := by
    intro h
    have : (UInt64.ofNat (Nat.gcd r.toNat b.toNat)).toNat = 0 := by rw [h]; rfl
    omega
  -- Use a `let` for readability.
  -- r /? g = pure (r / g)
  have h_r_div : (r /? UInt64.ofNat (Nat.gcd r.toNat b.toNat) : RustM u64) =
                 pure (r / UInt64.ofNat (Nat.gcd r.toNat b.toNat)) := by
    show (rust_primitives.ops.arith.Div.div r (UInt64.ofNat (Nat.gcd r.toNat b.toNat))
              : RustM u64) = _
    show (if UInt64.ofNat (Nat.gcd r.toNat b.toNat) = 0 then
            (.fail .divisionByZero : RustM u64)
          else pure (r / UInt64.ofNat (Nat.gcd r.toNat b.toNat))) = _
    rw [if_neg hg_ne]
  rw [h_r_div]
  simp only [pure_bind]
  -- b /? g = pure (b / g)
  have h_b_div : (b /? UInt64.ofNat (Nat.gcd r.toNat b.toNat) : RustM u64) =
                 pure (b / UInt64.ofNat (Nat.gcd r.toNat b.toNat)) := by
    show (rust_primitives.ops.arith.Div.div b (UInt64.ofNat (Nat.gcd r.toNat b.toNat))
              : RustM u64) = _
    show (if UInt64.ofNat (Nat.gcd r.toNat b.toNat) = 0 then
            (.fail .divisionByZero : RustM u64)
          else pure (b / UInt64.ofNat (Nat.gcd r.toNat b.toNat))) = _
    rw [if_neg hg_ne]
  rw [h_b_div]
  simp only [pure_bind]
  -- toNat of the quotients.
  have h_g_dvd_b : (UInt64.ofNat (Nat.gcd r.toNat b.toNat)).toNat ∣ b.toNat := by
    rw [hg_toNat]; exact Nat.gcd_dvd_right _ _
  have h_g_dvd_r : (UInt64.ofNat (Nat.gcd r.toNat b.toNat)).toNat ∣ r.toNat := by
    rw [hg_toNat]; exact Nat.gcd_dvd_left _ _
  have h_bg_toNat : (b / UInt64.ofNat (Nat.gcd r.toNat b.toNat)).toNat =
                    b.toNat / (UInt64.ofNat (Nat.gcd r.toNat b.toNat)).toNat :=
    UInt64.toNat_div _ _
  have h_rg_toNat : (r / UInt64.ofNat (Nat.gcd r.toNat b.toNat)).toNat =
                    r.toNat / (UInt64.ofNat (Nat.gcd r.toNat b.toNat)).toNat :=
    UInt64.toNat_div _ _
  -- (b/g) > 0
  have h_bg_natpos : 0 < b.toNat / (UInt64.ofNat (Nat.gcd r.toNat b.toNat)).toNat :=
    Nat.div_pos (Nat.le_of_dvd hb_pos h_g_dvd_b) hg_pos
  have h_bg_pos : 0 < (b / UInt64.ofNat (Nat.gcd r.toNat b.toNat)).toNat := by
    rw [h_bg_toNat]; exact h_bg_natpos
  have h_bg_ne : (b / UInt64.ofNat (Nat.gcd r.toNat b.toNat)) ≠ 0 := by
    intro h
    have : (b / UInt64.ofNat (Nat.gcd r.toNat b.toNat)).toNat = 0 := by rw [h]; rfl
    omega
  -- a /? (b/g) = pure (a / (b/g))
  have h_a_div : (a /? (b / UInt64.ofNat (Nat.gcd r.toNat b.toNat)) : RustM u64) =
                 pure (a / (b / UInt64.ofNat (Nat.gcd r.toNat b.toNat))) := by
    show (rust_primitives.ops.arith.Div.div a
              (b / UInt64.ofNat (Nat.gcd r.toNat b.toNat)) : RustM u64) = _
    show (if (b / UInt64.ofNat (Nat.gcd r.toNat b.toNat)) = 0 then
            (.fail .divisionByZero : RustM u64)
          else pure (a / (b / UInt64.ofNat (Nat.gcd r.toNat b.toNat)))) = _
    rw [if_neg h_bg_ne]
  rw [h_a_div]
  simp only [pure_bind]
  -- Now the final multiplication
  have h_abg_toNat :
      (a / (b / UInt64.ofNat (Nat.gcd r.toNat b.toNat))).toNat =
      a.toNat / (b.toNat / (UInt64.ofNat (Nat.gcd r.toNat b.toNat)).toNat) := by
    rw [UInt64.toNat_div, h_bg_toNat]
  -- Nat-level value identity
  have h_value :
      (r / UInt64.ofNat (Nat.gcd r.toNat b.toNat)).toNat *
      (a / (b / UInt64.ofNat (Nat.gcd r.toNat b.toNat))).toNat =
      r.toNat * a.toNat / b.toNat := by
    rw [h_rg_toNat, h_abg_toNat, hg_toNat]
    exact mad_value r.toNat a.toNat b.toNat hb_pos hdvd
  -- No overflow on the multiplication.
  have h_no_overflow :
      BitVec.umulOverflow (r / UInt64.ofNat (Nat.gcd r.toNat b.toNat)).toBitVec
                          (a / (b / UInt64.ofNat (Nat.gcd r.toNat b.toNat))).toBitVec
        = false := by
    have : ¬ UInt64.mulOverflow (r / UInt64.ofNat (Nat.gcd r.toNat b.toNat))
                                (a / (b / UInt64.ofNat (Nat.gcd r.toNat b.toNat))) := by
      rw [UInt64.mulOverflow_iff, h_value]
      omega
    simpa [UInt64.mulOverflow] using this
  show (rust_primitives.ops.arith.Mul.mul
          (r / UInt64.ofNat (Nat.gcd r.toNat b.toNat))
          (a / (b / UInt64.ofNat (Nat.gcd r.toNat b.toNat))) : RustM u64)
        = RustM.ok (UInt64.ofNat (r.toNat * a.toNat / b.toNat))
  simp only [rust_primitives.ops.arith.Mul.mul, h_no_overflow,
    Bool.false_eq_true, ↓reduceIte]
  apply congrArg RustM.ok
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_mul, h_value, UInt64.toNat_ofNat_of_lt' h_result_lt]
  exact Nat.mod_eq_of_lt h_result_lt

/-! ## Multiplicative step identity for `nchoose`.

`(j + 1) * C(n, j + 1) = C(n, j) * (n - j)` — the rearrangement of
Pascal's recurrence that lets `multiply_and_divide` carry the binomial-loop
invariant `r_i = C(n_init, i - 1)` forward. -/

private theorem nchoose_step :
    ∀ n j, (j + 1) * nchoose n (j + 1) = nchoose n j * (n - j)
  | 0, 0 => by
    show (1 : Nat) * nchoose 0 1 = nchoose 0 0 * (0 - 0)
    show (1 : Nat) * 0 = 1 * 0
    rfl
  | 0, j + 1 => by
    show (j + 2) * nchoose 0 (j + 2) = nchoose 0 (j + 1) * (0 - (j + 1))
    -- nchoose 0 (j + 2) = 0 and nchoose 0 (j + 1) = 0 by definition's second case.
    have h1 : nchoose 0 (j + 2) = 0 := rfl
    have h2 : nchoose 0 (j + 1) = 0 := rfl
    rw [h1, h2]
    simp
  | n + 1, 0 => by
    show (1 : Nat) * nchoose (n + 1) 1 = nchoose (n + 1) 0 * (n + 1 - 0)
    -- nchoose (n+1) 1 = nchoose n 0 + nchoose n 1, nchoose (n+1) 0 = 1
    show (1 : Nat) * (nchoose n 0 + nchoose n 1) =
         nchoose (n + 1) 0 * (n + 1 - 0)
    have h_nch_n_0 : nchoose n 0 = 1 := by cases n <;> rfl
    have h_nch_n1_0 : nchoose (n + 1) 0 = 1 := rfl
    rw [h_nch_n_0, h_nch_n1_0, Nat.sub_zero, Nat.one_mul, Nat.one_mul]
    -- Goal: 1 + nchoose n 1 = n + 1
    -- ih (with literal `1` form): nchoose n 1 = n.
    have ih : nchoose n 1 = n := by
      have := nchoose_step n 0
      -- this : (0 + 1) * nchoose n (0 + 1) = nchoose n 0 * (n - 0)
      simp [h_nch_n_0] at this
      exact this
    omega
  | n + 1, j + 1 => by
    show (j + 2) * nchoose (n + 1) (j + 2) =
         nchoose (n + 1) (j + 1) * (n + 1 - (j + 1))
    show (j + 2) * (nchoose n (j + 1) + nchoose n (j + 2)) =
         (nchoose n j + nchoose n (j + 1)) * (n + 1 - (j + 1))
    have hsub : n + 1 - (j + 1) = n - j := by omega
    rw [hsub]
    by_cases hjn : j < n
    · -- Standard case: j < n.
      have ihj := nchoose_step n j
      have ihjp1 := nchoose_step n (j + 1)
      -- ihj   : (j + 1) * nchoose n (j + 1) = nchoose n j * (n - j)
      -- ihjp1 : (j + 1 + 1) * nchoose n (j + 1 + 1) = nchoose n (j + 1) * (n - (j + 1))
      -- Distribute the RHS only via a targeted helper.
      have h_rhs : (nchoose n j + nchoose n (j + 1)) * (n - j) =
                   nchoose n j * (n - j) + nchoose n (j + 1) * (n - j) :=
        Nat.add_mul _ _ _
      rw [h_rhs]
      -- Goal: (j+2) * (nchoose n (j+1) + nchoose n (j+2)) =
      --       nchoose n j * (n-j) + nchoose n (j+1) * (n-j)
      -- Distribute the LHS via mul_add.
      rw [Nat.mul_add]
      -- Goal: (j+2) * nchoose n (j+1) + (j+2) * nchoose n (j+2) = R*(n-j) + P*(n-j)
      -- Replace (j+2) * nchoose n (j+2) using ihjp1 (with j+2 = j+1+1).
      have h_jp2_eq : (j + 2 : Nat) * nchoose n (j + 2) =
                       nchoose n (j + 1) * (n - (j + 1)) := ihjp1
      rw [h_jp2_eq]
      -- Goal: (j+2) * P + P*(n-(j+1)) = R*(n-j) + P*(n-j) where P = nchoose n (j+1).
      -- Split (j+2)*P = (j+1)*P + P.
      have h1 : (j + 2 : Nat) * nchoose n (j + 1) =
                (j + 1) * nchoose n (j + 1) + nchoose n (j + 1) := by
        rw [show (j + 2 : Nat) = (j + 1) + 1 from rfl, Nat.add_mul, Nat.one_mul]
      rw [h1, ihj]
      -- Goal: R*(n-j) + P + P*(n-(j+1)) = R*(n-j) + P*(n-j)
      rw [Nat.add_assoc]
      congr 1
      -- Goal: P + P*(n-(j+1)) = P*(n-j)
      have h_n_jm1 : n - j = n - (j + 1) + 1 := by omega
      rw [h_n_jm1, Nat.mul_add, Nat.mul_one]
      -- Goal: P + P * (n - (j+1)) = P * (n - (j+1)) + P
      exact Nat.add_comm _ _
    · -- j ≥ n: both sides become 0 since the relevant nchoose values vanish.
      have hjn' : n ≤ j := by omega
      have h_n_j : n - j = 0 := by omega
      have h1 : nchoose n (j + 1) = 0 :=
        nchoose_eq_zero_of_lt n (j + 1) (by omega)
      have h2 : nchoose n (j + 2) = 0 :=
        nchoose_eq_zero_of_lt n (j + 2) (by omega)
      rw [h_n_j, Nat.mul_zero, h1, h2]
      simp

/-! ## `binomial_loop` closed form.

The loop accumulates the running product `r = C(n_init, d - 1)`. The
state invariant is `n = n_init - (d - 1) ∧ r = C(n_init, d - 1)`. Strong
induction on the measure `k.toNat + 1 - d.toNat`. -/

/-- The "n component is bounded" fact: through the loop, `n.toNat = n_init.toNat + 1 - d.toNat`,
    so `n.toNat ≤ n_init.toNat ≤ 67`. -/
private theorem binomial_loop_spec (n_init k : u64) :
    ∀ (n d r : u64),
      n_init.toNat ≤ 67 →
      k.toNat ≤ n_init.toNat - k.toNat →
      1 ≤ d.toNat →
      d.toNat ≤ k.toNat + 1 →
      n.toNat + d.toNat = n_init.toNat + 1 →
      r.toNat = nchoose n_init.toNat (d.toNat - 1) →
      binomial_u64.binomial_loop n k d r
        = RustM.ok (UInt64.ofNat (nchoose n_init.toNat k.toNat)) := by
  intro n d r hn_init hk_half hd_pos hd_bound hn_eq hr_eq
  induction hkd : (k.toNat + 1 - d.toNat) using Nat.strongRecOn generalizing n d r with
  | _ K ih =>
    unfold binomial_u64.binomial_loop
    have h_gt_eqq : (d >? k : RustM Bool) = pure (decide (d > k)) := rfl
    rw [h_gt_eqq]
    simp only [pure_bind]
    by_cases hdk : d > k
    · -- termination branch
      rw [decide_eq_true hdk]
      simp only [if_true]
      have hdk_nat : k.toNat < d.toNat := UInt64.lt_iff_toNat_lt.mp hdk
      -- d ≤ k + 1 ∧ d > k ⟹ d.toNat = k.toNat + 1
      have hd_eq : d.toNat = k.toNat + 1 := by omega
      show RustM.ok r = RustM.ok (UInt64.ofNat (nchoose n_init.toNat k.toNat))
      congr 1
      apply UInt64.toNat_inj.mp
      have hk_lt_2_64 : nchoose n_init.toNat k.toNat < 2 ^ 64 :=
        nchoose_lt_2_64 _ _ hn_init
      rw [UInt64.toNat_ofNat_of_lt' hk_lt_2_64, hr_eq, hd_eq]
      -- After hd_eq subs, goal is nchoose n_init.toNat (k.toNat + 1 - 1) = nchoose ... k.toNat.
      -- (k + 1 - 1) reduces def to k.
      rfl
    · -- recursive branch
      rw [decide_eq_false hdk]
      simp only [Bool.false_eq_true, if_false]
      have hdk_nat : d.toNat ≤ k.toNat := by
        rcases Nat.lt_or_ge k.toNat d.toNat with h | h
        · exfalso; apply hdk; exact UInt64.lt_iff_toNat_lt.mpr h
        · exact h
      -- Compute the body step.
      -- First: n -? 1 = pure (n - 1).
      -- n.toNat = n_init.toNat + 1 - d.toNat. Since d ≤ k ≤ n_init - k ≤ n_init,
      -- n.toNat = n_init + 1 - d ≥ 1.
      have hn_pos : 1 ≤ n.toNat := by omega
      have h_n_sub : (n -? (1 : u64) : RustM u64) = pure (n - 1) := by
        show (rust_primitives.ops.arith.Sub.sub n (1 : u64) : RustM u64) = pure (n - 1)
        show (if BitVec.usubOverflow n.toBitVec (1 : u64).toBitVec then
                (.fail .integerOverflow : RustM u64) else pure (n - 1)) = pure (n - 1)
        have h_no_uf : BitVec.usubOverflow n.toBitVec (1 : u64).toBitVec = false := by
          cases h_eq : BitVec.usubOverflow n.toBitVec (1 : u64).toBitVec with
          | false => rfl
          | true =>
            exfalso
            have : UInt64.subOverflow n (1 : u64) = true := h_eq
            rw [UInt64.subOverflow_iff] at this
            have h1 : (1 : u64).toNat = 1 := rfl
            omega
        rw [h_no_uf]; rfl
      rw [h_n_sub]
      simp only [pure_bind]
      -- Second: d +? 1 = pure (d + 1).
      have hd_lt : d.toNat + 1 < 2 ^ 64 := by
        have hk_lt : k.toNat < 2 ^ 64 := UInt64.toNat_lt k
        omega
      have h_d_add : (d +? (1 : u64) : RustM u64) = pure (d + 1) := by
        show (rust_primitives.ops.arith.Add.add d (1 : u64) : RustM u64) = pure (d + 1)
        show (if BitVec.uaddOverflow d.toBitVec (1 : u64).toBitVec then
                (.fail .integerOverflow : RustM u64) else pure (d + 1)) = pure (d + 1)
        have h_no_ovf : BitVec.uaddOverflow d.toBitVec (1 : u64).toBitVec = false := by
          cases h_eq : BitVec.uaddOverflow d.toBitVec (1 : u64).toBitVec with
          | false => rfl
          | true =>
            exfalso
            have : UInt64.addOverflow d (1 : u64) = true := h_eq
            rw [UInt64.addOverflow_iff] at this
            have h1 : (1 : u64).toNat = 1 := rfl
            omega
        rw [h_no_ovf]; rfl
      rw [h_d_add]
      simp only [pure_bind]
      -- Third: multiply_and_divide r n d = ok (ofNat (nchoose n_init.toNat d.toNat)).
      -- Apply multiply_and_divide_spec.
      -- Preconditions: 0 < d.toNat, d.toNat ∣ r.toNat * n.toNat, r.toNat * n.toNat / d.toNat < 2^64.
      have hd_natpos : 0 < d.toNat := hd_pos
      -- d ∣ r * n: by nchoose_step, r * n = nchoose n_init (d-1) * (n_init - (d-1)) = d * nchoose n_init d.
      -- (Note: d - 1 + 1 = d, and n_init - (d - 1) = n.toNat by hn_eq.)
      have h_dvd : d.toNat ∣ r.toNat * n.toNat := by
        rw [hr_eq]
        -- Goal: d.toNat ∣ nchoose n_init.toNat (d.toNat - 1) * n.toNat
        -- By nchoose_step (n_init, d-1): d * nchoose n_init d = nchoose n_init (d - 1) * (n_init - (d - 1))
        -- So nchoose n_init (d-1) * (n_init - (d-1)) = d * nchoose n_init d.
        -- And n.toNat = n_init + 1 - d = n_init - (d - 1).
        have h_n_eq : n.toNat = n_init.toNat - (d.toNat - 1) := by omega
        rw [h_n_eq]
        have step := nchoose_step n_init.toNat (d.toNat - 1)
        -- step : (d.toNat - 1 + 1) * nchoose n_init.toNat (d.toNat - 1 + 1) =
        --        nchoose n_init.toNat (d.toNat - 1) * (n_init.toNat - (d.toNat - 1))
        have h_d_succ : d.toNat - 1 + 1 = d.toNat := by omega
        rw [h_d_succ] at step
        -- step : d.toNat * nchoose n_init.toNat d.toNat =
        --        nchoose n_init.toNat (d.toNat - 1) * (n_init.toNat - (d.toNat - 1))
        rw [← step]
        exact ⟨nchoose n_init.toNat d.toNat, rfl⟩
      have h_value_lt : r.toNat * n.toNat / d.toNat < 2 ^ 64 := by
        rw [hr_eq]
        have h_n_eq : n.toNat = n_init.toNat - (d.toNat - 1) := by omega
        rw [h_n_eq]
        have step := nchoose_step n_init.toNat (d.toNat - 1)
        have h_d_succ : d.toNat - 1 + 1 = d.toNat := by omega
        rw [h_d_succ] at step
        -- nchoose n_init (d-1) * (n_init - (d-1)) = d * nchoose n_init d.
        rw [← step]
        -- d.toNat * nchoose n_init.toNat d.toNat / d.toNat = nchoose n_init.toNat d.toNat
        rw [Nat.mul_div_cancel_left _ hd_natpos]
        exact nchoose_lt_2_64 _ _ hn_init
      rw [multiply_and_divide_spec r n d hd_natpos h_dvd h_value_lt]
      simp only [RustM_ok_bind]
      -- After multiply_and_divide_spec, the recursive call has 
      -- (UInt64.ofNat (r.toNat * n.toNat / d.toNat)) as the new r argument.
      -- We need to bridge this to (UInt64.ofNat (nchoose n_init.toNat d.toNat)).
      have h_mad_value_eq :
          r.toNat * n.toNat / d.toNat = nchoose n_init.toNat d.toNat := by
        rw [hr_eq]
        have h_n_eq : n.toNat = n_init.toNat - (d.toNat - 1) := by omega
        rw [h_n_eq]
        have step := nchoose_step n_init.toNat (d.toNat - 1)
        have h_d_succ : d.toNat - 1 + 1 = d.toNat := by omega
        rw [h_d_succ] at step
        rw [← step]
        rw [Nat.mul_div_cancel_left _ hd_natpos]
      rw [h_mad_value_eq]
      -- Now goal: binomial_loop (n - 1) k (d + 1) (UInt64.ofNat (nchoose n_init.toNat d.toNat))
      -- Apply IH with measure (k - (d+1) + 1) < (k - d + 1).
      have h_nm1_toNat : (n - 1).toNat = n.toNat - 1 := by
        apply UInt64.toNat_sub_of_le'
        show (1 : u64).toNat ≤ n.toNat
        have h1 : (1 : u64).toNat = 1 := rfl
        omega
      have h_dp1_toNat : (d + 1).toNat = d.toNat + 1 := by
        apply UInt64.toNat_add_of_lt
        show d.toNat + (1 : u64).toNat < 2 ^ 64
        have h1 : (1 : u64).toNat = 1 := rfl
        omega
      have h_v_lt : nchoose n_init.toNat d.toNat < 2 ^ 64 :=
        nchoose_lt_2_64 _ _ hn_init
      have h_v_toNat : (UInt64.ofNat (nchoose n_init.toNat d.toNat)).toNat =
                       nchoose n_init.toNat d.toNat :=
        UInt64.toNat_ofNat_of_lt' h_v_lt
      have h_new_meas : k.toNat + 1 - (d + 1).toNat < K := by
        rw [h_dp1_toNat]
        omega
      have h_new_hd_pos : 1 ≤ (d + 1).toNat := by rw [h_dp1_toNat]; omega
      have h_new_hd_bound : (d + 1).toNat ≤ k.toNat + 1 := by rw [h_dp1_toNat]; omega
      have h_new_hn_eq : (n - 1).toNat + (d + 1).toNat = n_init.toNat + 1 := by
        rw [h_nm1_toNat, h_dp1_toNat]; omega
      have h_new_hr_eq :
          (UInt64.ofNat (nchoose n_init.toNat d.toNat)).toNat =
          nchoose n_init.toNat ((d + 1).toNat - 1) := by
        rw [h_v_toNat, h_dp1_toNat]
        -- nchoose n_init.toNat d.toNat = nchoose n_init.toNat (d.toNat + 1 - 1).
        -- (d.toNat + 1 - 1) reduces to d.toNat definitionally.
        rfl
      exact ih (k.toNat + 1 - (d + 1).toNat) h_new_meas
        (n - 1) (d + 1) (UInt64.ofNat (nchoose n_init.toNat d.toNat))
        h_new_hd_pos h_new_hd_bound h_new_hn_eq h_new_hr_eq rfl

/-! ## Master closed-form postcondition.

Within the overflow-free range (`n ≤ 67`), the extracted `binomial` reduces to
the mathematical binomial coefficient on the `toNat` projection.

Proof:  case-split on the three branches of the function.
  - `k > n`:  returns `0` and `nchoose n k = 0` by `nchoose_eq_zero_of_lt`.
  - `k > n - k`:  recurses to `binomial n (n - k)`.  After one more unfold,
    the function goes to the else-branch and calls `binomial_loop n (n-k) 1 1`,
    which closes by `binomial_loop_spec` + `nchoose_symm`.
  - else:  direct call to `binomial_loop n k 1 1`, closes by `binomial_loop_spec`.

The middle case is the only one that requires unfolding `binomial` twice, but
the recursive call is structurally determined (we never recurse a second
time), so we can hand-unfold without using strong induction. -/

/-- The "else-branch" computation: at the point where we know `k ≤ n - k`,
    the function is exactly `binomial_loop n k 1 1`, which closes by
    `binomial_loop_spec`. -/
private theorem binomial_else_branch (n k : u64) (hn : n.toNat ≤ 67)
    (hk_le_half : k.toNat ≤ n.toNat - k.toNat) :
    binomial_u64.binomial_loop n k 1 1 =
      RustM.ok (UInt64.ofNat (nchoose n.toNat k.toNat)) := by
  apply binomial_loop_spec n k n 1 1 hn hk_le_half
  · show 1 ≤ (1 : u64).toNat
    decide
  · show (1 : u64).toNat ≤ k.toNat + 1
    have h1 : (1 : u64).toNat = 1 := rfl
    omega
  · show n.toNat + (1 : u64).toNat = n.toNat + 1
    rfl
  · show (1 : u64).toNat = nchoose n.toNat ((1 : u64).toNat - 1)
    have h1 : (1 : u64).toNat = 1 := rfl
    rw [h1]
    show 1 = nchoose n.toNat 0
    cases n.toNat <;> rfl

theorem binomial_postcondition (n k : u64) (hn : n.toNat ≤ 67) :
    binomial_u64.binomial n k = RustM.ok (UInt64.ofNat (nchoose n.toNat k.toNat)) := by
  unfold binomial_u64.binomial
  have h_gt_eqq : (k >? n : RustM Bool) = pure (decide (k > n)) := rfl
  rw [h_gt_eqq]
  simp only [pure_bind]
  by_cases hkn : k > n
  · -- Case A: k > n. Function returns 0.
    rw [decide_eq_true hkn]
    simp only [if_true]
    have hkn_nat : n.toNat < k.toNat := UInt64.lt_iff_toNat_lt.mp hkn
    show RustM.ok (0 : u64) = RustM.ok (UInt64.ofNat (nchoose n.toNat k.toNat))
    congr 1
    have h_zero : nchoose n.toNat k.toNat = 0 := nchoose_eq_zero_of_lt _ _ hkn_nat
    rw [h_zero]
    rfl
  · -- k ≤ n.
    rw [decide_eq_false hkn]
    simp only [Bool.false_eq_true, if_false]
    have hk_le_n : k.toNat ≤ n.toNat := by
      rcases Nat.lt_or_ge n.toNat k.toNat with h | h
      · exfalso; apply hkn; exact UInt64.lt_iff_toNat_lt.mpr h
      · exact h
    -- Compute n -? k = pure (n - k).
    have h_n_sub : (n -? k : RustM u64) = pure (n - k) := by
      show (rust_primitives.ops.arith.Sub.sub n k : RustM u64) = pure (n - k)
      show (if BitVec.usubOverflow n.toBitVec k.toBitVec then
              (.fail .integerOverflow : RustM u64) else pure (n - k)) = pure (n - k)
      have h_no_uf : BitVec.usubOverflow n.toBitVec k.toBitVec = false := by
        cases h_eq : BitVec.usubOverflow n.toBitVec k.toBitVec with
        | false => rfl
        | true =>
          exfalso
          have : UInt64.subOverflow n k = true := h_eq
          rw [UInt64.subOverflow_iff] at this
          omega
      rw [h_no_uf]; rfl
    rw [h_n_sub]
    simp only [pure_bind]
    have h_n_sub_toNat : (n - k).toNat = n.toNat - k.toNat :=
      UInt64.toNat_sub_of_le' hk_le_n
    have h_gt2 : (k >? (n - k) : RustM Bool) = pure (decide (k > n - k)) := rfl
    rw [h_gt2]
    simp only [pure_bind]
    by_cases hk_gt_nk : k > n - k
    · -- Case B: k > n - k. Recurse to `binomial n (n - k)`.
      rw [decide_eq_true hk_gt_nk]
      simp only [if_true]
      have hk_gt_nk_nat : (n - k).toNat < k.toNat :=
        UInt64.lt_iff_toNat_lt.mp hk_gt_nk
      rw [h_n_sub_toNat] at hk_gt_nk_nat
      -- After the symmetry redirect, we need to evaluate `binomial n (n - k)`
      -- and show it equals ok (UInt64.ofNat (nchoose n.toNat k.toNat)).
      -- Unfold binomial once more for the recursive call.
      unfold binomial_u64.binomial
      have h_gt_eqq' : ((n - k) >? n : RustM Bool) = pure (decide ((n - k) > n)) := rfl
      rw [h_gt_eqq']
      simp only [pure_bind]
      -- (n - k) ≤ n, so (n - k) > n is false.
      have h_nk_le_n : (n - k).toNat ≤ n.toNat := by
        rw [h_n_sub_toNat]; omega
      have h_nk_not_gt_n : ¬ ((n - k) > n) := by
        intro h
        have : n.toNat < (n - k).toNat := UInt64.lt_iff_toNat_lt.mp h
        omega
      rw [decide_eq_false h_nk_not_gt_n]
      simp only [Bool.false_eq_true, if_false]
      -- Compute n -? (n - k) = pure (n - (n - k)).
      have h_n_sub_nk : (n -? (n - k) : RustM u64) = pure (n - (n - k)) := by
        show (rust_primitives.ops.arith.Sub.sub n (n - k) : RustM u64) =
              pure (n - (n - k))
        show (if BitVec.usubOverflow n.toBitVec (n - k).toBitVec then
                (.fail .integerOverflow : RustM u64) else pure (n - (n - k))) =
              pure (n - (n - k))
        have h_no_uf : BitVec.usubOverflow n.toBitVec (n - k).toBitVec = false := by
          cases h_eq : BitVec.usubOverflow n.toBitVec (n - k).toBitVec with
          | false => rfl
          | true =>
            exfalso
            have : UInt64.subOverflow n (n - k) = true := h_eq
            rw [UInt64.subOverflow_iff] at this
            omega
        rw [h_no_uf]; rfl
      rw [h_n_sub_nk]
      simp only [pure_bind]
      -- (n - k) > n - (n - k) = k.  Since k > n - k, we have n - k < k = n - (n - k),
      -- so (n - k) > k is false.
      have h_nk_sub : (n - (n - k)).toNat = k.toNat := by
        have h_nk_le_n_u : (n - k) ≤ n := by
          rw [UInt64.le_iff_toNat_le]
          rw [h_n_sub_toNat]; omega
        rw [UInt64.toNat_sub_of_le' h_nk_le_n_u]
        rw [h_n_sub_toNat]; omega
      have h_nk_not_gt_k : ¬ ((n - k) > (n - (n - k))) := by
        intro h
        have : (n - (n - k)).toNat < (n - k).toNat := UInt64.lt_iff_toNat_lt.mp h
        rw [h_nk_sub, h_n_sub_toNat] at this
        omega
      have h_gt_eqq'' :
          ((n - k) >? (n - (n - k)) : RustM Bool) =
          pure (decide ((n - k) > (n - (n - k)))) := rfl
      rw [h_gt_eqq'']
      simp only [pure_bind]
      rw [decide_eq_false h_nk_not_gt_k]
      simp only [Bool.false_eq_true, if_false]
      -- Now: binomial_loop n (n - k) 1 1
      have h_nk_le_half : (n - k).toNat ≤ n.toNat - (n - k).toNat := by
        rw [h_n_sub_toNat]; omega
      rw [binomial_else_branch n (n - k) hn h_nk_le_half]
      -- Goal: ok (ofNat (nchoose n.toNat (n - k).toNat)) = ok (ofNat (nchoose n.toNat k.toNat))
      congr 2
      rw [h_n_sub_toNat]
      exact (nchoose_symm n.toNat k.toNat hk_le_n).symm
    · -- Case C: k ≤ n - k.  Direct call to binomial_loop n k 1 1.
      rw [decide_eq_false hk_gt_nk]
      simp only [Bool.false_eq_true, if_false]
      have hk_le_nk_nat : k.toNat ≤ (n - k).toNat := by
        rcases Nat.lt_or_ge (n - k).toNat k.toNat with h | h
        · exfalso; apply hk_gt_nk; exact UInt64.lt_iff_toNat_lt.mpr h
        · exact h
      rw [h_n_sub_toNat] at hk_le_nk_nat
      exact binomial_else_branch n k hn hk_le_nk_nat

/-! ## Contract clauses derived from / parallel to the master postcondition. -/

/-- Totality / no-panic in the overflow-free range. The Rust source has no
    explicit `panic!`; failure modes (integer overflow on `*`, `+`, `-`;
    division by zero on `/`) are confined to the inner partial operators
    inside `multiply_and_divide`. For `n ≤ 67` the closed form rules them
    all out. -/
theorem binomial_total (n k : u64) (hn : n.toNat ≤ 67) :
    ∃ v : u64, binomial_u64.binomial n k = RustM.ok v :=
  ⟨_, binomial_postcondition n k hn⟩

/-- `k > n` branch: when `k` exceeds `n`, the result is `0`. Captures the
    property test `k_greater_than_n_is_zero`. Unconditional in `n` (the
    early-return branch never invokes the loop, so no overflow concerns). -/
theorem binomial_k_gt_n (n k : u64) (hkn : n.toNat < k.toNat) :
    binomial_u64.binomial n k = RustM.ok 0 := by
  unfold binomial_u64.binomial
  have h_gt_eqq : (k >? n : RustM Bool) = pure (decide (k > n)) := rfl
  rw [h_gt_eqq]
  simp only [pure_bind]
  have h_dec : (decide (k > n)) = true :=
    decide_eq_true (UInt64.lt_iff_toNat_lt.mpr hkn)
  rw [h_dec]
  simp only [if_true]
  rfl

/-- Boundary `C(n, 0) = 1`. Captures the `k = 0` half of the property test
    `boundary_k_zero_and_k_eq_n`. Unconditional in `n`: the loop terminates
    immediately (`d = 1 > k = 0`) without invoking `multiply_and_divide`. -/
theorem binomial_k_zero (n : u64) :
    binomial_u64.binomial n 0 = RustM.ok 1 := by
  unfold binomial_u64.binomial
  -- (0 >? n) = pure (decide (0 > n)) = pure false (since (0:u64) > n is always false)
  have h_gt1 : ((0 : u64) >? n : RustM Bool) = pure (decide ((0 : u64) > n)) := rfl
  rw [h_gt1]
  simp only [pure_bind]
  have h_dec1 : (decide ((0 : u64) > n)) = false := by
    apply decide_eq_false
    show ¬ n < (0 : u64)
    rw [UInt64.lt_iff_toNat_lt]
    show ¬ n.toNat < (0 : u64).toNat
    have h0 : (0 : u64).toNat = 0 := rfl
    omega
  rw [h_dec1]
  simp only [Bool.false_eq_true, if_false]
  -- n -? 0 = pure n
  have h_sub : (n -? (0 : u64) : RustM u64) = pure n := by
    show (rust_primitives.ops.arith.Sub.sub n (0 : u64) : RustM u64) = pure n
    show (if BitVec.usubOverflow n.toBitVec (0 : u64).toBitVec then
            (.fail .integerOverflow : RustM u64) else pure (n - 0)) = pure n
    have h_no_uf : BitVec.usubOverflow n.toBitVec (0 : u64).toBitVec = false := by
      cases h_eq : BitVec.usubOverflow n.toBitVec (0 : u64).toBitVec with
      | false => rfl
      | true =>
        exfalso
        have : UInt64.subOverflow n (0 : u64) = true := h_eq
        rw [UInt64.subOverflow_iff] at this
        have h0 : (0 : UInt64).toNat = 0 := rfl
        omega
    rw [h_no_uf]
    simp only [Bool.false_eq_true, if_false]
    have h_n0 : n - 0 = n := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le']
      · show n.toNat - (0 : u64).toNat = n.toNat
        have h0 : (0 : u64).toNat = 0 := rfl
        omega
      · show (0 : u64).toNat ≤ n.toNat
        have h0 : (0 : u64).toNat = 0 := rfl; omega
    rw [h_n0]
  rw [h_sub]
  simp only [pure_bind]
  -- (0 >? n) = pure false (again)
  rw [h_gt1]
  simp only [pure_bind]
  rw [h_dec1]
  simp only [Bool.false_eq_true, if_false]
  -- Now we have binomial_loop n 0 1 1
  unfold binomial_u64.binomial_loop
  have h_gt2 : ((1 : u64) >? (0 : u64) : RustM Bool) = pure (decide ((1 : u64) > (0 : u64))) := rfl
  rw [h_gt2]
  simp only [pure_bind]
  have h_dec2 : (decide ((1 : u64) > (0 : u64))) = true := by decide
  rw [h_dec2]
  simp only [if_true]
  rfl

/-- Boundary `C(n, n) = 1`. Captures the `k = n` half of the property test
    `boundary_k_zero_and_k_eq_n`. Unconditional in `n`: when `n ≥ 1` the
    symmetry branch recurses to `binomial n 0`; when `n = 0` the loop returns
    `1` directly. -/
theorem binomial_k_eq_n (n : u64) :
    binomial_u64.binomial n n = RustM.ok 1 := by
  unfold binomial_u64.binomial
  -- (n >? n) = pure false
  have h_gt1 : (n >? n : RustM Bool) = pure (decide (n > n)) := rfl
  rw [h_gt1]
  simp only [pure_bind]
  have h_dec1 : (decide (n > n)) = false := by
    apply decide_eq_false
    show ¬ n < n
    rw [UInt64.lt_iff_toNat_lt]
    omega
  rw [h_dec1]
  simp only [Bool.false_eq_true, if_false]
  -- n -? n = pure 0
  have h_sub : (n -? n : RustM u64) = pure (n - n) := by
    show (rust_primitives.ops.arith.Sub.sub n n : RustM u64) = pure (n - n)
    show (if BitVec.usubOverflow n.toBitVec n.toBitVec then
            (.fail .integerOverflow : RustM u64) else pure (n - n)) = pure (n - n)
    have h_no_uf : BitVec.usubOverflow n.toBitVec n.toBitVec = false := by
      cases h_eq : BitVec.usubOverflow n.toBitVec n.toBitVec with
      | false => rfl
      | true =>
        exfalso
        have : UInt64.subOverflow n n = true := h_eq
        rw [UInt64.subOverflow_iff] at this
        omega
    rw [h_no_uf]
    simp only [Bool.false_eq_true, if_false]
  rw [h_sub]
  simp only [pure_bind]
  have h_n_minus_n : n - n = 0 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le' (Nat.le_refl _)]
    show n.toNat - n.toNat = (0 : u64).toNat
    have h0 : (0 : u64).toNat = 0 := rfl
    omega
  rw [h_n_minus_n]
  -- Now (n >? 0) and split on n = 0 or n > 0
  have h_gt2 : (n >? (0 : u64) : RustM Bool) = pure (decide (n > (0 : u64))) := rfl
  rw [h_gt2]
  simp only [pure_bind]
  by_cases hn0 : n = 0
  · -- n = 0 case: binomial 0 0 = pure 1 via binomial_loop 0 0 1 1
    subst hn0
    have h_dec2 : (decide ((0 : u64) > (0 : u64))) = false := by decide
    rw [h_dec2]
    simp only [Bool.false_eq_true, if_false]
    unfold binomial_u64.binomial_loop
    have h_gt3 : ((1 : u64) >? (0 : u64) : RustM Bool) =
                  pure (decide ((1 : u64) > (0 : u64))) := rfl
    rw [h_gt3]
    simp only [pure_bind]
    have h_dec3 : (decide ((1 : u64) > (0 : u64))) = true := by decide
    rw [h_dec3]
    simp only [if_true]
    rfl
  · -- n ≠ 0: recurse with `binomial n 0` and use previous lemma.
    have hn_pos : 0 < n.toNat := by
      rcases Nat.eq_zero_or_pos n.toNat with h | h
      · exfalso; apply hn0; apply UInt64.toNat_inj.mp; rw [h]; rfl
      · exact h
    have h_dec2 : (decide (n > (0 : u64))) = true := by
      apply decide_eq_true
      show (0 : u64) < n
      rw [UInt64.lt_iff_toNat_lt]
      show (0 : u64).toNat < n.toNat
      have h0 : (0 : u64).toNat = 0 := rfl
      omega
    rw [h_dec2]
    simp only [if_true]
    exact binomial_k_zero n

/-- Pascal's recurrence: `C(n, k) = C(n-1, k-1) + C(n-1, k)` for `n ≥ 1`
    and `1 ≤ k ≤ n`. Captures the property test `pascal_recurrence`. The
    defining recurrence of the binomial coefficients, independent of the
    symmetry and boundary clauses: a buggy implementation could satisfy
    all boundaries and symmetry but still miscompute interior cells, and
    would be caught here. Restricted to the overflow-free range `n ≤ 67`
    so that `binomial (n-1) (k-1)`, `binomial (n-1) k`, and their sum
    (which equals `C(n, k) ≤ C(67, 33) < 2 ^ 64`) all fit in `u64`. -/
theorem binomial_pascal_recurrence (n k : u64)
    (hn : n.toNat ≤ 67) (hk1 : 1 ≤ k.toNat) (hkn : k.toNat ≤ n.toNat) :
    ∃ v vl vr : u64,
      binomial_u64.binomial n k = RustM.ok v ∧
      binomial_u64.binomial (n - 1) (k - 1) = RustM.ok vl ∧
      binomial_u64.binomial (n - 1) k = RustM.ok vr ∧
      v.toNat = vl.toNat + vr.toNat := by
  -- Witnesses from the master postcondition.
  have hn_ge_1 : 1 ≤ n.toNat := Nat.le_trans hk1 hkn
  have h_n_sub : (n - 1).toNat = n.toNat - 1 := by
    apply UInt64.toNat_sub_of_le'
    show (1 : u64).toNat ≤ n.toNat
    have h1 : (1 : u64).toNat = 1 := rfl
    omega
  have h_k_sub : (k - 1).toNat = k.toNat - 1 := by
    apply UInt64.toNat_sub_of_le'
    show (1 : u64).toNat ≤ k.toNat
    have h1 : (1 : u64).toNat = 1 := rfl
    omega
  have hn1_le_67 : (n - 1).toNat ≤ 67 := by rw [h_n_sub]; omega
  -- The three master invocations.
  have h_main : binomial_u64.binomial n k =
                  RustM.ok (UInt64.ofNat (nchoose n.toNat k.toNat)) :=
    binomial_postcondition n k hn
  have h_left : binomial_u64.binomial (n - 1) (k - 1) =
                  RustM.ok (UInt64.ofNat (nchoose (n - 1).toNat (k - 1).toNat)) :=
    binomial_postcondition (n - 1) (k - 1) hn1_le_67
  have h_right : binomial_u64.binomial (n - 1) k =
                   RustM.ok (UInt64.ofNat (nchoose (n - 1).toNat k.toNat)) :=
    binomial_postcondition (n - 1) k hn1_le_67
  refine ⟨_, _, _, h_main, h_left, h_right, ?_⟩
  -- Goal: v.toNat = vl.toNat + vr.toNat, all three being ofNat (nchoose ...)
  -- Bounds:
  have h_b_main : nchoose n.toNat k.toNat < 2 ^ 64 := nchoose_lt_2_64 _ _ hn
  have h_b_left : nchoose (n - 1).toNat (k - 1).toNat < 2 ^ 64 :=
    nchoose_lt_2_64 _ _ hn1_le_67
  have h_b_right : nchoose (n - 1).toNat k.toNat < 2 ^ 64 :=
    nchoose_lt_2_64 _ _ hn1_le_67
  -- Reduce ofNat.toNat via the bounds.
  rw [UInt64.toNat_ofNat_of_lt' h_b_main,
      UInt64.toNat_ofNat_of_lt' h_b_left,
      UInt64.toNat_ofNat_of_lt' h_b_right]
  -- Goal: nchoose n.toNat k.toNat = nchoose (n-1).toNat (k-1).toNat + nchoose (n-1).toNat k.toNat
  rw [h_n_sub, h_k_sub]
  -- Goal: nchoose n.toNat k.toNat = nchoose (n.toNat - 1) (k.toNat - 1) + nchoose (n.toNat - 1) k.toNat
  -- Rewrite n.toNat = m + 1, k.toNat = j + 1 via Pascal's recurrence.
  obtain ⟨m, hm⟩ : ∃ m, n.toNat = m + 1 := ⟨n.toNat - 1, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, k.toNat = j + 1 := ⟨k.toNat - 1, by omega⟩
  rw [hm, hj]
  show nchoose (m + 1) (j + 1) = nchoose m j + nchoose m (j + 1)
  rfl

/-- Symmetry: `C(n, k) = C(n, n - k)` for `k ≤ n`. Captures the property
    test `symmetry`. A structural property the implementation exploits (the
    `if k > n - k { return binomial(n, n - k); }` line in the Rust source,
    which bounds the inner loop to `min(k, n - k) + 1` iterations), and
    also an independent semantic clause. Stated within the overflow-free
    range `n ≤ 67`. -/
theorem binomial_symmetry (n k : u64) (hn : n.toNat ≤ 67) (hkn : k.toNat ≤ n.toNat) :
    ∃ v : u64,
      binomial_u64.binomial n k = RustM.ok v ∧
      binomial_u64.binomial n (n - k) = RustM.ok v := by
  refine ⟨UInt64.ofNat (nchoose n.toNat k.toNat),
          binomial_postcondition n k hn, ?_⟩
  rw [binomial_postcondition n (n - k) hn]
  congr 2
  have h_sub : (n - k).toNat = n.toNat - k.toNat :=
    UInt64.toNat_sub_of_le' hkn
  rw [h_sub]
  exact (nchoose_symm n.toNat k.toNat hkn).symm

end Binomial_u64Obligations
