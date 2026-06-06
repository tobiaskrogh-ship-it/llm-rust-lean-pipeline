-- Companion obligations file for the `multinomial_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import multinomial_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Multinomial_u64Obligations

/-! ## Mathematical binomial coefficient.

Lean core does not provide `Nat.choose` (only Mathlib does); define one
locally so the closed-form spec can use it. -/

/-- Mathematical binomial coefficient. Standard Pascal-triangle definition. -/
private def nchoose : Nat → Nat → Nat
  | _,     0     => 1
  | 0,     _ + 1 => 0
  | n + 1, k + 1 => nchoose n k + nchoose n (k + 1)

/-! ## Prefix-based specifications of running sum and multinomial product.

These mirror the algorithm's left-to-right iteration in `multinomial_loop`,
viewed at the `Nat` level so the spec itself cannot overflow. -/

private def sum_prefix (k : RustSlice u64) : Nat → Nat
  | 0     => 0
  | i + 1 =>
      sum_prefix k i +
        (if h : i < k.val.size then (k.val[i]'h).toNat else 0)

private def mult_prefix (k : RustSlice u64) : Nat → Nat
  | 0     => 1
  | i + 1 =>
      mult_prefix k i *
        (if h : i < k.val.size then
           nchoose (sum_prefix k (i + 1)) (k.val[i]'h).toNat
         else 1)

/-! ## Nat-level helpers for `nchoose`. -/

/-- `nchoose n k = 0` for `n < k`. -/
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

/-- `nchoose n n = 1` for all `n`. -/
private theorem nchoose_self : ∀ n, nchoose n n = 1
  | 0 => rfl
  | n + 1 => by
    show nchoose n n + nchoose n (n + 1) = 1
    rw [nchoose_self n, nchoose_eq_zero_of_lt n (n + 1) (Nat.lt_succ_self n)]

/-- `nchoose n 0 = 1` for all `n`. -/
private theorem nchoose_zero (n : Nat) : nchoose n 0 = 1 := by
  cases n <;> rfl

/-- `1 ≤ nchoose n k` whenever `k ≤ n`. -/
private theorem nchoose_ge_one : ∀ n k, k ≤ n → 1 ≤ nchoose n k
  | _, 0, _ => by rw [nchoose_zero]; exact Nat.le.refl
  | 0, _ + 1, h => by omega
  | n + 1, k + 1, h => by
    have hk : k ≤ n := by omega
    have ih := nchoose_ge_one n k hk
    show 1 ≤ nchoose n k + nchoose n (k + 1)
    omega

/-! ### Efficient Pascal-row computation for finite bound checks. -/

private def pascalNext (row : List Nat) : List Nat :=
  List.zipWith (· + ·) (0 :: row) (row ++ [0])

private def pascalRow : Nat → List Nat
  | 0 => [1]
  | n + 1 => pascalNext (pascalRow n)

private def nchooseFast (n k : Nat) : Nat := (pascalRow n).getD k 0

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

private theorem pascalRow_getD : ∀ n k, (pascalRow n).getD k 0 = nchoose n k
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | n + 1, 0 => by
    show (pascalNext (pascalRow n)).getD 0 0 = 1
    rw [pascalNext_getD]
    show 0 + (pascalRow n).getD 0 0 = 1
    rw [pascalRow_getD n 0]
    rw [nchoose_zero]
  | n + 1, k + 1 => by
    show (pascalNext (pascalRow n)).getD (k + 1) 0 = nchoose (n + 1) (k + 1)
    rw [pascalNext_getD]
    show (pascalRow n).getD k 0 + (pascalRow n).getD (k + 1) 0 = nchoose n k + nchoose n (k + 1)
    rw [pascalRow_getD n k, pascalRow_getD n (k + 1)]

private theorem nchooseFast_eq (n k : Nat) : nchooseFast n k = nchoose n k :=
  pascalRow_getD n k

/-! ## Multiplicative step identity for `nchoose`. -/

private theorem nchoose_step :
    ∀ n j, (j + 1) * nchoose n (j + 1) = nchoose n j * (n - j)
  | 0, 0 => by
    show (1 : Nat) * nchoose 0 1 = nchoose 0 0 * (0 - 0)
    show (1 : Nat) * 0 = 1 * 0
    rfl
  | 0, j + 1 => by
    show (j + 2) * nchoose 0 (j + 2) = nchoose 0 (j + 1) * (0 - (j + 1))
    have h1 : nchoose 0 (j + 2) = 0 := rfl
    have h2 : nchoose 0 (j + 1) = 0 := rfl
    rw [h1, h2]
    simp
  | n + 1, 0 => by
    show (1 : Nat) * nchoose (n + 1) 1 = nchoose (n + 1) 0 * (n + 1 - 0)
    show (1 : Nat) * (nchoose n 0 + nchoose n 1) =
         nchoose (n + 1) 0 * (n + 1 - 0)
    have h_nch_n_0 : nchoose n 0 = 1 := nchoose_zero n
    have h_nch_n1_0 : nchoose (n + 1) 0 = 1 := rfl
    rw [h_nch_n_0, h_nch_n1_0, Nat.sub_zero, Nat.one_mul, Nat.one_mul]
    have ih : nchoose n 1 = n := by
      have := nchoose_step n 0
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
    · have ihj := nchoose_step n j
      have ihjp1 := nchoose_step n (j + 1)
      have h_rhs : (nchoose n j + nchoose n (j + 1)) * (n - j) =
                   nchoose n j * (n - j) + nchoose n (j + 1) * (n - j) :=
        Nat.add_mul _ _ _
      rw [h_rhs]
      rw [Nat.mul_add]
      have h_jp2_eq : (j + 2 : Nat) * nchoose n (j + 2) =
                       nchoose n (j + 1) * (n - (j + 1)) := ihjp1
      rw [h_jp2_eq]
      have h1 : (j + 2 : Nat) * nchoose n (j + 1) =
                (j + 1) * nchoose n (j + 1) + nchoose n (j + 1) := by
        rw [show (j + 2 : Nat) = (j + 1) + 1 from rfl, Nat.add_mul, Nat.one_mul]
      rw [h1, ihj]
      rw [Nat.add_assoc]
      congr 1
      have h_n_jm1 : n - j = n - (j + 1) + 1 := by omega
      rw [h_n_jm1, Nat.mul_add, Nat.mul_one]
      exact Nat.add_comm _ _
    · have hjn' : n ≤ j := by omega
      have h_n_j : n - j = 0 := by omega
      have h1 : nchoose n (j + 1) = 0 :=
        nchoose_eq_zero_of_lt n (j + 1) (by omega)
      have h2 : nchoose n (j + 2) = 0 :=
        nchoose_eq_zero_of_lt n (j + 2) (by omega)
      rw [h_n_j, Nat.mul_zero, h1, h2]
      simp

/-- Symmetry of `nchoose`: `nchoose n k = nchoose n (n - k)` for `k ≤ n`. -/
private theorem nchoose_symm : ∀ n k, k ≤ n → nchoose n k = nchoose n (n - k)
  | 0,     0,     _ => rfl
  | 0,     _ + 1, h => by omega
  | n + 1, 0,     _ => by
    show 1 = nchoose (n + 1) (n + 1 - 0)
    rw [Nat.sub_zero]
    exact (nchoose_self (n + 1)).symm
  | n + 1, k + 1, h => by
    have hk : k ≤ n := by omega
    show nchoose n k + nchoose n (k + 1) = nchoose (n + 1) (n + 1 - (k + 1))
    have h_rhs_sub : n + 1 - (k + 1) = n - k := by omega
    rw [h_rhs_sub]
    by_cases hk_lt_n : k + 1 ≤ n
    · have h_ih1 : nchoose n k = nchoose n (n - k) := nchoose_symm n k hk
      have h_ih2 : nchoose n (k + 1) = nchoose n (n - (k + 1)) :=
        nchoose_symm n (k + 1) hk_lt_n
      rw [h_ih1, h_ih2]
      have hj_eq : ∃ j, n - k = j + 1 := ⟨n - k - 1, by omega⟩
      obtain ⟨j, hj⟩ := hj_eq
      have hj' : n - (k + 1) = j := by omega
      rw [hj, hj']
      show nchoose n (j + 1) + nchoose n j = nchoose n j + nchoose n (j + 1)
      omega
    · have hk_eq_n : k = n := by omega
      rw [hk_eq_n, Nat.sub_self]
      show nchoose n n + nchoose n (n + 1) = 1
      rw [nchoose_self n, nchoose_eq_zero_of_lt n (n + 1) (Nat.lt_succ_self n)]

/-! ## Monotonicity of `nchoose` on the increasing side. -/

private theorem nchoose_le_succ_of_half (n d : Nat) (h : 2 * d + 1 ≤ n) :
    nchoose n d ≤ nchoose n (d + 1) := by
  -- (d+1) * nchoose n (d+1) = nchoose n d * (n - d)
  have step := nchoose_step n d
  -- From step: nchoose n d * (n - d) = (d + 1) * nchoose n (d + 1)
  -- So: (d + 1) * nchoose n d ≤ (d + 1) * nchoose n (d + 1)  [given d + 1 ≤ n - d]
  -- iff nchoose n d ≤ nchoose n (d + 1).
  have h_n_minus_d : d + 1 ≤ n - d := by omega
  have h1 : (d + 1) * nchoose n d ≤ nchoose n d * (n - d) := by
    rw [Nat.mul_comm (d + 1) (nchoose n d)]
    exact Nat.mul_le_mul_left (nchoose n d) h_n_minus_d
  rw [← step] at h1
  exact Nat.le_of_mul_le_mul_left h1 (by omega : 0 < d + 1)

/-- `nchoose n d ≤ nchoose n k` whenever `d ≤ k ≤ n / 2` (here `2k ≤ n`). -/
private theorem nchoose_mono_to_half (n k d : Nat) (hdk : d ≤ k) (hk : 2 * k ≤ n) :
    nchoose n d ≤ nchoose n k := by
  -- Induction on k - d.
  induction h : k - d generalizing d with
  | zero =>
    have hd_eq : d = k := by omega
    rw [hd_eq]
    exact Nat.le.refl
  | succ m ih =>
    have h_next : k - (d + 1) = m := by omega
    have h_d_lt : d + 1 ≤ k := by omega
    have h_2d_lt : 2 * d + 1 ≤ n := by omega
    have ih' := ih (d + 1) h_d_lt h_next
    have h_le := nchoose_le_succ_of_half n d h_2d_lt
    exact Nat.le_trans h_le ih'

/-! ## Trailing-zeros infrastructure. -/

open rust_primitives.hax (Tuple2)

/-- `RustM.ok`-headed bind reduction. -/
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
      multinomial_u64.trailing_zeros_u64 x
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
  unfold multinomial_u64.trailing_zeros_u64
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

private theorem tz_nonzero_spec (x : u64) (hx : x ≠ 0) :
    ∃ r : u32, multinomial_u64.trailing_zeros_u64 x = RustM.ok r ∧
                r.toNat < 64 ∧
                2 ^ r.toNat ∣ x.toNat ∧
                (x.toNat >>> r.toNat) &&& 1 = 1 := by
  have h := tz_function_nonzero_triple x hx
  rw [RustM.Triple_iff_BitVec] at h
  simp only [decide_true, Bool.not_true, Bool.false_or,
             Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hok, hpost⟩ := h
  cases hf : multinomial_u64.trailing_zeros_u64 x with
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

private theorem tz_zero :
    multinomial_u64.trailing_zeros_u64 (0 : u64) = RustM.ok (64 : u32) := by
  unfold multinomial_u64.trailing_zeros_u64
  rfl

/-! ## Nat-level Stein identities. -/

private theorem nat_gcd_double_both (m n : Nat) :
    Nat.gcd (2 * m) (2 * n) = 2 * Nat.gcd m n :=
  Nat.gcd_mul_left 2 m n

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

private theorem nat_gcd_sub_right (m n : Nat) (h : n ≤ m) :
    Nat.gcd m n = Nat.gcd (m - n) n := by
  have h_eq : Nat.gcd m n = Nat.gcd ((m - n) + n) n := by
    rw [Nat.sub_add_cancel h]
  rw [h_eq, Nat.gcd_add_self_left]

private theorem nat_gcd_mul_pow_two_left_odd_right (a n : Nat) (hn : n % 2 = 1) :
    ∀ k, Nat.gcd (a * 2 ^ k) n = Nat.gcd a n
  | 0 => by rw [Nat.pow_zero, Nat.mul_one]
  | k + 1 => by
    have ih := nat_gcd_mul_pow_two_left_odd_right a n hn k
    have h_eq : a * 2 ^ (k + 1) = 2 * (a * 2 ^ k) := by
      rw [Nat.pow_succ]
      rw [← Nat.mul_assoc, Nat.mul_comm (a * 2 ^ k) 2]
    rw [h_eq, nat_gcd_two_left_odd_right _ _ hn, ih]

/-! ## `gcd_stein_loop` closed form. -/

private theorem gcd_lt_2_64 (a b : u64) : Nat.gcd a.toNat b.toNat < 2 ^ 64 := by
  by_cases hb : b.toNat = 0
  · rw [hb, Nat.gcd_zero_right]
    exact a.toNat_lt
  · have h_le : Nat.gcd a.toNat b.toNat ≤ b.toNat :=
      Nat.gcd_le_right a.toNat (Nat.pos_of_ne_zero hb)
    exact Nat.lt_of_le_of_lt h_le b.toNat_lt

private theorem gcd_toNat_ofNat (a b : u64) :
    (UInt64.ofNat (Nat.gcd a.toNat b.toNat)).toNat = Nat.gcd a.toNat b.toNat :=
  UInt64.toNat_ofNat_of_lt' (gcd_lt_2_64 a b)

private theorem gcd_stein_loop_spec (m n : u64)
    (hm_odd : m.toNat % 2 = 1) (hn_odd : n.toNat % 2 = 1) :
    multinomial_u64.gcd_stein_loop m n
      = RustM.ok (UInt64.ofNat (Nat.gcd m.toNat n.toNat)) := by
  have hm_pos : 0 < m.toNat := by omega
  have hn_pos : 0 < n.toNat := by omega
  induction hk : (m.toNat + n.toNat) using Nat.strongRecOn generalizing m n with
  | _ k ih =>
    unfold multinomial_u64.gcd_stein_loop
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

/-! ## Outer-wrapper Nat helpers for `gcd`. -/

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

/-! ## `gcd` closed form (named `gcd`, not `gcd_u64`, in this crate). -/

private theorem gcd_spec (a b : u64) :
    multinomial_u64.gcd a b
      = RustM.ok (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) := by
  unfold multinomial_u64.gcd
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

/-! ## `multiply_and_divide` closed form. -/

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

private theorem mad_value (r a b : Nat) (hb : 0 < b) (hdvd : b ∣ r * a) :
    (r / Nat.gcd r b) * (a / (b / Nat.gcd r b)) = r * a / b := by
  have hg_pos : 0 < Nat.gcd r b := Nat.gcd_pos_of_pos_right r hb
  exact mad_value_param r a b (Nat.gcd r b) hb hdvd hg_pos
    (Nat.gcd_dvd_left r b) (Nat.gcd_dvd_right r b)
    (Nat.coprime_div_gcd_div_gcd hg_pos)

private theorem multiply_and_divide_spec (r a b : u64)
    (hb_pos : 0 < b.toNat)
    (hdvd : b.toNat ∣ r.toNat * a.toNat)
    (h_result_lt : r.toNat * a.toNat / b.toNat < 2 ^ 64) :
    multinomial_u64.multiply_and_divide r a b
      = RustM.ok (UInt64.ofNat (r.toNat * a.toNat / b.toNat)) := by
  unfold multinomial_u64.multiply_and_divide
  rw [gcd_spec r b]
  simp only [RustM_ok_bind]
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
  have h_bg_natpos : 0 < b.toNat / (UInt64.ofNat (Nat.gcd r.toNat b.toNat)).toNat :=
    Nat.div_pos (Nat.le_of_dvd hb_pos h_g_dvd_b) hg_pos
  have h_bg_pos : 0 < (b / UInt64.ofNat (Nat.gcd r.toNat b.toNat)).toNat := by
    rw [h_bg_toNat]; exact h_bg_natpos
  have h_bg_ne : (b / UInt64.ofNat (Nat.gcd r.toNat b.toNat)) ≠ 0 := by
    intro h
    have : (b / UInt64.ofNat (Nat.gcd r.toNat b.toNat)).toNat = 0 := by rw [h]; rfl
    omega
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
  have h_abg_toNat :
      (a / (b / UInt64.ofNat (Nat.gcd r.toNat b.toNat))).toNat =
      a.toNat / (b.toNat / (UInt64.ofNat (Nat.gcd r.toNat b.toNat)).toNat) := by
    rw [UInt64.toNat_div, h_bg_toNat]
  have h_value :
      (r / UInt64.ofNat (Nat.gcd r.toNat b.toNat)).toNat *
      (a / (b / UInt64.ofNat (Nat.gcd r.toNat b.toNat))).toNat =
      r.toNat * a.toNat / b.toNat := by
    rw [h_rg_toNat, h_abg_toNat, hg_toNat]
    exact mad_value r.toNat a.toNat b.toNat hb_pos hdvd
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

/-! ## `binomial_loop` closed form (general version). -/

/-- General binomial-loop spec: works under `nchoose n_init k < 2^64` plus
    the loop invariant `2k ≤ n_init` (the "else" branch of `binomial`).
    The reference's `n ≤ 67` form is a corollary. -/
private theorem binomial_loop_spec (n_init k : u64) :
    ∀ (n d r : u64),
      k.toNat ≤ n_init.toNat - k.toNat →
      1 ≤ d.toNat →
      d.toNat ≤ k.toNat + 1 →
      n.toNat + d.toNat = n_init.toNat + 1 →
      r.toNat = nchoose n_init.toNat (d.toNat - 1) →
      nchoose n_init.toNat k.toNat < 2 ^ 64 →
      multinomial_u64.binomial_loop n k d r
        = RustM.ok (UInt64.ofNat (nchoose n_init.toNat k.toNat)) := by
  intro n d r hk_half hd_pos hd_bound hn_eq hr_eq hbnd
  induction hkd : (k.toNat + 1 - d.toNat) using Nat.strongRecOn generalizing n d r with
  | _ K ih =>
    unfold multinomial_u64.binomial_loop
    have h_gt_eqq : (d >? k : RustM Bool) = pure (decide (d > k)) := rfl
    rw [h_gt_eqq]
    simp only [pure_bind]
    by_cases hdk : d > k
    · -- termination branch
      rw [decide_eq_true hdk]
      simp only [if_true]
      have hdk_nat : k.toNat < d.toNat := UInt64.lt_iff_toNat_lt.mp hdk
      have hd_eq : d.toNat = k.toNat + 1 := by omega
      show RustM.ok r = RustM.ok (UInt64.ofNat (nchoose n_init.toNat k.toNat))
      congr 1
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_ofNat_of_lt' hbnd, hr_eq, hd_eq]
      rfl
    · -- recursive branch
      rw [decide_eq_false hdk]
      simp only [Bool.false_eq_true, if_false]
      have hdk_nat : d.toNat ≤ k.toNat := by
        rcases Nat.lt_or_ge k.toNat d.toNat with h | h
        · exfalso; apply hdk; exact UInt64.lt_iff_toNat_lt.mpr h
        · exact h
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
      have hd_lt : d.toNat + 1 < 2 ^ 64 := by
        have hk_lt : k.toNat < 2 ^ 64 := UInt64.toNat_lt k
        have hn_init_lt : n_init.toNat < 2 ^ 64 := UInt64.toNat_lt n_init
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
      have hd_natpos : 0 < d.toNat := hd_pos
      have h_dvd : d.toNat ∣ r.toNat * n.toNat := by
        rw [hr_eq]
        have h_n_eq : n.toNat = n_init.toNat - (d.toNat - 1) := by omega
        rw [h_n_eq]
        have step := nchoose_step n_init.toNat (d.toNat - 1)
        have h_d_succ : d.toNat - 1 + 1 = d.toNat := by omega
        rw [h_d_succ] at step
        rw [← step]
        exact ⟨nchoose n_init.toNat d.toNat, rfl⟩
      -- nchoose n_init.toNat d.toNat ≤ nchoose n_init.toNat k.toNat (monotonicity)
      have h_2k_le_n : 2 * k.toNat ≤ n_init.toNat := by omega
      have h_nch_d_le_k :
          nchoose n_init.toNat d.toNat ≤ nchoose n_init.toNat k.toNat :=
        nchoose_mono_to_half n_init.toNat k.toNat d.toNat hdk_nat h_2k_le_n
      have h_nch_d_lt_2_64 : nchoose n_init.toNat d.toNat < 2 ^ 64 :=
        Nat.lt_of_le_of_lt h_nch_d_le_k hbnd
      have h_value_lt : r.toNat * n.toNat / d.toNat < 2 ^ 64 := by
        rw [hr_eq]
        have h_n_eq : n.toNat = n_init.toNat - (d.toNat - 1) := by omega
        rw [h_n_eq]
        have step := nchoose_step n_init.toNat (d.toNat - 1)
        have h_d_succ : d.toNat - 1 + 1 = d.toNat := by omega
        rw [h_d_succ] at step
        rw [← step]
        rw [Nat.mul_div_cancel_left _ hd_natpos]
        exact h_nch_d_lt_2_64
      rw [multiply_and_divide_spec r n d hd_natpos h_dvd h_value_lt]
      simp only [RustM_ok_bind]
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
      have h_v_toNat : (UInt64.ofNat (nchoose n_init.toNat d.toNat)).toNat =
                       nchoose n_init.toNat d.toNat :=
        UInt64.toNat_ofNat_of_lt' h_nch_d_lt_2_64
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
        rfl
      exact ih (k.toNat + 1 - (d + 1).toNat) h_new_meas
        (n - 1) (d + 1) (UInt64.ofNat (nchoose n_init.toNat d.toNat))
        h_new_hd_pos h_new_hd_bound h_new_hn_eq h_new_hr_eq rfl

/-- Else-branch helper. -/
private theorem binomial_else_branch (n k : u64)
    (hbnd : nchoose n.toNat k.toNat < 2 ^ 64)
    (hk_le_half : k.toNat ≤ n.toNat - k.toNat) :
    multinomial_u64.binomial_loop n k 1 1 =
      RustM.ok (UInt64.ofNat (nchoose n.toNat k.toNat)) := by
  apply binomial_loop_spec n k n 1 1 hk_le_half
  · show 1 ≤ (1 : u64).toNat; decide
  · show (1 : u64).toNat ≤ k.toNat + 1
    have h1 : (1 : u64).toNat = 1 := rfl
    omega
  · show n.toNat + (1 : u64).toNat = n.toNat + 1
    rfl
  · show (1 : u64).toNat = nchoose n.toNat ((1 : u64).toNat - 1)
    have h1 : (1 : u64).toNat = 1 := rfl
    rw [h1]
    show 1 = nchoose n.toNat 0
    rw [nchoose_zero]
  · exact hbnd

/-- General `binomial` postcondition: works whenever `nchoose n k < 2^64`. -/
private theorem binomial_postcondition_gen (n k : u64)
    (hbnd : nchoose n.toNat k.toNat < 2 ^ 64) :
    multinomial_u64.binomial n k = RustM.ok (UInt64.ofNat (nchoose n.toNat k.toNat)) := by
  unfold multinomial_u64.binomial
  have h_gt_eqq : (k >? n : RustM Bool) = pure (decide (k > n)) := rfl
  rw [h_gt_eqq]
  simp only [pure_bind]
  by_cases hkn : k > n
  · rw [decide_eq_true hkn]
    simp only [if_true]
    have hkn_nat : n.toNat < k.toNat := UInt64.lt_iff_toNat_lt.mp hkn
    show RustM.ok (0 : u64) = RustM.ok (UInt64.ofNat (nchoose n.toNat k.toNat))
    congr 1
    have h_zero : nchoose n.toNat k.toNat = 0 := nchoose_eq_zero_of_lt _ _ hkn_nat
    rw [h_zero]
    rfl
  · rw [decide_eq_false hkn]
    simp only [Bool.false_eq_true, if_false]
    have hk_le_n : k.toNat ≤ n.toNat := by
      rcases Nat.lt_or_ge n.toNat k.toNat with h | h
      · exfalso; apply hkn; exact UInt64.lt_iff_toNat_lt.mpr h
      · exact h
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
    · rw [decide_eq_true hk_gt_nk]
      simp only [if_true]
      have hk_gt_nk_nat : (n - k).toNat < k.toNat :=
        UInt64.lt_iff_toNat_lt.mp hk_gt_nk
      rw [h_n_sub_toNat] at hk_gt_nk_nat
      -- Recurse: binomial n (n - k), where 2(n - k) ≤ n
      unfold multinomial_u64.binomial
      have h_gt_eqq' : ((n - k) >? n : RustM Bool) = pure (decide ((n - k) > n)) := rfl
      rw [h_gt_eqq']
      simp only [pure_bind]
      have h_nk_le_n : (n - k).toNat ≤ n.toNat := by
        rw [h_n_sub_toNat]; omega
      have h_nk_not_gt_n : ¬ ((n - k) > n) := by
        intro h
        have : n.toNat < (n - k).toNat := UInt64.lt_iff_toNat_lt.mp h
        omega
      rw [decide_eq_false h_nk_not_gt_n]
      simp only [Bool.false_eq_true, if_false]
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
      have h_nk_le_half : (n - k).toNat ≤ n.toNat - (n - k).toNat := by
        rw [h_n_sub_toNat]; omega
      have h_nch_eq : nchoose n.toNat (n - k).toNat = nchoose n.toNat k.toNat := by
        rw [h_n_sub_toNat]
        exact (nchoose_symm n.toNat k.toNat hk_le_n).symm
      have h_bnd' : nchoose n.toNat (n - k).toNat < 2 ^ 64 := by
        rw [h_nch_eq]; exact hbnd
      rw [binomial_else_branch n (n - k) h_bnd' h_nk_le_half]
      rw [h_nch_eq]
    · rw [decide_eq_false hk_gt_nk]
      simp only [Bool.false_eq_true, if_false]
      have hk_le_nk_nat : k.toNat ≤ (n - k).toNat := by
        rcases Nat.lt_or_ge (n - k).toNat k.toNat with h | h
        · exfalso; apply hk_gt_nk; exact UInt64.lt_iff_toNat_lt.mpr h
        · exact h
      rw [h_n_sub_toNat] at hk_le_nk_nat
      exact binomial_else_branch n k hbnd hk_le_nk_nat

/-- `binomial(n, n) = 1` for every `n : u64`. -/
private theorem binomial_k_eq_n (n : u64) :
    multinomial_u64.binomial n n = RustM.ok (1 : u64) := by
  have h_bnd : nchoose n.toNat n.toNat < 2 ^ 64 := by
    rw [nchoose_self]; decide
  rw [binomial_postcondition_gen n n h_bnd]
  congr 1
  rw [nchoose_self]
  rfl

/-! ## Multinomial-loop step lemmas. -/

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

/-- OOB step: when `i.toNat ≥ k.val.size`, `multinomial_loop` returns `ok r`. -/
private theorem multinomial_loop_oob (k : RustSlice u64) (i : usize) (p r : u64)
    (hi : k.val.size ≤ i.toNat) :
    multinomial_u64.multinomial_loop k i p r = RustM.ok r := by
  conv => lhs; unfold multinomial_u64.multinomial_loop
  have h_ofNat : (USize64.ofNat k.val.size).toNat = k.val.size :=
    USize64.toNat_ofNat_of_lt' k.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat k.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- Recurse step: when `i.toNat < k.val.size`, no overflow on `+` and `*`,
    and `binomial(p + k[i], k[i])` succeeds with value `b`, the loop
    transitions to the next index. -/
private theorem multinomial_loop_recurse
    (k : RustSlice u64) (i : usize) (p r : u64)
    (hi : i.toNat < k.val.size)
    (hno_add : ¬ UInt64.addOverflow p (k.val[i.toNat]'hi))
    (b : u64)
    (hb : multinomial_u64.binomial (p + k.val[i.toNat]'hi) (k.val[i.toNat]'hi)
           = RustM.ok b)
    (hno_mul : ¬ UInt64.mulOverflow r b) :
    multinomial_u64.multinomial_loop k i p r =
      multinomial_u64.multinomial_loop k (i + 1)
        (p + k.val[i.toNat]'hi) (r * b) := by
  conv => lhs; unfold multinomial_u64.multinomial_loop
  have h_ofNat : (USize64.ofNat k.val.size).toNat = k.val.size :=
    USize64.toNat_ofNat_of_lt' k.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat k.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (k[i]_? : RustM u64) = RustM.ok (k.val[i.toNat]'hi) := by
    show (if h : i.toNat < k.val.size then pure (k.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (k.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
  have h_no_bv :
      BitVec.uaddOverflow p.toBitVec (k.val[i.toNat]'hi).toBitVec = false := by
    cases hb' : BitVec.uaddOverflow p.toBitVec (k.val[i.toNat]'hi).toBitVec with
    | false => rfl
    | true => exact absurd hb' hno_add
  have h_no_mul_bv :
      BitVec.umulOverflow r.toBitVec b.toBitVec = false := by
    cases hb' : BitVec.umulOverflow r.toBitVec b.toBitVec with
    | false => rfl
    | true => exact absurd hb' hno_mul
  have h_size_lt : k.val.size < 2^64 := k.size_lt_usizeSize
  have h_no_overflow_i : i.toNat + 1 < 2^64 := by omega
  have h_no_bv_i :
      BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hii := (USize64.uaddOverflow_iff i 1).mp hbo
      rw [usize_one_toNat] at hii
      omega
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.ops.arith.Add.add, h_no_bv, h_no_bv_i,
             rust_primitives.ops.arith.Mul.mul, h_no_mul_bv,
             hb]

/-! ## Monotonicity of `mult_prefix` and bounds derived from `hfit_result`. -/

/-- The factor at step `i` is at least 1 (because `sum_prefix k (i+1) ≥ k[i].toNat`). -/
private theorem nchoose_factor_ge_one (k : RustSlice u64) (i : Nat)
    (hi : i < k.val.size) :
    1 ≤ nchoose (sum_prefix k (i + 1)) (k.val[i]'hi).toNat := by
  apply nchoose_ge_one
  -- need (k.val[i]'hi).toNat ≤ sum_prefix k (i + 1)
  show (k.val[i]'hi).toNat ≤ sum_prefix k (i + 1)
  show (k.val[i]'hi).toNat ≤ sum_prefix k i +
        (if h : i < k.val.size then (k.val[i]'h).toNat else 0)
  rw [dif_pos hi]
  omega

/-- `mult_prefix k i ≤ mult_prefix k j` for `i ≤ j ≤ k.val.size`. -/
private theorem mult_prefix_mono (k : RustSlice u64) :
    ∀ i j, i ≤ j → j ≤ k.val.size → mult_prefix k i ≤ mult_prefix k j := by
  intro i j hij hj
  induction j with
  | zero =>
    have : i = 0 := by omega
    rw [this]
    exact Nat.le.refl
  | succ j ih =>
    by_cases h_eq : i = j + 1
    · rw [h_eq]
      exact Nat.le.refl
    · have hij' : i ≤ j := by omega
      have hj' : j ≤ k.val.size := by omega
      have ih' := ih hij' hj'
      have hj_lt : j < k.val.size := by omega
      show mult_prefix k i ≤ mult_prefix k j *
        (if h : j < k.val.size then nchoose (sum_prefix k (j+1)) (k.val[j]'h).toNat else 1)
      rw [dif_pos hj_lt]
      have h_factor_ge : 1 ≤ nchoose (sum_prefix k (j + 1)) (k.val[j]'hj_lt).toNat :=
        nchoose_factor_ge_one k j hj_lt
      calc mult_prefix k i
          ≤ mult_prefix k j := ih'
        _ = mult_prefix k j * 1 := (Nat.mul_one _).symm
        _ ≤ mult_prefix k j * nchoose (sum_prefix k (j+1)) (k.val[j]'hj_lt).toNat :=
            Nat.mul_le_mul_left _ h_factor_ge

/-- `sum_prefix k i ≤ sum_prefix k j` for `i ≤ j`. -/
private theorem sum_prefix_mono (k : RustSlice u64) :
    ∀ i j, i ≤ j → sum_prefix k i ≤ sum_prefix k j := by
  intro i j hij
  induction j with
  | zero =>
    have : i = 0 := by omega
    rw [this]
    exact Nat.le.refl
  | succ j ih =>
    by_cases h_eq : i = j + 1
    · rw [h_eq]
      exact Nat.le.refl
    · have hij' : i ≤ j := by omega
      have ih' := ih hij'
      show sum_prefix k i ≤ sum_prefix k j + _
      omega

/-- The individual factor `nchoose (sum_prefix k (i+1)) (k.val[i]'hi).toNat` is
    `≤ mult_prefix k (i+1)`. -/
private theorem nchoose_factor_le_mult_prefix (k : RustSlice u64) (i : Nat)
    (hi : i < k.val.size) :
    nchoose (sum_prefix k (i + 1)) (k.val[i]'hi).toNat ≤ mult_prefix k (i + 1) := by
  show nchoose (sum_prefix k (i + 1)) (k.val[i]'hi).toNat ≤
       mult_prefix k i * _
  rw [dif_pos hi]
  -- mult_prefix k i ≥ 1, factor ≥ 0, so factor ≤ mult_prefix k i * factor
  have h_mp_ge : 1 ≤ mult_prefix k i := by
    have := mult_prefix_mono k 0 i (Nat.zero_le _) (by omega)
    show 1 ≤ mult_prefix k i
    show (1 : Nat) ≤ mult_prefix k i
    have h0 : mult_prefix k 0 = 1 := rfl
    omega
  calc nchoose (sum_prefix k (i + 1)) (k.val[i]'hi).toNat
      = 1 * nchoose (sum_prefix k (i + 1)) (k.val[i]'hi).toNat := (Nat.one_mul _).symm
    _ ≤ mult_prefix k i * nchoose (sum_prefix k (i + 1)) (k.val[i]'hi).toNat :=
        Nat.mul_le_mul_right _ h_mp_ge

/-! ## Main multinomial-loop correctness. -/

private theorem multinomial_loop_correct (k : RustSlice u64)
    (hfit_sum : sum_prefix k k.val.size < 2 ^ 64)
    (hfit_result : mult_prefix k k.val.size < 2 ^ 64) :
    ∀ (m : Nat) (i : usize) (p r : u64),
      k.val.size - i.toNat ≤ m →
      i.toNat ≤ k.val.size →
      p.toNat = sum_prefix k i.toNat →
      r.toNat = mult_prefix k i.toNat →
      multinomial_u64.multinomial_loop k i p r =
        RustM.ok (UInt64.ofNat (mult_prefix k k.val.size)) := by
  intro m
  induction m with
  | zero =>
    intro i p r hm hi_le hinv_p hinv_r
    have hi_eq : i.toNat = k.val.size := by omega
    have hi_ge : k.val.size ≤ i.toNat := by omega
    rw [multinomial_loop_oob k i p r hi_ge]
    apply congrArg RustM.ok
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_ofNat_of_lt' hfit_result, hinv_r, hi_eq]
  | succ m ih =>
    intro i p r hm hi_le hinv_p hinv_r
    by_cases hi_ge : k.val.size ≤ i.toNat
    · have hi_eq : i.toNat = k.val.size := by omega
      rw [multinomial_loop_oob k i p r hi_ge]
      apply congrArg RustM.ok
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_ofNat_of_lt' hfit_result, hinv_r, hi_eq]
    · have hi_lt : i.toNat < k.val.size := Nat.lt_of_not_le hi_ge
      -- The current slice element.
      let x := k.val[i.toNat]'hi_lt
      have hx_def : x = k.val[i.toNat]'hi_lt := rfl
      -- Bounds for sum and mult at step i + 1:
      have h_sum_succ_eq :
          sum_prefix k (i.toNat + 1) = sum_prefix k i.toNat + x.toNat := by
        show sum_prefix k i.toNat +
              (if h : i.toNat < k.val.size then (k.val[i.toNat]'h).toNat else 0) =
              sum_prefix k i.toNat + x.toNat
        rw [dif_pos hi_lt]
      have h_sum_succ_lt : sum_prefix k (i.toNat + 1) < 2 ^ 64 := by
        have : sum_prefix k (i.toNat + 1) ≤ sum_prefix k k.val.size :=
          sum_prefix_mono k (i.toNat + 1) k.val.size (by omega)
        omega
      have h_mult_succ_lt : mult_prefix k (i.toNat + 1) < 2 ^ 64 := by
        have : mult_prefix k (i.toNat + 1) ≤ mult_prefix k k.val.size :=
          mult_prefix_mono k (i.toNat + 1) k.val.size (by omega) (by omega)
        omega
      -- p + x doesn't overflow because sum_prefix k (i + 1) < 2^64.
      have hno_add : ¬ UInt64.addOverflow p x := by
        intro hov
        rw [UInt64.addOverflow_iff] at hov
        rw [hinv_p] at hov
        rw [← h_sum_succ_eq] at hov
        omega
      -- The new p value.
      have h_p_new_toNat : (p + x).toNat = sum_prefix k (i.toNat + 1) := by
        rw [UInt64.toNat_add_of_lt]
        · rw [hinv_p, ← h_sum_succ_eq]
        · rw [UInt64.addOverflow_iff] at hno_add
          omega
      -- binomial(p + x, x) returns ok (UInt64.ofNat (nchoose ...)).
      have h_nch_factor :
          nchoose (sum_prefix k (i.toNat + 1)) x.toNat ≤ mult_prefix k (i.toNat + 1) :=
        nchoose_factor_le_mult_prefix k i.toNat hi_lt
      have h_nch_factor_lt : nchoose (p + x).toNat x.toNat < 2 ^ 64 := by
        rw [h_p_new_toNat]
        exact Nat.lt_of_le_of_lt h_nch_factor h_mult_succ_lt
      have h_binom :
          multinomial_u64.binomial (p + x) x =
            RustM.ok (UInt64.ofNat (nchoose (p + x).toNat x.toNat)) :=
        binomial_postcondition_gen (p + x) x h_nch_factor_lt
      let b := UInt64.ofNat (nchoose (p + x).toNat x.toNat)
      have hb_def : b = UInt64.ofNat (nchoose (p + x).toNat x.toNat) := rfl
      have hb_toNat : b.toNat = nchoose (p + x).toNat x.toNat := by
        rw [hb_def]
        exact UInt64.toNat_ofNat_of_lt' h_nch_factor_lt
      -- r * b doesn't overflow.
      have h_rb_eq : r.toNat * b.toNat = mult_prefix k (i.toNat + 1) := by
        rw [hinv_r, hb_toNat, h_p_new_toNat]
        show mult_prefix k i.toNat * nchoose (sum_prefix k (i.toNat + 1)) x.toNat =
              mult_prefix k (i.toNat + 1)
        show _ = mult_prefix k i.toNat *
                  (if h : i.toNat < k.val.size then
                    nchoose (sum_prefix k (i.toNat + 1)) (k.val[i.toNat]'h).toNat else 1)
        rw [dif_pos hi_lt]
      have hno_mul : ¬ UInt64.mulOverflow r b := by
        intro hov
        rw [UInt64.mulOverflow_iff] at hov
        rw [h_rb_eq] at hov
        omega
      rw [multinomial_loop_recurse k i p r hi_lt hno_add b h_binom hno_mul]
      -- Now we need the new invariants for (i + 1, p + x, r * b).
      have h_size_lt : k.val.size < 2^64 := k.size_lt_usizeSize
      have h_i1_lt : i.toNat + 1 < 2^64 := by omega
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_i1_lt
      have h_new_hm : k.val.size - (i + 1).toNat ≤ m := by
        rw [h_i1_toNat]; omega
      have h_new_hi_le : (i + 1).toNat ≤ k.val.size := by
        rw [h_i1_toNat]; omega
      have h_new_hinv_p : (p + x).toNat = sum_prefix k (i + 1).toNat := by
        rw [h_i1_toNat, h_p_new_toNat]
      have h_new_hinv_r : (r * b).toNat = mult_prefix k (i + 1).toNat := by
        rw [h_i1_toNat]
        rw [UInt64.toNat_mul]
        rw [h_rb_eq]
        rw [Nat.mod_eq_of_lt h_mult_succ_lt]
      exact ih (i + 1) (p + x) (r * b) h_new_hm h_new_hi_le
        h_new_hinv_p h_new_hinv_r

/-! ## Failure step lemmas. -/

/-- At step `i < size`, if `p + k[i]` overflows, the loop fails. -/
private theorem multinomial_loop_add_fail
    (k : RustSlice u64) (i : usize) (p r : u64)
    (hi : i.toNat < k.val.size)
    (hov : UInt64.addOverflow p (k.val[i.toNat]'hi)) :
    multinomial_u64.multinomial_loop k i p r = RustM.fail Error.integerOverflow := by
  conv => lhs; unfold multinomial_u64.multinomial_loop
  have h_ofNat : (USize64.ofNat k.val.size).toNat = k.val.size :=
    USize64.toNat_ofNat_of_lt' k.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat k.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (k[i]_? : RustM u64) = RustM.ok (k.val[i.toNat]'hi) := by
    show (if h : i.toNat < k.val.size then pure (k.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (k.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_bv_true :
      BitVec.uaddOverflow p.toBitVec (k.val[i.toNat]'hi).toBitVec = true := hov
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.ops.arith.Add.add, h_bv_true]
  rfl

/-- At step `i < size`, if `p + k[i]` doesn't overflow but `binomial(p+k[i], k[i])`
    fails with error `e`, the loop fails with the same `e`. Requires `i+1` no overflow. -/
private theorem multinomial_loop_binom_fail
    (k : RustSlice u64) (i : usize) (p r : u64)
    (hi : i.toNat < k.val.size)
    (hno_add : ¬ UInt64.addOverflow p (k.val[i.toNat]'hi))
    (hi_ovf : i.toNat + 1 < 2 ^ 64)
    (e : Error)
    (hb : multinomial_u64.binomial (p + k.val[i.toNat]'hi) (k.val[i.toNat]'hi) = RustM.fail e) :
    multinomial_u64.multinomial_loop k i p r = RustM.fail e := by
  conv => lhs; unfold multinomial_u64.multinomial_loop
  have h_ofNat : (USize64.ofNat k.val.size).toNat = k.val.size :=
    USize64.toNat_ofNat_of_lt' k.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat k.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (k[i]_? : RustM u64) = RustM.ok (k.val[i.toNat]'hi) := by
    show (if h : i.toNat < k.val.size then pure (k.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (k.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_no_bv :
      BitVec.uaddOverflow p.toBitVec (k.val[i.toNat]'hi).toBitVec = false := by
    cases hb' : BitVec.uaddOverflow p.toBitVec (k.val[i.toNat]'hi).toBitVec with
    | false => rfl
    | true => exact absurd hb' hno_add
  have h_no_bv_i :
      BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hii := (USize64.uaddOverflow_iff i 1).mp hbo
      rw [usize_one_toNat] at hii
      omega
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.ops.arith.Add.add, h_no_bv, h_no_bv_i,
             hb]
  rfl

/-- At step `i < size`, if `+` and `binomial` succeed but `r * b` overflows, fail. -/
private theorem multinomial_loop_mul_fail
    (k : RustSlice u64) (i : usize) (p r : u64)
    (hi : i.toNat < k.val.size)
    (hno_add : ¬ UInt64.addOverflow p (k.val[i.toNat]'hi))
    (hi_ovf : i.toNat + 1 < 2 ^ 64)
    (b : u64)
    (hb : multinomial_u64.binomial (p + k.val[i.toNat]'hi) (k.val[i.toNat]'hi) = RustM.ok b)
    (hov : UInt64.mulOverflow r b) :
    multinomial_u64.multinomial_loop k i p r = RustM.fail Error.integerOverflow := by
  conv => lhs; unfold multinomial_u64.multinomial_loop
  have h_ofNat : (USize64.ofNat k.val.size).toNat = k.val.size :=
    USize64.toNat_ofNat_of_lt' k.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat k.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (k[i]_? : RustM u64) = RustM.ok (k.val[i.toNat]'hi) := by
    show (if h : i.toNat < k.val.size then pure (k.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (k.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_no_bv :
      BitVec.uaddOverflow p.toBitVec (k.val[i.toNat]'hi).toBitVec = false := by
    cases hb' : BitVec.uaddOverflow p.toBitVec (k.val[i.toNat]'hi).toBitVec with
    | false => rfl
    | true => exact absurd hb' hno_add
  have h_no_bv_i :
      BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hii := (USize64.uaddOverflow_iff i 1).mp hbo
      rw [usize_one_toNat] at hii
      omega
  have h_mul_bv :
      BitVec.umulOverflow r.toBitVec b.toBitVec = true := hov
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.ops.arith.Add.add, h_no_bv, h_no_bv_i,
             rust_primitives.ops.arith.Mul.mul, h_mul_bv,
             hb]
  rfl

/-! ## Non-divergence helpers (RustM α = Option (Except Error α)). -/

private theorem pure_ne_div {α : Type} (v : α) : (pure v : RustM α) ≠ RustM.div := by
  intro h
  -- `pure v` in RustM = some (.ok v), RustM.div = none. Equation impossible.
  change some (Except.ok v) = none at h
  cases h

private theorem ok_ne_div {α : Type} (v : α) : (RustM.ok v : RustM α) ≠ RustM.div := by
  intro h
  change some (Except.ok v) = none at h
  cases h

private theorem fail_ne_div {α : Type} (e : Error) : (RustM.fail e : RustM α) ≠ RustM.div := by
  intro h
  change some (Except.error e) = none at h
  cases h

/-- Bind preserves non-divergence: if `x` and `f v` (for every `v`) are not div,
    then `x >>= f` is not div. -/
private theorem bind_ne_div {α β : Type} (x : RustM α) (f : α → RustM β)
    (hx : x ≠ RustM.div) (hf : ∀ v, f v ≠ RustM.div) : (x >>= f) ≠ RustM.div := by
  intro hcon
  cases hx_case : x with
  | none => exact hx hx_case
  | some result =>
    cases result with
    | ok v =>
      -- x = ok v ⇒ x >>= f = f v
      have h_xv : x = RustM.ok v := hx_case
      have : (RustM.ok v : RustM α) >>= f = RustM.div := h_xv ▸ hcon
      have h_red : (RustM.ok v : RustM α) >>= f = f v := pure_bind v f
      rw [h_red] at this
      exact hf v this
    | error e =>
      -- x = fail e ⇒ x >>= f = fail e ≠ div
      have h_xe : x = RustM.fail e := hx_case
      have : (RustM.fail e : RustM α) >>= f = RustM.div := h_xe ▸ hcon
      -- fail e >>= f = fail e definitionally
      exact fail_ne_div e this

/-! ## Non-divergence of direct (`-?`, `+?`, `*?`, `/?`) operations on u64. -/

private theorem u64_sub_ne_div (a b : u64) : (a -? b : RustM u64) ≠ RustM.div := by
  intro h
  change (rust_primitives.ops.arith.Sub.sub a b : RustM u64) = RustM.div at h
  change (if BitVec.usubOverflow a.toBitVec b.toBitVec then
          (.fail .integerOverflow : RustM u64) else pure (a - b)) = RustM.div at h
  by_cases hov : BitVec.usubOverflow a.toBitVec b.toBitVec
  · rw [if_pos hov] at h; exact fail_ne_div _ h
  · rw [if_neg hov] at h; exact pure_ne_div _ h

private theorem u64_add_ne_div (a b : u64) : (a +? b : RustM u64) ≠ RustM.div := by
  intro h
  change (rust_primitives.ops.arith.Add.add a b : RustM u64) = RustM.div at h
  change (if BitVec.uaddOverflow a.toBitVec b.toBitVec then
          (.fail .integerOverflow : RustM u64) else pure (a + b)) = RustM.div at h
  by_cases hov : BitVec.uaddOverflow a.toBitVec b.toBitVec
  · rw [if_pos hov] at h; exact fail_ne_div _ h
  · rw [if_neg hov] at h; exact pure_ne_div _ h

private theorem u64_mul_ne_div (a b : u64) : (a *? b : RustM u64) ≠ RustM.div := by
  intro h
  change (rust_primitives.ops.arith.Mul.mul a b : RustM u64) = RustM.div at h
  change (if BitVec.umulOverflow a.toBitVec b.toBitVec then
          (.fail .integerOverflow : RustM u64) else pure (a * b)) = RustM.div at h
  by_cases hov : BitVec.umulOverflow a.toBitVec b.toBitVec
  · rw [if_pos hov] at h; exact fail_ne_div _ h
  · rw [if_neg hov] at h; exact pure_ne_div _ h

private theorem u64_div_ne_div (a b : u64) : (a /? b : RustM u64) ≠ RustM.div := by
  intro h
  change (rust_primitives.ops.arith.Div.div a b : RustM u64) = RustM.div at h
  change (if b = 0 then (.fail .divisionByZero : RustM u64) else pure (a / b)) = RustM.div at h
  by_cases hbz : b = 0
  · rw [if_pos hbz] at h; exact fail_ne_div _ h
  · rw [if_neg hbz] at h; exact pure_ne_div _ h

/-! ## Non-divergence of `multiply_and_divide` (built from total ops + total `gcd`). -/

private theorem multiply_and_divide_not_div (r a b : u64) :
    multinomial_u64.multiply_and_divide r a b ≠ RustM.div := by
  unfold multinomial_u64.multiply_and_divide
  rw [gcd_spec r b]
  simp only [RustM_ok_bind]
  -- Goal: (r /? g) >>= fun r' => (b /? g) >>= fun b' => (a /? b') >>= fun a' => (r' *? a') ≠ div
  -- where g = UInt64.ofNat (Nat.gcd r.toNat b.toNat).
  -- The do-block desugars to nested binds. Each step is a direct op, hence ≠ div.
  apply bind_ne_div
  · exact u64_div_ne_div r _
  · intro r'
    apply bind_ne_div
    · exact u64_div_ne_div b _
    · intro b'
      apply bind_ne_div
      · exact u64_div_ne_div a _
      · intro a'
        exact u64_mul_ne_div r' a'

/-! ## Non-divergence of `binomial_loop` (strong induction on the measure).
    The trick: don't abstract the bound variables via bind_ne_div on the
    chain, because we need to know `d' = d + 1` to apply the IH. Instead,
    do explicit `by_cases` on each overflow condition. -/

private theorem binomial_loop_not_div :
    ∀ (n k d r : u64), multinomial_u64.binomial_loop n k d r ≠ RustM.div := by
  intro n k d r
  induction h_m : (k.toNat + 1 - d.toNat) using Nat.strongRecOn generalizing n d r with
  | _ M ih =>
    unfold multinomial_u64.binomial_loop
    have h_gt_eqq : (d >? k : RustM Bool) = pure (decide (d > k)) := rfl
    rw [h_gt_eqq]
    simp only [pure_bind]
    by_cases hdk : d > k
    · rw [decide_eq_true hdk]
      simp only [if_true]
      exact pure_ne_div _
    · rw [decide_eq_false hdk]
      simp only [Bool.false_eq_true, if_false]
      have hdk_nat : d.toNat ≤ k.toNat := by
        rcases Nat.lt_or_ge k.toNat d.toNat with h | h
        · exfalso; apply hdk; exact UInt64.lt_iff_toNat_lt.mpr h
        · exact h
      -- n -? 1: case split on overflow.
      by_cases h_sub_ov : BitVec.usubOverflow n.toBitVec (1 : u64).toBitVec
      · -- n -? 1 fails. Whole chain reduces to fail.
        have h_sub_eq : (n -? (1 : u64) : RustM u64) = RustM.fail .integerOverflow := by
          show (rust_primitives.ops.arith.Sub.sub n (1 : u64) : RustM u64) = _
          show (if BitVec.usubOverflow n.toBitVec (1 : u64).toBitVec then
                  (.fail .integerOverflow : RustM u64) else pure (n - 1)) = _
          rw [if_pos h_sub_ov]
        rw [h_sub_eq]
        -- (RustM.fail e >>= ...) reduces to RustM.fail e definitionally.
        change RustM.fail Error.integerOverflow ≠ RustM.div
        exact fail_ne_div _
      · -- n -? 1 succeeds with n - 1.
        have h_sub_eq : (n -? (1 : u64) : RustM u64) = pure (n - 1) := by
          show (rust_primitives.ops.arith.Sub.sub n (1 : u64) : RustM u64) = _
          show (if BitVec.usubOverflow n.toBitVec (1 : u64).toBitVec then
                  (.fail .integerOverflow : RustM u64) else pure (n - 1)) = _
          rw [if_neg h_sub_ov]
        rw [h_sub_eq]
        simp only [pure_bind]
        -- d +? 1: case split.
        by_cases h_add_ov : BitVec.uaddOverflow d.toBitVec (1 : u64).toBitVec
        · -- fails
          have h_add_eq : (d +? (1 : u64) : RustM u64) = RustM.fail .integerOverflow := by
            show (rust_primitives.ops.arith.Add.add d (1 : u64) : RustM u64) = _
            show (if BitVec.uaddOverflow d.toBitVec (1 : u64).toBitVec then
                    (.fail .integerOverflow : RustM u64) else pure (d + 1)) = _
            rw [if_pos h_add_ov]
          rw [h_add_eq]
          change RustM.fail Error.integerOverflow ≠ RustM.div
          exact fail_ne_div _
        · -- succeeds
          have h_add_eq : (d +? (1 : u64) : RustM u64) = pure (d + 1) := by
            show (rust_primitives.ops.arith.Add.add d (1 : u64) : RustM u64) = _
            show (if BitVec.uaddOverflow d.toBitVec (1 : u64).toBitVec then
                    (.fail .integerOverflow : RustM u64) else pure (d + 1)) = _
            rw [if_neg h_add_ov]
          rw [h_add_eq]
          simp only [pure_bind]
          -- multiply_and_divide r n d: case split on result.
          cases h_mad : multinomial_u64.multiply_and_divide r n d with
          | none =>
            -- multiply_and_divide returned div — contradiction.
            exact absurd h_mad (multiply_and_divide_not_div r n d)
          | some res =>
            cases res with
            | ok rn =>
              -- After cases, goal: (some (.ok rn) >>= ...) ≠ div, which reduces
              -- to binomial_loop (n - 1) k (d + 1) rn ≠ div.
              change multinomial_u64.binomial_loop (n - 1) k (d + 1) rn ≠ RustM.div
              -- Apply IH with measure (k - (d+1) + 1) < M.
              -- We need d.toNat + 1 < 2^64 to compute (d+1).toNat. The fact
              -- h_add_ov tells us d +? 1 didn't overflow, so this holds.
              have h_no_ov : d.toNat + 1 < 2 ^ 64 := by
                have ho : ¬ UInt64.addOverflow d (1 : u64) = true := h_add_ov
                rw [UInt64.addOverflow_iff] at ho
                have h1 : (1 : u64).toNat = 1 := rfl
                omega
              have h_dp1_toNat : (d + 1).toNat = d.toNat + 1 := by
                apply UInt64.toNat_add_of_lt
                show d.toNat + (1 : u64).toNat < 2 ^ 64
                have h1 : (1 : u64).toNat = 1 := rfl
                omega
              have h_meas : k.toNat + 1 - (d + 1).toNat < M := by
                rw [h_dp1_toNat, ← h_m]; omega
              exact ih (k.toNat + 1 - (d + 1).toNat) h_meas (n - 1) (d + 1) rn rfl
            | error e =>
              -- After cases, goal: (some (.error e) >>= ...) ≠ div, reduces to fail e ≠ div.
              change RustM.fail e ≠ RustM.div
              exact fail_ne_div e

/-! ## Non-divergence of `binomial` (top-level). -/

private theorem binomial_not_div :
    ∀ (n k : u64), multinomial_u64.binomial n k ≠ RustM.div := by
  intro n k
  induction h_m : k.toNat using Nat.strongRecOn generalizing k with
  | _ K ih =>
    unfold multinomial_u64.binomial
    have h_gt_eqq : (k >? n : RustM Bool) = pure (decide (k > n)) := rfl
    rw [h_gt_eqq]
    simp only [pure_bind]
    by_cases hkn : k > n
    · rw [decide_eq_true hkn]
      simp only [if_true]
      exact pure_ne_div _
    · rw [decide_eq_false hkn]
      simp only [Bool.false_eq_true, if_false]
      have hk_le_n : k.toNat ≤ n.toNat := by
        rcases Nat.lt_or_ge n.toNat k.toNat with h | h
        · exfalso; apply hkn; exact UInt64.lt_iff_toNat_lt.mpr h
        · exact h
      have h_sub_no_ov : BitVec.usubOverflow n.toBitVec k.toBitVec = false := by
        cases h_eq : BitVec.usubOverflow n.toBitVec k.toBitVec with
        | false => rfl
        | true =>
          exfalso
          have : UInt64.subOverflow n k = true := h_eq
          rw [UInt64.subOverflow_iff] at this
          omega
      have h_sub_eq : (n -? k : RustM u64) = pure (n - k) := by
        show (rust_primitives.ops.arith.Sub.sub n k : RustM u64) = pure (n - k)
        show (if BitVec.usubOverflow n.toBitVec k.toBitVec then
                (.fail .integerOverflow : RustM u64) else pure (n - k)) = pure (n - k)
        rw [h_sub_no_ov]; rfl
      rw [h_sub_eq]
      simp only [pure_bind]
      have h_n_sub_toNat : (n - k).toNat = n.toNat - k.toNat :=
        UInt64.toNat_sub_of_le' hk_le_n
      have h_gt2 : (k >? (n - k) : RustM Bool) = pure (decide (k > n - k)) := rfl
      rw [h_gt2]
      simp only [pure_bind]
      by_cases hk_gt : k > n - k
      · rw [decide_eq_true hk_gt]
        simp only [if_true]
        have hk_gt_nat : (n - k).toNat < k.toNat := UInt64.lt_iff_toNat_lt.mp hk_gt
        have hk_gt_K : (n - k).toNat < K := h_m ▸ hk_gt_nat
        exact ih (n - k).toNat hk_gt_K (n - k) rfl
      · rw [decide_eq_false hk_gt]
        simp only [Bool.false_eq_true, if_false]
        exact binomial_loop_not_div n k 1 1

/-! ## Auxiliary failure-induction lemma. -/

private theorem multinomial_loop_fails_aux (k : RustSlice u64) :
    ∀ (m : Nat) (i : usize) (p r : u64),
      k.val.size - i.toNat ≤ m →
      i.toNat ≤ k.val.size →
      p.toNat = sum_prefix k i.toNat →
      2 ^ 64 ≤ sum_prefix k k.val.size →
      ∃ e, multinomial_u64.multinomial_loop k i p r = RustM.fail e := by
  intro m
  induction m with
  | zero =>
    intro i p r hm hi_le hinv hov
    -- i.toNat = size and p.toNat = sum ≥ 2^64, but p.toNat < 2^64. Contradiction.
    have hi_eq : i.toNat = k.val.size := by omega
    have hp_lt : p.toNat < 2 ^ 64 := UInt64.toNat_lt p
    have hp_ge : p.toNat ≥ 2 ^ 64 := by rw [hinv, hi_eq]; exact hov
    omega
  | succ m ih =>
    intro i p r hm hi_le hinv hov
    by_cases hi_ge : k.val.size ≤ i.toNat
    · have hi_eq : i.toNat = k.val.size := by omega
      have hp_lt : p.toNat < 2 ^ 64 := UInt64.toNat_lt p
      have hp_ge : p.toNat ≥ 2 ^ 64 := by rw [hinv, hi_eq]; exact hov
      omega
    · have hi_lt : i.toNat < k.val.size := Nat.lt_of_not_le hi_ge
      let x := k.val[i.toNat]'hi_lt
      have hx_def : x = k.val[i.toNat]'hi_lt := rfl
      by_cases hadd : UInt64.addOverflow p x
      · -- Add overflows.
        exact ⟨_, multinomial_loop_add_fail k i p r hi_lt hadd⟩
      · -- Add doesn't overflow.
        have h_p_new_toNat : (p + x).toNat = sum_prefix k (i.toNat + 1) := by
          rw [UInt64.toNat_add_of_lt]
          · rw [hinv]
            show sum_prefix k i.toNat + x.toNat = sum_prefix k (i.toNat + 1)
            show sum_prefix k i.toNat + x.toNat =
                  sum_prefix k i.toNat +
                    (if h : i.toNat < k.val.size then (k.val[i.toNat]'h).toNat else 0)
            rw [dif_pos hi_lt]
          · rw [UInt64.addOverflow_iff] at hadd; omega
        have h_size_lt : k.val.size < 2^64 := k.size_lt_usizeSize
        have h_i1_lt : i.toNat + 1 < 2^64 := by omega
        -- Case-split on the binomial result.
        cases hb_res : multinomial_u64.binomial (p + x) x with
        | none =>
          -- binomial returned RustM.div (= none). Use binomial_not_div.
          exact absurd hb_res (binomial_not_div (p + x) x)
        | some result =>
          cases result with
          | ok bval =>
            -- binomial succeeded with bval; check r * bval.
            by_cases hmul : UInt64.mulOverflow r bval
            · -- Mul overflows.
              exact ⟨_, multinomial_loop_mul_fail k i p r hi_lt hadd h_i1_lt
                        bval hb_res hmul⟩
            · -- Mul doesn't overflow; recurse.
              rw [multinomial_loop_recurse k i p r hi_lt hadd bval hb_res hmul]
              -- Apply IH at (i + 1, p + x, r * bval).
              have h_i1_toNat : (i + 1).toNat = i.toNat + 1 :=
                usize_add_one_toNat i h_i1_lt
              have h_new_hm : k.val.size - (i + 1).toNat ≤ m := by
                rw [h_i1_toNat]; omega
              have h_new_hi_le : (i + 1).toNat ≤ k.val.size := by
                rw [h_i1_toNat]; omega
              have h_new_hinv : (p + x).toNat = sum_prefix k (i + 1).toNat := by
                rw [h_i1_toNat]; exact h_p_new_toNat
              exact ih (i + 1) (p + x) (r * bval) h_new_hm h_new_hi_le h_new_hinv hov
          | error e =>
            -- binomial failed with e.
            exact ⟨e, multinomial_loop_binom_fail k i p r hi_lt hadd h_i1_lt e hb_res⟩

/-! ## The top-level theorems. -/

/-- Boundary contract: `multinomial(&[])` is the empty product, 1. -/
theorem multinomial_empty_returns_one
    (k : RustSlice u64) (hempty : k.val.size = 0) :
    multinomial_u64.multinomial k = RustM.ok (1 : u64) := by
  unfold multinomial_u64.multinomial
  have hi_ge : k.val.size ≤ (0 : usize).toNat := by
    show k.val.size ≤ 0
    omega
  exact multinomial_loop_oob k (0 : usize) (0 : u64) (1 : u64) hi_ge

/-- Boundary contract: a singleton `&[n]` returns 1. -/
theorem multinomial_singleton_returns_one
    (k : RustSlice u64) (hsing : k.val.size = 1) :
    multinomial_u64.multinomial k = RustM.ok (1 : u64) := by
  unfold multinomial_u64.multinomial
  -- multinomial_loop k 0 0 1, with size = 1.
  -- Step: x = k[0], p = 0, p + x = x, binomial(x, x) = 1, r * 1 = 1.
  have h0_lt : (0 : usize).toNat < k.val.size := by
    show 0 < k.val.size; omega
  let x := k.val[(0 : usize).toNat]'h0_lt
  have hx_def : x = k.val[(0 : usize).toNat]'h0_lt := rfl
  -- ¬ UInt64.addOverflow 0 x
  have hno_add : ¬ UInt64.addOverflow (0 : u64) x := by
    intro hov
    rw [UInt64.addOverflow_iff] at hov
    have h0 : (0 : u64).toNat = 0 := rfl
    have hx_lt : x.toNat < 2 ^ 64 := UInt64.toNat_lt x
    omega
  have h_p_new : (0 : u64) + x = x := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add_of_lt]
    · show (0 : u64).toNat + x.toNat = x.toNat
      have h0 : (0 : u64).toNat = 0 := rfl
      omega
    · rw [UInt64.addOverflow_iff] at hno_add
      have h0 : (0 : u64).toNat = 0 := rfl
      have hx_lt : x.toNat < 2 ^ 64 := UInt64.toNat_lt x
      omega
  -- binomial(x, x) = 1.
  have h_binom : multinomial_u64.binomial ((0 : u64) + x) x = RustM.ok (1 : u64) := by
    rw [h_p_new]
    exact binomial_k_eq_n x
  -- r * 1 = 1.
  have hno_mul : ¬ UInt64.mulOverflow (1 : u64) (1 : u64) := by
    intro hov
    rw [UInt64.mulOverflow_iff] at hov
    have h1 : (1 : u64).toNat = 1 := rfl
    rw [h1] at hov
    omega
  rw [multinomial_loop_recurse k (0 : usize) (0 : u64) (1 : u64) h0_lt hno_add
        (1 : u64) h_binom hno_mul]
  -- Now multinomial_loop k 1 (0 + x) (1 * 1) = multinomial_loop k 1 x 1.
  -- This should be OOB since (1 : usize).toNat = 1 = k.val.size.
  have h_oob : k.val.size ≤ ((0 : usize) + 1).toNat := by
    have h1 : ((0 : usize) + 1).toNat = 1 := by
      rw [usize_add_one_toNat]
      · rfl
      · show (0 : usize).toNat + 1 < 2 ^ 64
        decide
    rw [h1]; omega
  rw [multinomial_loop_oob k ((0 : usize) + 1) ((0 : u64) + x) ((1 : u64) * (1 : u64)) h_oob]
  apply congrArg RustM.ok
  apply UInt64.toNat_inj.mp
  show ((1 : u64) * (1 : u64)).toNat = (1 : u64).toNat
  rw [UInt64.toNat_mul]
  rfl

/-- Closed-form postcondition. -/
theorem multinomial_closed_form (k : RustSlice u64)
    (hfit_sum    : sum_prefix  k k.val.size < 2 ^ 64)
    (hfit_result : mult_prefix k k.val.size < 2 ^ 64) :
    multinomial_u64.multinomial k =
      RustM.ok (UInt64.ofNat (mult_prefix k k.val.size)) := by
  unfold multinomial_u64.multinomial
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_inv_p : (0 : u64).toNat = sum_prefix k (0 : usize).toNat := by
    rw [h_zero_toNat]; rfl
  have h_inv_r : (1 : u64).toNat = mult_prefix k (0 : usize).toNat := by
    rw [h_zero_toNat]; rfl
  exact multinomial_loop_correct k hfit_sum hfit_result k.val.size
    (0 : usize) (0 : u64) (1 : u64)
    (by rw [h_zero_toNat]; omega)
    (by rw [h_zero_toNat]; omega)
    h_inv_p h_inv_r

/-- Failure clause: when the integer running sum exceeds the `u64` range
    (i.e. `2 ^ 64 ≤ sum_prefix k k.val.size`), the unchecked `p + k[i]`
    addition in the loop body overflows and the function fails with an
    integer-overflow error. Captures the `sum_overflow_panics` test. -/
theorem multinomial_overflow_fails (k : RustSlice u64)
    (hov : 2 ^ 64 ≤ sum_prefix k k.val.size) :
    ∃ e, multinomial_u64.multinomial k = RustM.fail e := by
  unfold multinomial_u64.multinomial
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  exact multinomial_loop_fails_aux k k.val.size (0 : usize) (0 : u64) (1 : u64)
    (by rw [h_zero_toNat]; omega)
    (by rw [h_zero_toNat]; omega)
    (by rw [h_zero_toNat]; rfl)
    hov

/-! ## Permutation infrastructure: factorial closed form for `mult_prefix`. -/

/-- Standard factorial. -/
private def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

private theorem factorial_pos : ∀ n, 0 < factorial n
  | 0 => by decide
  | n + 1 => by
    show 0 < (n + 1) * factorial n
    have := factorial_pos n
    exact Nat.mul_pos (by omega) this

/-- Binomial identity: `k! * (n - k)! * C(n, k) = n!` for `k ≤ n`. -/
private theorem factorial_nchoose_eq : ∀ n k, k ≤ n →
    factorial k * factorial (n - k) * nchoose n k = factorial n
  | n, 0, _ => by
    show factorial 0 * factorial (n - 0) * nchoose n 0 = factorial n
    rw [nchoose_zero, Nat.sub_zero]
    show 1 * factorial n * 1 = factorial n
    rw [Nat.one_mul, Nat.mul_one]
  | 0, k + 1, h => by omega
  | n + 1, k + 1, h => by
    have hk : k ≤ n := by omega
    show factorial (k + 1) * factorial (n + 1 - (k + 1)) * (nchoose n k + nchoose n (k + 1)) =
      factorial (n + 1)
    have hsub : n + 1 - (k + 1) = n - k := by omega
    rw [hsub]
    rw [Nat.mul_add]
    have ih1 := factorial_nchoose_eq n k hk
    -- factorial (k + 1) = (k + 1) * factorial k by def
    have hfact_kp1 : factorial (k + 1) = (k + 1) * factorial k := rfl
    have h_term1 : factorial (k + 1) * factorial (n - k) * nchoose n k =
                    (k + 1) * factorial n := by
      rw [hfact_kp1, Nat.mul_assoc (k + 1) (factorial k) (factorial (n - k)),
          Nat.mul_assoc (k + 1) (factorial k * factorial (n - k)) (nchoose n k), ih1]
    by_cases hkn : k + 1 ≤ n
    · have ih2 := factorial_nchoose_eq n (k + 1) hkn
      have h_n_sub : n - k = (n - (k + 1)) + 1 := by omega
      have h_term2 : factorial (k + 1) * factorial (n - k) * nchoose n (k + 1) =
                      (n - k) * factorial n := by
        rw [h_n_sub]
        have hfact_succ : factorial ((n - (k + 1)) + 1) =
                           ((n - (k + 1)) + 1) * factorial (n - (k + 1)) := rfl
        rw [hfact_succ]
        -- Show: factorial (k+1) * (((n - (k+1)) + 1) * factorial (n - (k+1))) * nchoose n (k+1)
        --       = ((n - (k+1)) + 1) * factorial n
        -- Strategy: rewrite to ((n - (k+1)) + 1) * (factorial (k+1) * factorial (n - (k+1)) * nchoose n (k+1))
        -- then apply ih2.
        have step : factorial (k + 1) * ((n - (k + 1) + 1) * factorial (n - (k + 1))) *
                    nchoose n (k + 1) =
                    (n - (k + 1) + 1) *
                    (factorial (k + 1) * factorial (n - (k + 1)) * nchoose n (k + 1)) := by
          rw [← Nat.mul_assoc (factorial (k + 1)) ((n - (k + 1)) + 1) _,
              Nat.mul_comm (factorial (k + 1)) ((n - (k + 1)) + 1),
              Nat.mul_assoc ((n - (k + 1)) + 1) (factorial (k + 1)) _,
              Nat.mul_assoc ((n - (k + 1)) + 1) (factorial (k + 1) * factorial (n - (k + 1))) _]
        rw [step, ih2]
      rw [h_term1, h_term2]
      show (k + 1) * factorial n + (n - k) * factorial n = factorial (n + 1)
      have h_sum : (k + 1) + (n - k) = n + 1 := by omega
      rw [← Nat.add_mul, h_sum]
      rfl
    · have hk_eq : k = n := by omega
      have hn_sub : nchoose n (k + 1) = 0 := by
        apply nchoose_eq_zero_of_lt
        omega
      have h_term2 : factorial (k + 1) * factorial (n - k) * nchoose n (k + 1) = 0 := by
        rw [hn_sub, Nat.mul_zero]
      rw [h_term1, h_term2]
      show (k + 1) * factorial n + 0 = factorial (n + 1)
      rw [Nat.add_zero]
      rw [hk_eq]
      rfl

/-- The denominator: product of factorials of slice elements (as Nats). -/
private def denom_prefix (k : RustSlice u64) : Nat → Nat
  | 0     => 1
  | i + 1 =>
      denom_prefix k i *
        (if h : i < k.val.size then factorial (k.val[i]'h).toNat else 1)

private theorem denom_prefix_pos (k : RustSlice u64) :
    ∀ i, 0 < denom_prefix k i
  | 0 => Nat.zero_lt_one
  | i + 1 => by
    show 0 < denom_prefix k i *
          (if h : i < k.val.size then factorial (k.val[i]'h).toNat else 1)
    by_cases hi : i < k.val.size
    · rw [dif_pos hi]
      exact Nat.mul_pos (denom_prefix_pos k i) (factorial_pos _)
    · rw [dif_neg hi]
      rw [Nat.mul_one]
      exact denom_prefix_pos k i

/-- The telescoping closed form: `mult_prefix * denom = sum_factorial`. -/
private theorem mult_prefix_denom_eq (k : RustSlice u64) :
    ∀ i, i ≤ k.val.size →
      mult_prefix k i * denom_prefix k i = factorial (sum_prefix k i)
  | 0, _ => by
    show 1 * 1 = factorial 0
    decide
  | i + 1, hi => by
    have hi' : i ≤ k.val.size := by omega
    have hi_lt : i < k.val.size := by omega
    have ih := mult_prefix_denom_eq k i hi'
    -- LHS = mult_prefix k (i+1) * denom_prefix k (i+1)
    --     = (mult_prefix k i * nchoose s_{i+1} k_i) * (denom_prefix k i * k_i!)
    --     = (mult_prefix k i * denom_prefix k i) * (nchoose s_{i+1} k_i * k_i!)
    --     = s_i! * (nchoose s_{i+1} k_i * k_i!)
    --     = s_i! * (s_{i+1}! / s_i!) using the binomial identity
    --     = s_{i+1}!
    show (mult_prefix k i *
          (if h : i < k.val.size then nchoose (sum_prefix k (i + 1)) (k.val[i]'h).toNat else 1)) *
         (denom_prefix k i *
          (if h : i < k.val.size then factorial (k.val[i]'h).toNat else 1))
         = factorial (sum_prefix k (i + 1))
    rw [dif_pos hi_lt, dif_pos hi_lt]
    have hxi_le : (k.val[i]'hi_lt).toNat ≤ sum_prefix k (i + 1) := by
      show (k.val[i]'hi_lt).toNat ≤ sum_prefix k i + _
      show (k.val[i]'hi_lt).toNat ≤ sum_prefix k i +
            (if h : i < k.val.size then (k.val[i]'h).toNat else 0)
      rw [dif_pos hi_lt]; omega
    have h_n_sub : sum_prefix k (i + 1) - (k.val[i]'hi_lt).toNat = sum_prefix k i := by
      show sum_prefix k i + (if h : i < k.val.size then (k.val[i]'h).toNat else 0)
          - (k.val[i]'hi_lt).toNat = sum_prefix k i
      rw [dif_pos hi_lt]; omega
    have h_id :
        factorial (k.val[i]'hi_lt).toNat * factorial (sum_prefix k i) *
        nchoose (sum_prefix k (i + 1)) (k.val[i]'hi_lt).toNat =
        factorial (sum_prefix k (i + 1)) := by
      have := factorial_nchoose_eq (sum_prefix k (i + 1)) (k.val[i]'hi_lt).toNat hxi_le
      rw [h_n_sub] at this
      exact this
    -- Now goal: (mp_i * C(s, k_i)) * (dp_i * k_i!) = s!
    -- Rearrange: (mp_i * dp_i) * (C(s, k_i) * k_i!)
    -- Abbreviations
    -- A := mult_prefix k i, B := nchoose s_{i+1} k_i, C := denom_prefix k i,
    -- D := factorial k_i, E := factorial s_i, F := factorial s_{i+1}
    -- ih: A * C = E, h_id: D * E * B = F
    -- Goal: (A * B) * (C * D) = F
    -- = A * C * (B * D)  [reassociate]
    -- = E * (B * D)
    -- = D * E * B  [rearrange]
    -- = F
    have step1 : (mult_prefix k i * nchoose (sum_prefix k (i + 1)) (k.val[i]'hi_lt).toNat) *
          (denom_prefix k i * factorial (k.val[i]'hi_lt).toNat) =
          (mult_prefix k i * denom_prefix k i) *
            (factorial (k.val[i]'hi_lt).toNat *
              nchoose (sum_prefix k (i + 1)) (k.val[i]'hi_lt).toNat) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [step1, ih]
    -- Goal: factorial s_i * (k_i! * C(s_{i+1}, k_i)) = factorial s_{i+1}
    have step2 : factorial (sum_prefix k i) *
          (factorial (k.val[i]'hi_lt).toNat *
            nchoose (sum_prefix k (i + 1)) (k.val[i]'hi_lt).toNat) =
          factorial (k.val[i]'hi_lt).toNat * factorial (sum_prefix k i) *
            nchoose (sum_prefix k (i + 1)) (k.val[i]'hi_lt).toNat := by
      simp [Nat.mul_assoc, Nat.mul_comm]
    rw [step2]
    exact h_id

/-! ## List-based mult and connection to mult_prefix. -/

/-- Multinomial coefficient on a `List Nat`. Defined left-to-right (matching
    `mult_prefix`'s prefix-scan structure), but proven equivalent to the
    permutation-invariant factorial form. -/
private def mult_list : List Nat → Nat
  | [] => 1
  | x :: xs => nchoose (x + xs.sum) x * mult_list xs

/-- List product of factorials. -/
private def list_factorial_prod : List Nat → Nat
  | [] => 1
  | x :: xs => factorial x * list_factorial_prod xs

private theorem list_factorial_prod_pos : ∀ L, 0 < list_factorial_prod L
  | [] => by decide
  | x :: xs => by
    show 0 < factorial x * list_factorial_prod xs
    exact Nat.mul_pos (factorial_pos x) (list_factorial_prod_pos xs)

/-- The list closed form. -/
private theorem mult_list_closed_form : ∀ L : List Nat,
    mult_list L * list_factorial_prod L = factorial L.sum
  | [] => by decide
  | x :: xs => by
    show nchoose (x + xs.sum) x * mult_list xs * (factorial x * list_factorial_prod xs) =
          factorial (x + xs.sum)
    have h_le : x ≤ x + xs.sum := Nat.le_add_right _ _
    have h_sub : x + xs.sum - x = xs.sum := by omega
    have hid := factorial_nchoose_eq (x + xs.sum) x h_le
    rw [h_sub] at hid
    -- hid : factorial x * factorial xs.sum * nchoose (x + xs.sum) x = factorial (x + xs.sum)
    have ih := mult_list_closed_form xs
    -- ih: mult_list xs * list_factorial_prod xs = factorial xs.sum
    -- Goal: C(x+s, x) * ML * (x! * LP) = factorial(x + s)
    -- Use simp to put both sides in AC normal form, then conclude.
    have step1 : nchoose (x + xs.sum) x * mult_list xs *
          (factorial x * list_factorial_prod xs) =
          factorial x * (mult_list xs * list_factorial_prod xs) *
            nchoose (x + xs.sum) x := by
      simp [Nat.mul_assoc, Nat.mul_comm]
    rw [step1, ih]
    -- Goal: x! * factorial s * C(x+s, x) = factorial (x + s)
    exact hid

/-- List sum is permutation-invariant. -/
private theorem list_sum_perm_invariant {L L' : List Nat} (h : L.Perm L') :
    L.sum = L'.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    simp [List.sum_cons, ih]
  | swap x y l =>
    simp [List.sum_cons]
    omega
  | trans _ _ ih1 ih2 =>
    exact ih1.trans ih2

private theorem list_factorial_prod_perm_invariant {L L' : List Nat} (h : L.Perm L') :
    list_factorial_prod L = list_factorial_prod L' := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    show factorial x * _ = factorial x * _
    rw [ih]
  | swap x y l =>
    show factorial y * (factorial x * list_factorial_prod l) =
          factorial x * (factorial y * list_factorial_prod l)
    rw [← Nat.mul_assoc (factorial y) (factorial x) _,
        Nat.mul_comm (factorial y) (factorial x),
        Nat.mul_assoc (factorial x) (factorial y) _]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Permutation invariance of `mult_list`, derived from the closed form. -/
private theorem mult_list_perm_invariant {L L' : List Nat} (h : L.Perm L') :
    mult_list L = mult_list L' := by
  have hsum := list_sum_perm_invariant h
  have hprod := list_factorial_prod_perm_invariant h
  have hL := mult_list_closed_form L
  have hL' := mult_list_closed_form L'
  -- mult_list L * list_factorial_prod L = factorial L.sum
  -- mult_list L' * list_factorial_prod L' = factorial L'.sum = factorial L.sum
  rw [← hsum] at hL'
  -- mult_list L' * list_factorial_prod L' = factorial L.sum
  rw [← hprod] at hL'
  -- mult_list L' * list_factorial_prod L = factorial L.sum
  rw [← hL] at hL'
  -- mult_list L' * list_factorial_prod L = mult_list L * list_factorial_prod L
  have hpos : 0 < list_factorial_prod L := list_factorial_prod_pos L
  exact (Nat.eq_of_mul_eq_mul_right hpos hL').symm

/-- Bridge: `(l.take (i+1)).map f = (l.take i).map f ++ [f l[i]]` for `i < l.length`. -/
private theorem map_take_succ {α β} (f : α → β) (l : List α) (i : Nat)
    (hi : i < l.length) :
    (l.take (i + 1)).map f = (l.take i).map f ++ [f (l[i]'hi)] := by
  rw [List.take_add_one]
  -- l.take (i+1) = l.take i ++ l[i]?.toList
  have h_some : l[i]? = some (l[i]'hi) := List.getElem?_eq_getElem hi
  rw [h_some]
  -- (some x).toList = [x]
  show (l.take i ++ [l[i]'hi]).map f = (l.take i).map f ++ [f (l[i]'hi)]
  rw [List.map_append, List.map_cons, List.map_nil]

/-- Bridge: `sum_prefix k i = ((k.val.toList.take i).map UInt64.toNat).sum` for `i ≤ size`. -/
private theorem sum_prefix_eq_take_sum (k : RustSlice u64) :
    ∀ i, i ≤ k.val.size →
      sum_prefix k i = ((k.val.toList.take i).map UInt64.toNat).sum
  | 0, _ => by
    show (0 : Nat) = ((k.val.toList.take 0).map UInt64.toNat).sum
    rw [List.take_zero, List.map_nil, List.sum_nil]
  | i + 1, hi => by
    have hi_lt : i < k.val.size := by omega
    have hi_lt_list : i < k.val.toList.length := by
      rw [Array.length_toList]; exact hi_lt
    have ih := sum_prefix_eq_take_sum k i (by omega)
    show sum_prefix k i + (if h : i < k.val.size then (k.val[i]'h).toNat else 0) =
          ((k.val.toList.take (i + 1)).map UInt64.toNat).sum
    rw [dif_pos hi_lt, ih]
    rw [map_take_succ UInt64.toNat k.val.toList i hi_lt_list]
    rw [List.sum_append]
    -- Need k.val.toList[i] = k.val[i]
    have h_eq : k.val.toList[i]'hi_lt_list = k.val[i]'hi_lt := by
      rw [Array.getElem_toList]
      rfl
    show _ + (k.val[i]'hi_lt).toNat =
          ((k.val.toList.take i).map UInt64.toNat).sum +
          [UInt64.toNat (k.val.toList[i]'hi_lt_list)].sum
    show _ + (k.val[i]'hi_lt).toNat =
          ((k.val.toList.take i).map UInt64.toNat).sum +
          (UInt64.toNat (k.val.toList[i]'hi_lt_list) + 0)
    rw [Nat.add_zero, h_eq]

/-- Bridge: `denom_prefix k i = list_factorial_prod ((k.val.toList.take i).map UInt64.toNat)`. -/
private theorem denom_prefix_eq_take_lfp (k : RustSlice u64) :
    ∀ i, i ≤ k.val.size →
      denom_prefix k i =
        list_factorial_prod ((k.val.toList.take i).map UInt64.toNat)
  | 0, _ => by
    show (1 : Nat) = list_factorial_prod ((k.val.toList.take 0).map UInt64.toNat)
    rw [List.take_zero, List.map_nil]
    rfl
  | i + 1, hi => by
    have hi_lt : i < k.val.size := by omega
    have hi_lt_list : i < k.val.toList.length := by
      rw [Array.length_toList]; exact hi_lt
    have ih := denom_prefix_eq_take_lfp k i (by omega)
    show denom_prefix k i *
          (if h : i < k.val.size then factorial (k.val[i]'h).toNat else 1) =
          list_factorial_prod ((k.val.toList.take (i + 1)).map UInt64.toNat)
    rw [dif_pos hi_lt, ih]
    rw [map_take_succ UInt64.toNat k.val.toList i hi_lt_list]
    -- list_factorial_prod (xs ++ [x]) = list_factorial_prod xs * factorial x
    have h_lfp_append : ∀ (xs : List Nat) (x : Nat),
        list_factorial_prod (xs ++ [x]) = list_factorial_prod xs * factorial x := by
      intro xs x
      induction xs with
      | nil => 
        show factorial x * 1 = 1 * factorial x
        rw [Nat.mul_one, Nat.one_mul]
      | cons y ys ih =>
        show factorial y * list_factorial_prod (ys ++ [x]) =
              factorial y * list_factorial_prod ys * factorial x
        rw [ih, Nat.mul_assoc]
    rw [h_lfp_append]
    have h_eq : k.val.toList[i]'hi_lt_list = k.val[i]'hi_lt := by
      rw [Array.getElem_toList]
      rfl
    rw [h_eq]

/-- Connection: `mult_prefix k k.val.size` equals `mult_list` on the underlying
    list of nats. -/
private theorem mult_prefix_eq_mult_list (k : RustSlice u64) :
    mult_prefix k k.val.size = mult_list (k.val.toList.map UInt64.toNat) := by
  have hL := mult_list_closed_form (k.val.toList.map UInt64.toNat)
  have hP := mult_prefix_denom_eq k k.val.size (Nat.le_refl _)
  -- Show: sum_prefix k size = (toList.map).sum
  have h_sum_eq :
      sum_prefix k k.val.size = (k.val.toList.map UInt64.toNat).sum := by
    have h := sum_prefix_eq_take_sum k k.val.size (Nat.le_refl _)
    rw [h]
    -- (toList.take size) = toList
    have : k.val.toList.take k.val.size = k.val.toList := by
      apply List.take_of_length_le
      rw [Array.length_toList]
      exact Nat.le.refl
    rw [this]
  -- Show: denom_prefix k size = list_factorial_prod (toList.map)
  have h_denom_eq :
      denom_prefix k k.val.size =
        list_factorial_prod (k.val.toList.map UInt64.toNat) := by
    have h := denom_prefix_eq_take_lfp k k.val.size (Nat.le_refl _)
    rw [h]
    have : k.val.toList.take k.val.size = k.val.toList := by
      apply List.take_of_length_le
      rw [Array.length_toList]
      exact Nat.le.refl
    rw [this]
  -- Conclude using both closed forms
  have hP' : mult_prefix k k.val.size *
              list_factorial_prod (k.val.toList.map UInt64.toNat) =
              factorial ((k.val.toList.map UInt64.toNat).sum) := by
    rw [← h_denom_eq, ← h_sum_eq]
    exact hP
  have hpos : 0 < list_factorial_prod (k.val.toList.map UInt64.toNat) :=
    list_factorial_prod_pos _
  rw [← hL] at hP'
  exact Nat.eq_of_mul_eq_mul_right hpos hP'

/-- Permutation invariance. -/
theorem multinomial_permutation_invariant (k k' : RustSlice u64)
    (hperm        : k.val.toList.Perm k'.val.toList)
    (hfit_sum_k   : sum_prefix  k  k.val.size  < 2 ^ 64)
    (hfit_res_k   : mult_prefix k  k.val.size  < 2 ^ 64)
    (hfit_sum_k'  : sum_prefix  k' k'.val.size < 2 ^ 64)
    (hfit_res_k'  : mult_prefix k' k'.val.size < 2 ^ 64) :
    ∃ v : u64,
      multinomial_u64.multinomial k  = RustM.ok v ∧
      multinomial_u64.multinomial k' = RustM.ok v := by
  refine ⟨UInt64.ofNat (mult_prefix k k.val.size),
          multinomial_closed_form k hfit_sum_k hfit_res_k, ?_⟩
  rw [multinomial_closed_form k' hfit_sum_k' hfit_res_k']
  -- Goal: ok (ofNat (mult_prefix k' size')) = ok (ofNat (mult_prefix k size))
  congr 1
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofNat_of_lt' hfit_res_k',
      UInt64.toNat_ofNat_of_lt' hfit_res_k]
  -- Both equal via mult_prefix_eq_mult_list and perm invariance of mult_list
  rw [mult_prefix_eq_mult_list k, mult_prefix_eq_mult_list k']
  -- Goal: mult_list (k'.val.toList.map UInt64.toNat) = mult_list (k.val.toList.map UInt64.toNat)
  -- From hperm: k.val.toList.Perm k'.val.toList ⇒ (.map UInt64.toNat) preserves Perm
  have hperm_mapped : (k.val.toList.map UInt64.toNat).Perm (k'.val.toList.map UInt64.toNat) :=
    hperm.map UInt64.toNat
  exact (mult_list_perm_invariant hperm_mapped).symm

end Multinomial_u64Obligations
