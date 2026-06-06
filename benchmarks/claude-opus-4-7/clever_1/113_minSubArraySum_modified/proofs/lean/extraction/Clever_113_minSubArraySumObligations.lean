-- Companion obligations file for the `clever_113_minSubArraySum` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_113_minSubArraySum

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_113_minSubArraySumObligations

/-! ## Specification oracle: integer-valued prefix sums.

The sum of the contiguous subarray `nums[a..b]` (zero-based half-open,
`a < b`) is `prefix_sum_int nums b - prefix_sum_int nums a`. We work in
`Int` so the spec itself never overflows; obligations whose conclusion
talks about the result already condition on `minSubArraySum nums =
RustM.ok r`, which carries the no-overflow side condition implicitly. -/

private def prefix_sum_int (nums : RustSlice i64) : Nat → Int
  | 0     => 0
  | k + 1 =>
      prefix_sum_int nums k +
        (if h : k < nums.val.size then (nums.val[k]'h).toInt else 0)

/-! ## Helpers (transferred from `below_zero` reference). -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl
private theorem usize_zero_toNat : (0 : usize).toNat = 0 := rfl

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide

private theorem prefix_sum_int_succ
    (nums : RustSlice i64) (k : Nat) (hk : k < nums.val.size) :
    prefix_sum_int nums (k + 1) =
      prefix_sum_int nums k + (nums.val[k]'hk).toInt := by
  show prefix_sum_int nums k
        + (if h : k < nums.val.size then (nums.val[k]'h).toInt else 0)
       = prefix_sum_int nums k + (nums.val[k]'hk).toInt
  rw [dif_pos hk]

/-! ## `is_empty` evaluation lemmas. -/

private theorem is_empty_true (l : RustSlice i64) (hempty : l.val.size = 0) :
    (core_models.slice.Impl.is_empty i64 l : RustM Bool) = RustM.ok true := by
  unfold core_models.slice.Impl.is_empty core_models.slice.Impl.len
         rust_primitives.slice.slice_length
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  simp only [bind_pure_comp, pure_bind]
  show RustM.ok (USize64.ofNat l.val.size == (0 : usize)) = RustM.ok true
  congr 1
  rw [show (USize64.ofNat l.val.size == (0 : usize))
        = decide (USize64.ofNat l.val.size = 0) from rfl]
  apply decide_eq_true
  apply USize64.toNat_inj.mp
  rw [h_ofNat, hempty]; rfl

private theorem is_empty_false (l : RustSlice i64) (hne : 0 < l.val.size) :
    (core_models.slice.Impl.is_empty i64 l : RustM Bool) = RustM.ok false := by
  unfold core_models.slice.Impl.is_empty core_models.slice.Impl.len
         rust_primitives.slice.slice_length
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  simp only [bind_pure_comp, pure_bind]
  show RustM.ok (USize64.ofNat l.val.size == (0 : usize)) = RustM.ok false
  congr 1
  rw [show (USize64.ofNat l.val.size == (0 : usize))
        = decide (USize64.ofNat l.val.size = 0) from rfl]
  apply decide_eq_false
  intro h
  have h_nat : (USize64.ofNat l.val.size).toNat = 0 := by rw [h]; rfl
  rw [h_ofNat] at h_nat
  omega

/-! ## Step lemmas for `run_at`. -/

/-- Out-of-bounds step: when `i.toNat ≥ l.val.size`, the function
    returns `RustM.ok best`. -/
private theorem run_at_oob (l : RustSlice i64) (i : usize) (cur best : i64)
    (hi : l.val.size ≤ i.toNat) :
    clever_113_minSubArraySum.run_at l i cur best = RustM.ok best := by
  conv => lhs; unfold clever_113_minSubArraySum.run_at
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- Recursion step: when `i.toNat < l.val.size`, addition `cur +? l[i]` does
    not overflow, and `i+1` does not overflow. The function reduces to the
    nested conditional pick of `nc` (min of `cur+l[i]` and `l[i]`) and `nb`
    (min of `nc` and `best`), then recurses. -/
private theorem run_at_recurse (l : RustSlice i64) (i : usize) (cur best : i64)
    (hi : i.toNat < l.val.size)
    (hno_add : ¬ Int64.addOverflow cur (l.val[i.toNat]'hi))
    (hno_i : i.toNat + 1 < 2^64) :
    clever_113_minSubArraySum.run_at l i cur best =
      (if (cur + l.val[i.toNat]'hi) < (l.val[i.toNat]'hi) then
         (if (cur + l.val[i.toNat]'hi) < best then
            clever_113_minSubArraySum.run_at l (i + 1)
              (cur + l.val[i.toNat]'hi) (cur + l.val[i.toNat]'hi)
          else
            clever_113_minSubArraySum.run_at l (i + 1)
              (cur + l.val[i.toNat]'hi) best)
       else
         (if (l.val[i.toNat]'hi) < best then
            clever_113_minSubArraySum.run_at l (i + 1)
              (l.val[i.toNat]'hi) (l.val[i.toNat]'hi)
          else
            clever_113_minSubArraySum.run_at l (i + 1)
              (l.val[i.toNat]'hi) best)) := by
  conv => lhs; unfold clever_113_minSubArraySum.run_at
  have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
  have h_no_bv :
      BitVec.saddOverflow cur.toBitVec (l.val[i.toNat]'hi).toBitVec = false := by
    have hno' : ¬ (BitVec.saddOverflow cur.toBitVec
                                       (l.val[i.toNat]'hi).toBitVec = true) := hno_add
    cases hb : BitVec.saddOverflow cur.toBitVec (l.val[i.toNat]'hi).toBitVec with
    | false => rfl
    | true => exact absurd hb hno'
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
  have h_cond_prop : ¬ (USize64.ofNat l.val.size ≤ i) := by
    rw [USize64.le_iff_toNat_le, h_ofNat]; omega
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.ops.arith.Add.add, h_no_bv, h_no_bv_i,
             rust_primitives.cmp.lt, decide_eq_true_eq]
  rw [if_neg h_cond_prop]

/-! ## Top-level contract obligations. -/

/-- Boundary clause: on the empty slice the sentinel `0` is returned.
    Captures the property test `empty_input_returns_zero`. -/
theorem empty_returns_zero (nums : RustSlice i64) (hempty : nums.val.size = 0) :
    clever_113_minSubArraySum.minSubArraySum nums = RustM.ok (0 : i64) := by
  unfold clever_113_minSubArraySum.minSubArraySum
  rw [is_empty_true nums hempty]
  simp only [RustM_ok_bind, ↓reduceIte]
  rfl

/-- Boundary clause: on a length-1 slice the sole element is returned.
    Captures the property test `singleton_returns_element`. -/
theorem singleton_returns_element (nums : RustSlice i64)
    (hsingle : nums.val.size = 1) :
    clever_113_minSubArraySum.minSubArraySum nums
      = RustM.ok (nums.val[0]'(by omega)) := by
  unfold clever_113_minSubArraySum.minSubArraySum
  have h_size_pos : 0 < nums.val.size := by omega
  rw [is_empty_false nums h_size_pos]
  simp only [RustM_ok_bind, Bool.false_eq_true, ↓reduceIte]
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_zero_lt : (0 : usize).toNat < nums.val.size := by rw [h_zero_toNat]; omega
  have h_idx : (nums[(0 : usize)]_? : RustM i64) = RustM.ok (nums.val[0]'h_size_pos) := by
    show (if h : (0 : usize).toNat < nums.val.size then pure (nums.val[(0 : usize)])
            else .fail .arrayOutOfBounds)
        = RustM.ok (nums.val[0]'h_size_pos)
    rw [dif_pos h_zero_lt]; rfl
  rw [h_idx]
  simp only [RustM_ok_bind]
  -- Now goal: run_at nums 1 nums[0] nums[0] = RustM.ok nums[0]
  have h_one_toNat : (1 : usize).toNat = 1 := usize_one_toNat
  have h_one_ge : nums.val.size ≤ (1 : usize).toNat := by
    rw [h_one_toNat]; omega
  exact run_at_oob nums (1 : usize) (nums.val[0]'h_size_pos)
                                     (nums.val[0]'h_size_pos) h_one_ge

/-! ## Workhorse: strong-induction invariant for `run_at`.

We thread two invariants:
  - `cur` is the minimum subarray sum ending at index `i-1`, both achievable
    (∃ a₀ < i s.t. cur.toInt = ps i - ps a₀) and a lower bound (∀ a < i,
    cur.toInt ≤ ps i - ps a).
  - `best` is the minimum subarray sum among (a, b) with `a < b ≤ i`,
    similarly both achievable and a lower bound.

Conclusion on the returned `r`: `r` is achievable by some subarray
`(a, b)` with `a < b ≤ size`, and `r` is a lower bound on all such pairs. -/

private theorem run_at_correct (l : RustSlice i64) :
    ∀ (m : Nat) (i : usize) (cur best r : i64),
      l.val.size - i.toNat ≤ m →
      1 ≤ i.toNat →
      i.toNat ≤ l.val.size →
      (∃ a₀ : Nat, a₀ < i.toNat ∧
          cur.toInt = prefix_sum_int l i.toNat - prefix_sum_int l a₀) →
      (∀ a : Nat, a < i.toNat →
          cur.toInt ≤ prefix_sum_int l i.toNat - prefix_sum_int l a) →
      (∃ a₁ b₁ : Nat, a₁ < b₁ ∧ b₁ ≤ i.toNat ∧
          best.toInt = prefix_sum_int l b₁ - prefix_sum_int l a₁) →
      (∀ a b : Nat, a < b → b ≤ i.toNat →
          best.toInt ≤ prefix_sum_int l b - prefix_sum_int l a) →
      clever_113_minSubArraySum.run_at l i cur best = RustM.ok r →
      (∃ a₀ b₀ : Nat, a₀ < b₀ ∧ b₀ ≤ l.val.size ∧
          r.toInt = prefix_sum_int l b₀ - prefix_sum_int l a₀) ∧
      (∀ a b : Nat, a < b → b ≤ l.val.size →
          r.toInt ≤ prefix_sum_int l b - prefix_sum_int l a) := by
  intro m
  induction m with
  | zero =>
    intro i cur best r hm h_i_ge h_i_le h_cur_ach h_cur_min h_best_ach h_best_min h
    have hi_ge : l.val.size ≤ i.toNat := by omega
    have h_oob_eq := run_at_oob l i cur best hi_ge
    rw [h_oob_eq] at h
    have h_r_eq : r = best := by
      injection h with h1
      injection h1 with h2
      exact h2.symm
    subst h_r_eq
    refine ⟨?_, ?_⟩
    · obtain ⟨a₁, b₁, hab, hb_le, h_eq⟩ := h_best_ach
      exact ⟨a₁, b₁, hab, by omega, h_eq⟩
    · intro a b hab hb_le
      by_cases h_b_le : b ≤ i.toNat
      · exact h_best_min a b hab h_b_le
      · omega
  | succ m ih =>
    intro i cur best r hm h_i_ge h_i_le h_cur_ach h_cur_min h_best_ach h_best_min h
    by_cases h_oob : l.val.size ≤ i.toNat
    · have h_oob_eq := run_at_oob l i cur best h_oob
      rw [h_oob_eq] at h
      have h_r_eq : r = best := by
        injection h with h1
        injection h1 with h2
        exact h2.symm
      subst h_r_eq
      refine ⟨?_, ?_⟩
      · obtain ⟨a₁, b₁, hab, hb_le, h_eq⟩ := h_best_ach
        exact ⟨a₁, b₁, hab, by omega, h_eq⟩
      · intro a b hab hb_le
        by_cases h_b_le : b ≤ i.toNat
        · exact h_best_min a b hab h_b_le
        · omega
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le h_oob
      have h_size_lt : l.val.size < 2^64 := l.size_lt_usizeSize
      have h_i_no_ov : i.toNat + 1 < 2^64 := by omega
      -- Establish no-overflow on cur + l[i] from h (function would otherwise fail).
      have h_no_add : ¬ Int64.addOverflow cur (l.val[i.toNat]'hi_lt) := by
        intro hov
        conv at h => lhs; unfold clever_113_minSubArraySum.run_at
        have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
          USize64.toNat_ofNat_of_lt' l.size_lt_usizeSize
        have h_cond : decide (USize64.ofNat l.val.size ≤ i) = false := by
          rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]
          omega
        have h_idx : (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi_lt) := by
          show (if hh : i.toNat < l.val.size then pure (l.val[i]) else .fail .arrayOutOfBounds)
              = RustM.ok (l.val[i.toNat]'hi_lt)
          rw [dif_pos hi_lt]; rfl
        have h_bv_true :
            BitVec.saddOverflow cur.toBitVec (l.val[i.toNat]'hi_lt).toBitVec = true := hov
        have h_add_fail :
            (cur +? (l.val[i.toNat]'hi_lt) : RustM i64) =
              RustM.fail Error.integerOverflow := by
          show (rust_primitives.ops.arith.Add.add cur (l.val[i.toNat]'hi_lt) : RustM i64) = _
          show (if BitVec.saddOverflow cur.toBitVec (l.val[i.toNat]'hi_lt).toBitVec
                then (.fail .integerOverflow : RustM i64)
                else pure (cur + l.val[i.toNat]'hi_lt)) = _
          rw [h_bv_true]; rfl
        have h_cond_prop : ¬ (USize64.ofNat l.val.size ≤ i) := by
          rw [USize64.le_iff_toNat_le, h_ofNat]; omega
        simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
                   rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
                   h_cond, Bool.false_eq_true, ↓reduceIte,
                   h_idx, h_add_fail] at h
        -- h has form: do let ext ← RustM.fail integerOverflow; ... = RustM.ok r
        -- Reduce the bind explicitly.
        simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, Option.bind] at h
        cases h
      -- Use run_at_recurse to reduce the hypothesis.
      have h_rec := run_at_recurse l i cur best hi_lt h_no_add h_i_no_ov
      rw [h_rec] at h
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_i_no_ov
      have h_li_toInt :
          (l.val[i.toNat]'hi_lt).toInt =
            prefix_sum_int l (i.toNat + 1) - prefix_sum_int l i.toNat := by
        rw [prefix_sum_int_succ l i.toNat hi_lt]; omega
      have h_ext_toInt :
          (cur + l.val[i.toNat]'hi_lt).toInt = cur.toInt + (l.val[i.toNat]'hi_lt).toInt :=
        Int64.toInt_add_of_not_addOverflow h_no_add
      obtain ⟨a₀, ha₀_lt, h_cur_eq⟩ := h_cur_ach
      -- Characterize cur.toInt < 0 vs ≥ 0 from the `ext < l[i]` comparison.
      have h_cmp1_iff :
          (cur + l.val[i.toNat]'hi_lt) < l.val[i.toNat]'hi_lt ↔ cur.toInt < 0 := by
        rw [Int64.lt_iff_toInt_lt, h_ext_toInt]
        constructor <;> intro hh <;> omega
      by_cases h_cmp1 : (cur + l.val[i.toNat]'hi_lt) < l.val[i.toNat]'hi_lt
      · -- nc = cur + l[i] (i.e., extend); cur.toInt < 0
        rw [if_pos h_cmp1] at h
        have h_cur_neg : cur.toInt < 0 := h_cmp1_iff.mp h_cmp1
        have h_nc_eq :
            (cur + l.val[i.toNat]'hi_lt).toInt =
              prefix_sum_int l (i.toNat + 1) - prefix_sum_int l a₀ := by
          rw [h_ext_toInt, h_cur_eq, h_li_toInt]; omega
        -- State invariants in `i.toNat + 1` form.
        have h_nc_ach_succ :
            ∃ a₀' : Nat, a₀' < i.toNat + 1 ∧
              (cur + l.val[i.toNat]'hi_lt).toInt =
                prefix_sum_int l (i.toNat + 1) - prefix_sum_int l a₀' :=
          ⟨a₀, by omega, h_nc_eq⟩
        have h_nc_min_succ :
            ∀ a : Nat, a < i.toNat + 1 →
              (cur + l.val[i.toNat]'hi_lt).toInt ≤
                prefix_sum_int l (i.toNat + 1) - prefix_sum_int l a := by
          intro a ha
          by_cases h_a_lt : a < i.toNat
          · have h_split :
                prefix_sum_int l (i.toNat + 1) - prefix_sum_int l a =
                  (prefix_sum_int l i.toNat - prefix_sum_int l a)
                    + (l.val[i.toNat]'hi_lt).toInt := by
              rw [prefix_sum_int_succ l i.toNat hi_lt]; omega
            rw [h_split, h_ext_toInt]
            have h_cur_le := h_cur_min a h_a_lt
            omega
          · have h_a_eq : a = i.toNat := by omega
            subst h_a_eq
            rw [h_ext_toInt]
            have h_eq : prefix_sum_int l (i.toNat + 1) - prefix_sum_int l i.toNat
                = (l.val[i.toNat]'hi_lt).toInt := by
              rw [prefix_sum_int_succ l i.toNat hi_lt]; omega
            omega
        -- Bridge to (i + 1).toNat form for IH.
        have h_nc_ach :
            ∃ a₀' : Nat, a₀' < (i + 1).toNat ∧
              (cur + l.val[i.toNat]'hi_lt).toInt =
                prefix_sum_int l (i + 1).toNat - prefix_sum_int l a₀' := by
          rw [h_i1_toNat]; exact h_nc_ach_succ
        have h_nc_min :
            ∀ a : Nat, a < (i + 1).toNat →
              (cur + l.val[i.toNat]'hi_lt).toInt ≤
                prefix_sum_int l (i + 1).toNat - prefix_sum_int l a := by
          rw [h_i1_toNat]; exact h_nc_min_succ
        by_cases h_cmp2 : (cur + l.val[i.toNat]'hi_lt) < best
        · -- nb = ext
          rw [if_pos h_cmp2] at h
          have h_nb_ach :
              ∃ a₁ b₁ : Nat, a₁ < b₁ ∧ b₁ ≤ (i + 1).toNat ∧
                (cur + l.val[i.toNat]'hi_lt).toInt =
                  prefix_sum_int l b₁ - prefix_sum_int l a₁ := by
            refine ⟨a₀, i.toNat + 1, by omega, ?_, h_nc_eq⟩
            rw [h_i1_toNat]; omega
          have h_nb_min :
              ∀ a b : Nat, a < b → b ≤ (i + 1).toNat →
                (cur + l.val[i.toNat]'hi_lt).toInt ≤
                  prefix_sum_int l b - prefix_sum_int l a := by
            intro a b hab hb_le
            rw [h_i1_toNat] at hb_le
            by_cases h_b_le : b ≤ i.toNat
            · have h_best := h_best_min a b hab h_b_le
              have h_nc_lt_best :
                  (cur + l.val[i.toNat]'hi_lt).toInt < best.toInt :=
                Int64.lt_iff_toInt_lt.mp h_cmp2
              omega
            · have h_b_eq : b = i.toNat + 1 := by omega
              subst h_b_eq
              exact h_nc_min_succ a hab
          exact ih (i + 1) (cur + l.val[i.toNat]'hi_lt) (cur + l.val[i.toNat]'hi_lt) r
            (by rw [h_i1_toNat]; omega)
            (by rw [h_i1_toNat]; omega)
            (by rw [h_i1_toNat]; omega)
            h_nc_ach h_nc_min h_nb_ach h_nb_min h
        · -- nb = best (kept)
          rw [if_neg h_cmp2] at h
          have h_nb_ach :
              ∃ a₁ b₁ : Nat, a₁ < b₁ ∧ b₁ ≤ (i + 1).toNat ∧
                best.toInt = prefix_sum_int l b₁ - prefix_sum_int l a₁ := by
            obtain ⟨a₁, b₁, hab, hb_le, h_eq⟩ := h_best_ach
            refine ⟨a₁, b₁, hab, ?_, h_eq⟩
            rw [h_i1_toNat]; omega
          have h_nb_min :
              ∀ a b : Nat, a < b → b ≤ (i + 1).toNat →
                best.toInt ≤ prefix_sum_int l b - prefix_sum_int l a := by
            intro a b hab hb_le
            rw [h_i1_toNat] at hb_le
            by_cases h_b_le : b ≤ i.toNat
            · exact h_best_min a b hab h_b_le
            · have h_b_eq : b = i.toNat + 1 := by omega
              subst h_b_eq
              have h_nc_le := h_nc_min_succ a hab
              have h_best_le_nc :
                  best.toInt ≤ (cur + l.val[i.toNat]'hi_lt).toInt := by
                rcases Int.lt_or_le (cur + l.val[i.toNat]'hi_lt).toInt best.toInt
                  with h_lt | h_ge
                · exact absurd (Int64.lt_iff_toInt_lt.mpr h_lt) h_cmp2
                · exact h_ge
              omega
          exact ih (i + 1) (cur + l.val[i.toNat]'hi_lt) best r
            (by rw [h_i1_toNat]; omega)
            (by rw [h_i1_toNat]; omega)
            (by rw [h_i1_toNat]; omega)
            h_nc_ach h_nc_min h_nb_ach h_nb_min h
      · -- nc = l[i] (start fresh); cur.toInt ≥ 0
        rw [if_neg h_cmp1] at h
        have h_cur_nonneg : 0 ≤ cur.toInt := by
          rcases Int.lt_or_le cur.toInt 0 with h_lt | h_ge
          · exact absurd (h_cmp1_iff.mpr h_lt) h_cmp1
          · exact h_ge
        have h_nc'_ach_succ :
            ∃ a₀' : Nat, a₀' < i.toNat + 1 ∧
              (l.val[i.toNat]'hi_lt).toInt =
                prefix_sum_int l (i.toNat + 1) - prefix_sum_int l a₀' :=
          ⟨i.toNat, by omega, h_li_toInt⟩
        have h_nc'_min_succ :
            ∀ a : Nat, a < i.toNat + 1 →
              (l.val[i.toNat]'hi_lt).toInt ≤
                prefix_sum_int l (i.toNat + 1) - prefix_sum_int l a := by
          intro a ha
          by_cases h_a_lt : a < i.toNat
          · have h_split :
                prefix_sum_int l (i.toNat + 1) - prefix_sum_int l a =
                  (prefix_sum_int l i.toNat - prefix_sum_int l a)
                    + (l.val[i.toNat]'hi_lt).toInt := by
              rw [prefix_sum_int_succ l i.toNat hi_lt]; omega
            rw [h_split]
            have h_cur_le := h_cur_min a h_a_lt
            omega
          · have h_a_eq : a = i.toNat := by omega
            subst h_a_eq
            omega
        have h_nc'_ach :
            ∃ a₀' : Nat, a₀' < (i + 1).toNat ∧
              (l.val[i.toNat]'hi_lt).toInt =
                prefix_sum_int l (i + 1).toNat - prefix_sum_int l a₀' := by
          rw [h_i1_toNat]; exact h_nc'_ach_succ
        have h_nc'_min :
            ∀ a : Nat, a < (i + 1).toNat →
              (l.val[i.toNat]'hi_lt).toInt ≤
                prefix_sum_int l (i + 1).toNat - prefix_sum_int l a := by
          rw [h_i1_toNat]; exact h_nc'_min_succ
        by_cases h_cmp3 : (l.val[i.toNat]'hi_lt) < best
        · -- nb = l[i]
          rw [if_pos h_cmp3] at h
          have h_nb_ach :
              ∃ a₁ b₁ : Nat, a₁ < b₁ ∧ b₁ ≤ (i + 1).toNat ∧
                (l.val[i.toNat]'hi_lt).toInt =
                  prefix_sum_int l b₁ - prefix_sum_int l a₁ := by
            refine ⟨i.toNat, i.toNat + 1, by omega, ?_, h_li_toInt⟩
            rw [h_i1_toNat]; omega
          have h_nb_min :
              ∀ a b : Nat, a < b → b ≤ (i + 1).toNat →
                (l.val[i.toNat]'hi_lt).toInt ≤
                  prefix_sum_int l b - prefix_sum_int l a := by
            intro a b hab hb_le
            rw [h_i1_toNat] at hb_le
            by_cases h_b_le : b ≤ i.toNat
            · have h_best := h_best_min a b hab h_b_le
              have h_li_lt_best :
                  (l.val[i.toNat]'hi_lt).toInt < best.toInt :=
                Int64.lt_iff_toInt_lt.mp h_cmp3
              omega
            · have h_b_eq : b = i.toNat + 1 := by omega
              subst h_b_eq
              exact h_nc'_min_succ a hab
          exact ih (i + 1) (l.val[i.toNat]'hi_lt) (l.val[i.toNat]'hi_lt) r
            (by rw [h_i1_toNat]; omega)
            (by rw [h_i1_toNat]; omega)
            (by rw [h_i1_toNat]; omega)
            h_nc'_ach h_nc'_min h_nb_ach h_nb_min h
        · -- nb = best
          rw [if_neg h_cmp3] at h
          have h_nb_ach :
              ∃ a₁ b₁ : Nat, a₁ < b₁ ∧ b₁ ≤ (i + 1).toNat ∧
                best.toInt = prefix_sum_int l b₁ - prefix_sum_int l a₁ := by
            obtain ⟨a₁, b₁, hab, hb_le, h_eq⟩ := h_best_ach
            refine ⟨a₁, b₁, hab, ?_, h_eq⟩
            rw [h_i1_toNat]; omega
          have h_nb_min :
              ∀ a b : Nat, a < b → b ≤ (i + 1).toNat →
                best.toInt ≤ prefix_sum_int l b - prefix_sum_int l a := by
            intro a b hab hb_le
            rw [h_i1_toNat] at hb_le
            by_cases h_b_le : b ≤ i.toNat
            · exact h_best_min a b hab h_b_le
            · have h_b_eq : b = i.toNat + 1 := by omega
              subst h_b_eq
              have h_nc'_le := h_nc'_min_succ a hab
              have h_best_le_nc' :
                  best.toInt ≤ (l.val[i.toNat]'hi_lt).toInt := by
                rcases Int.lt_or_le (l.val[i.toNat]'hi_lt).toInt best.toInt
                  with h_lt | h_ge
                · exact absurd (Int64.lt_iff_toInt_lt.mpr h_lt) h_cmp3
                · exact h_ge
              omega
          exact ih (i + 1) (l.val[i.toNat]'hi_lt) best r
            (by rw [h_i1_toNat]; omega)
            (by rw [h_i1_toNat]; omega)
            (by rw [h_i1_toNat]; omega)
            h_nc'_ach h_nc'_min h_nb_ach h_nb_min h

/-! ## Bridging: reduce `minSubArraySum` on a non-empty slice. -/

private theorem minSubArraySum_nonempty_eq
    (nums : RustSlice i64) (hne : 0 < nums.val.size) (r : i64)
    (h : clever_113_minSubArraySum.minSubArraySum nums = RustM.ok r) :
    clever_113_minSubArraySum.run_at nums (1 : usize) (nums.val[0]'hne) (nums.val[0]'hne)
      = RustM.ok r := by
  unfold clever_113_minSubArraySum.minSubArraySum at h
  rw [is_empty_false nums hne] at h
  simp only [RustM_ok_bind, Bool.false_eq_true, ↓reduceIte] at h
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_zero_lt : (0 : usize).toNat < nums.val.size := by rw [h_zero_toNat]; omega
  have h_idx : (nums[(0 : usize)]_? : RustM i64) = RustM.ok (nums.val[0]'hne) := by
    show (if hh : (0 : usize).toNat < nums.val.size then pure (nums.val[(0 : usize)])
            else .fail .arrayOutOfBounds)
        = RustM.ok (nums.val[0]'hne)
    rw [dif_pos h_zero_lt]; rfl
  rw [h_idx] at h
  simp only [RustM_ok_bind] at h
  exact h

/-! ## Initial-state invariants for the top-level call. -/

private theorem initial_invariants (nums : RustSlice i64) (hne : 0 < nums.val.size) :
    (∃ a₀ : Nat, a₀ < (1 : usize).toNat ∧
        (nums.val[0]'hne).toInt = prefix_sum_int nums (1 : usize).toNat - prefix_sum_int nums a₀) ∧
    (∀ a : Nat, a < (1 : usize).toNat →
        (nums.val[0]'hne).toInt ≤ prefix_sum_int nums (1 : usize).toNat - prefix_sum_int nums a) ∧
    (∃ a₁ b₁ : Nat, a₁ < b₁ ∧ b₁ ≤ (1 : usize).toNat ∧
        (nums.val[0]'hne).toInt = prefix_sum_int nums b₁ - prefix_sum_int nums a₁) ∧
    (∀ a b : Nat, a < b → b ≤ (1 : usize).toNat →
        (nums.val[0]'hne).toInt ≤ prefix_sum_int nums b - prefix_sum_int nums a) := by
  have h_one_toNat : (1 : usize).toNat = 1 := usize_one_toNat
  have h_v_eq : (nums.val[0]'hne).toInt =
      prefix_sum_int nums 1 - prefix_sum_int nums 0 := by
    rw [prefix_sum_int_succ nums 0 hne]
    show (nums.val[0]'hne).toInt
      = (prefix_sum_int nums 0 + (nums.val[0]'hne).toInt) - prefix_sum_int nums 0
    show (nums.val[0]'hne).toInt = ((0 : Int) + (nums.val[0]'hne).toInt) - 0
    omega
  refine ⟨⟨0, ?_, ?_⟩, ?_, ⟨0, 1, ?_, ?_, ?_⟩, ?_⟩
  · rw [h_one_toNat]; omega
  · rw [h_one_toNat]; exact h_v_eq
  · intro a ha
    rw [h_one_toNat] at ha
    have h_a_eq : a = 0 := by omega
    subst h_a_eq
    rw [h_one_toNat]
    omega
  · omega
  · rw [h_one_toNat]; omega
  · exact h_v_eq
  · intro a b hab hb_le
    rw [h_one_toNat] at hb_le
    have h_b_eq : b = 1 := by omega
    subst h_b_eq
    have h_a_eq : a = 0 := by omega
    subst h_a_eq
    omega

/-- Achievability postcondition: the returned value is the integer sum of
    some non-empty contiguous subarray `nums[a..b]` with `a < b ≤ size`.
    Captures the property test `result_is_achieved_by_some_subarray`. -/
theorem result_is_achieved_by_some_subarray
    (nums : RustSlice i64) (r : i64)
    (hnonempty : 0 < nums.val.size)
    (h : clever_113_minSubArraySum.minSubArraySum nums = RustM.ok r) :
    ∃ a b : Nat, a < b ∧ b ≤ nums.val.size ∧
      r.toInt = prefix_sum_int nums b - prefix_sum_int nums a := by
  have h_eq := minSubArraySum_nonempty_eq nums hnonempty r h
  obtain ⟨h_ach, _, h_best_ach, h_best_min⟩ := initial_invariants nums hnonempty
  have h_one_toNat : (1 : usize).toNat = 1 := usize_one_toNat
  have h_correct := run_at_correct nums nums.val.size (1 : usize)
      (nums.val[0]'hnonempty) (nums.val[0]'hnonempty) r
      (by rw [h_one_toNat]; omega)
      (by rw [h_one_toNat]; omega)
      (by rw [h_one_toNat]; omega)
      h_ach
      (by intro a ha; exact (initial_invariants nums hnonempty).2.1 a ha)
      h_best_ach h_best_min h_eq
  exact h_correct.1

/-- Minimality postcondition: the returned value is a lower bound on every
    non-empty contiguous-subarray sum `nums[a..b]` with `a < b ≤ size`.
    Captures the property test `result_lower_bounds_all_subarrays`.

    Note: on the empty slice (`size = 0`), the universal premise `a < b ≤ 0`
    is unsatisfiable, so the statement is vacuously true — consistent with
    the empty-returns-0 boundary clause. -/
theorem result_lower_bounds_all_subarrays
    (nums : RustSlice i64) (r : i64)
    (h : clever_113_minSubArraySum.minSubArraySum nums = RustM.ok r) :
    ∀ a b : Nat, a < b → b ≤ nums.val.size →
      r.toInt ≤ prefix_sum_int nums b - prefix_sum_int nums a := by
  by_cases hempty : nums.val.size = 0
  · -- Empty case: the premise b ≤ 0 with a < b forces contradiction.
    intro a b hab hb_le
    omega
  · have hnonempty : 0 < nums.val.size := by omega
    have h_eq := minSubArraySum_nonempty_eq nums hnonempty r h
    obtain ⟨h_ach, _, h_best_ach, h_best_min⟩ := initial_invariants nums hnonempty
    have h_one_toNat : (1 : usize).toNat = 1 := usize_one_toNat
    have h_correct := run_at_correct nums nums.val.size (1 : usize)
        (nums.val[0]'hnonempty) (nums.val[0]'hnonempty) r
        (by rw [h_one_toNat]; omega)
        (by rw [h_one_toNat]; omega)
        (by rw [h_one_toNat]; omega)
        h_ach
        (by intro a ha; exact (initial_invariants nums hnonempty).2.1 a ha)
        h_best_ach h_best_min h_eq
    exact h_correct.2

end Clever_113_minSubArraySumObligations
