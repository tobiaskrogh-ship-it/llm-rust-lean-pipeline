-- Companion obligations file for the `clever_029_get_positive` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_029_get_positive

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_029_get_positiveObligations

/-! ## Specification helper

`positive_indices l k` is the list of input indices `j < k` whose entry
`l.val[j]` is strictly positive (i.e. `(l.val[j]).toInt > 0`). The `dite` on
`j < l.val.size` keeps the definition total; every theorem below applies it
with `k ≤ l.val.size`, so the bounded indices always exist. -/

private def positive_indices (l : RustSlice i64) : Nat → List Nat
  | 0     => []
  | k + 1 =>
      if h : k < l.val.size then
        if (l.val[k]'h).toInt > 0 then
          positive_indices l k ++ [k]
        else
          positive_indices l k
      else
        positive_indices l k

/-! ## Standard scaffolding (transferred from `clever_025_remove_duplicates`,
     `clever_003_below_zero`, `contains_u64`). -/

/-- `RustM.ok x >>= f = f x`. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide

private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide

/-! ## Push helper for `Vec` (`extend_from_slice` of a 1-element chunk). -/

private def push_one (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec i64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

/-! ## Step lemmas for `collect_at`.

Three branches of the recursive body, packaged so subsequent induction can
rewrite directly. -/

/-- Out-of-bounds step: `collect_at` returns the accumulator. -/
private theorem collect_at_oob (l : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : l.val.size ≤ i.toNat) :
    clever_029_get_positive.collect_at l i acc = RustM.ok acc := by
  conv => lhs; unfold clever_029_get_positive.collect_at
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

/-- Keep step: in-bounds, `l[i] > 0` → append and recurse. -/
private theorem collect_at_step_keep (l : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < l.val.size)
    (h_pos : (l.val[i.toNat]'hi).toInt > 0)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_029_get_positive.collect_at l i acc =
      clever_029_get_positive.collect_at l (i + 1)
        (push_one acc (l.val[i.toNat]'hi) h_acc) := by
  conv => lhs; unfold clever_029_get_positive.collect_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_pos_cond : decide ((l.val[i.toNat]'hi) > (0 : i64)) = true := by
    rw [decide_eq_true_iff]
    show (0 : i64) < l.val[i.toNat]'hi
    rw [Int64.lt_iff_toInt_lt, i64_zero_toInt]
    exact h_pos
  have h_no_ov_i : i.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_size_lt; omega
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
  have h_add_i : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
    show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
    show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
          then (.fail .integerOverflow : RustM usize)
          else pure (i + 1)) = _
    rw [h_no_bv_i]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.cmp.gt, h_pos_cond]
  rw [show (rust_primitives.unsize
            (RustArray.ofVec #v[l.val[i.toNat]'hi] : RustArray i64 1)
            : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[l.val[i.toNat]'hi], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size :
      acc.val.size + (#[l.val[i.toNat]'hi] : Array i64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size
    exact h_acc
  rw [show (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
              ⟨#[l.val[i.toNat]'hi], one_lt_usize_size⟩
            : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
        = RustM.ok (push_one acc (l.val[i.toNat]'hi) h_acc) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  simp only [RustM_ok_bind]
  rw [h_add_i]
  rfl

/-- Skip step: in-bounds, `l[i] ≤ 0` → recurse without appending. -/
private theorem collect_at_step_skip (l : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < l.val.size)
    (h_nonpos : ¬ (l.val[i.toNat]'hi).toInt > 0) :
    clever_029_get_positive.collect_at l i acc =
      clever_029_get_positive.collect_at l (i + 1) acc := by
  conv => lhs; unfold clever_029_get_positive.collect_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_pos_cond : decide ((l.val[i.toNat]'hi) > (0 : i64)) = false := by
    rw [decide_eq_false_iff_not]
    show ¬ (0 : i64) < l.val[i.toNat]'hi
    rw [Int64.lt_iff_toInt_lt, i64_zero_toInt]
    exact h_nonpos
  have h_no_ov_i : i.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_size_lt; omega
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
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.cmp.gt, h_pos_cond,
             rust_primitives.ops.arith.Add.add, h_no_bv_i]

/-! ## Helpers about `positive_indices`. -/

/-- All elements of `positive_indices l k` are `< k`. -/
private theorem positive_indices_lt (l : RustSlice i64) :
    ∀ (k : Nat) (j : Nat), j ∈ positive_indices l k → j < k := by
  intro k
  induction k with
  | zero =>
    intro j hj
    simp [positive_indices] at hj
  | succ k ih =>
    intro j hj
    show j < k + 1
    by_cases hk : k < l.val.size
    · by_cases hpos : (l.val[k]'hk).toInt > 0
      · have hbody :
            positive_indices l (k + 1) = positive_indices l k ++ [k] := by
          show (if h : k < l.val.size then
                 (if (l.val[k]'h).toInt > 0 then
                    positive_indices l k ++ [k]
                  else positive_indices l k)
               else positive_indices l k) = _
          rw [dif_pos hk, if_pos hpos]
        rw [hbody] at hj
        rw [List.mem_append] at hj
        rcases hj with hj_l | hj_r
        · have := ih j hj_l; omega
        · simp at hj_r; omega
      · have hbody :
            positive_indices l (k + 1) = positive_indices l k := by
          show (if h : k < l.val.size then
                 (if (l.val[k]'h).toInt > 0 then
                    positive_indices l k ++ [k]
                  else positive_indices l k)
               else positive_indices l k) = _
          rw [dif_pos hk, if_neg hpos]
        rw [hbody] at hj
        have := ih j hj; omega
    · have hbody :
          positive_indices l (k + 1) = positive_indices l k := by
        show (if h : k < l.val.size then _ else positive_indices l k) = _
        rw [dif_neg hk]
      rw [hbody] at hj
      have := ih j hj; omega

/-- Membership characterisation: `i ∈ positive_indices l k` iff `i < k` and
    `l[i] > 0`. -/
private theorem positive_indices_mem (l : RustSlice i64) :
    ∀ (k : Nat) (i : Nat),
      i ∈ positive_indices l k ↔
      (∃ (hi : i < l.val.size), i < k ∧ (l.val[i]'hi).toInt > 0) := by
  intro k
  induction k with
  | zero =>
    intro i
    constructor
    · intro h; simp [positive_indices] at h
    · rintro ⟨_, hlt, _⟩; omega
  | succ k ih =>
    intro i
    by_cases hk : k < l.val.size
    · by_cases hpos : (l.val[k]'hk).toInt > 0
      · have hbody :
            positive_indices l (k + 1) = positive_indices l k ++ [k] := by
          show (if h : k < l.val.size then
                 (if (l.val[k]'h).toInt > 0 then
                    positive_indices l k ++ [k]
                  else positive_indices l k)
               else positive_indices l k) = _
          rw [dif_pos hk, if_pos hpos]
        rw [hbody]
        constructor
        · intro h
          rw [List.mem_append] at h
          rcases h with h_l | h_r
          · obtain ⟨hi, hlt, hcc⟩ := (ih i).mp h_l
            exact ⟨hi, by omega, hcc⟩
          · simp at h_r
            subst h_r
            exact ⟨hk, by omega, hpos⟩
        · rintro ⟨hi, hlt, hcc⟩
          rw [List.mem_append]
          by_cases h_eq : i = k
          · subst h_eq; right; simp
          · left; exact (ih i).mpr ⟨hi, by omega, hcc⟩
      · have hbody :
            positive_indices l (k + 1) = positive_indices l k := by
          show (if h : k < l.val.size then
                 (if (l.val[k]'h).toInt > 0 then
                    positive_indices l k ++ [k]
                  else positive_indices l k)
               else positive_indices l k) = _
          rw [dif_pos hk, if_neg hpos]
        rw [hbody]
        constructor
        · intro h
          obtain ⟨hi, hlt, hcc⟩ := (ih i).mp h
          exact ⟨hi, by omega, hcc⟩
        · rintro ⟨hi, hlt, hcc⟩
          by_cases h_eq : i = k
          · exfalso
            apply hpos
            have h_ix_eq : l.val[k]'hk = l.val[i]'hi :=
              getElem_congr_idx h_eq.symm
            rw [h_ix_eq]; exact hcc
          · exact (ih i).mpr ⟨hi, by omega, hcc⟩
    · have hbody :
          positive_indices l (k + 1) = positive_indices l k := by
        show (if h : k < l.val.size then _ else positive_indices l k) = _
        rw [dif_neg hk]
      rw [hbody]
      constructor
      · intro h
        obtain ⟨hi, hlt, hcc⟩ := (ih i).mp h
        exact ⟨hi, by omega, hcc⟩
      · rintro ⟨hi, hlt, hcc⟩
        have h_lt_k : i < k := by
          rcases Nat.lt_or_ge i k with h | h
          · exact h
          · omega
        exact (ih i).mpr ⟨hi, h_lt_k, hcc⟩

/-- The spec list `positive_indices l k` is strictly increasing. -/
private theorem positive_indices_pairwise (l : RustSlice i64) :
    ∀ k : Nat, (positive_indices l k).Pairwise (· < ·) := by
  intro k
  induction k with
  | zero =>
    show ([] : List Nat).Pairwise (· < ·)
    exact List.Pairwise.nil
  | succ k ih =>
    by_cases hk : k < l.val.size
    · by_cases hpos : (l.val[k]'hk).toInt > 0
      · have hbody :
            positive_indices l (k + 1) = positive_indices l k ++ [k] := by
          show (if h : k < l.val.size then
                 (if (l.val[k]'h).toInt > 0 then
                    positive_indices l k ++ [k]
                  else positive_indices l k)
               else positive_indices l k) = _
          rw [dif_pos hk, if_pos hpos]
        rw [hbody, List.pairwise_append]
        refine ⟨ih, List.pairwise_singleton _ _, ?_⟩
        intro x hx y hy
        simp at hy
        rw [hy]
        exact positive_indices_lt l k x hx
      · have hbody :
            positive_indices l (k + 1) = positive_indices l k := by
          show (if h : k < l.val.size then
                 (if (l.val[k]'h).toInt > 0 then
                    positive_indices l k ++ [k]
                  else positive_indices l k)
               else positive_indices l k) = _
          rw [dif_pos hk, if_neg hpos]
        rw [hbody]; exact ih
    · have hbody :
          positive_indices l (k + 1) = positive_indices l k := by
        show (if h : k < l.val.size then _ else positive_indices l k) = _
        rw [dif_neg hk]
      rw [hbody]; exact ih

/-- Strict monotonicity of `positive_indices` in the `getD`-with-default form. -/
private theorem positive_indices_strict_mono (l : RustSlice i64) (k : Nat) :
    ∀ j₁ j₂ : Nat, j₁ < j₂ → j₂ < (positive_indices l k).length →
      (positive_indices l k).getD j₁ 0 < (positive_indices l k).getD j₂ 0 := by
  intro j₁ j₂ hlt hj₂
  have hj₁ : j₁ < (positive_indices l k).length := by omega
  have h_pw := positive_indices_pairwise l k
  have h_get_lt :
      (positive_indices l k)[j₁]'hj₁ < (positive_indices l k)[j₂]'hj₂ :=
    List.pairwise_iff_getElem.mp h_pw j₁ j₂ hj₁ hj₂ hlt
  rw [show (positive_indices l k).getD j₁ 0 = (positive_indices l k)[j₁]'hj₁ from
        (List.getElem_eq_getD (l := positive_indices l k) (i := j₁)
                              (h := hj₁) 0).symm]
  rw [show (positive_indices l k).getD j₂ 0 = (positive_indices l k)[j₂]'hj₂ from
        (List.getElem_eq_getD (l := positive_indices l k) (i := j₂)
                              (h := hj₂) 0).symm]
  exact h_get_lt

/-- `positive_indices l k` has length at most `k`. -/
private theorem positive_indices_length_le (l : RustSlice i64) :
    ∀ k : Nat, (positive_indices l k).length ≤ k := by
  intro k
  induction k with
  | zero =>
    show ([] : List Nat).length ≤ 0
    simp
  | succ k ih =>
    by_cases hk : k < l.val.size
    · by_cases hpos : (l.val[k]'hk).toInt > 0
      · have hbody :
            positive_indices l (k + 1) = positive_indices l k ++ [k] := by
          show (if h : k < l.val.size then
                  (if (l.val[k]'h).toInt > 0 then
                     positive_indices l k ++ [k]
                   else positive_indices l k)
                else positive_indices l k) = _
          rw [dif_pos hk, if_pos hpos]
        rw [hbody, List.length_append]
        show (positive_indices l k).length + [k].length ≤ k + 1
        have : [k].length = 1 := rfl
        omega
      · have hbody :
            positive_indices l (k + 1) = positive_indices l k := by
          show (if h : k < l.val.size then _ else positive_indices l k) = _
          rw [dif_pos hk, if_neg hpos]
        rw [hbody]; omega
    · have hbody :
          positive_indices l (k + 1) = positive_indices l k := by
        show (if h : k < l.val.size then _ else positive_indices l k) = _
        rw [dif_neg hk]
      rw [hbody]; omega

/-! ## getD helpers. -/

/-- `(L ++ M).getD k d = L.getD k d` when `k < L.length`. -/
private theorem list_getD_append_left {α} (L M : List α) (k : Nat) (d : α)
    (h : k < L.length) : (L ++ M).getD k d = L.getD k d := by
  have h_lt_app : k < (L ++ M).length := by
    rw [List.length_append]; omega
  rw [(List.getElem_eq_getD (l := L ++ M) (i := k) (h := h_lt_app) d).symm]
  rw [(List.getElem_eq_getD (l := L) (i := k) (h := h) d).symm]
  exact List.getElem_append_left h

/-- `(L ++ [x]).getD L.length d = x`. -/
private theorem list_getD_append_singleton_at_len {α} (L : List α) (x d : α) :
    (L ++ [x]).getD L.length d = x := by
  have h_lt : L.length < (L ++ [x]).length := by
    rw [List.length_append]
    show L.length < L.length + [x].length
    have : [x].length = 1 := rfl
    omega
  rw [(List.getElem_eq_getD (l := L ++ [x]) (i := L.length) (h := h_lt) d).symm]
  rw [List.getElem_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self]
  rfl

/-! ## OOB-finish helper. -/

private theorem collect_at_oob_finish (l : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi_eq : i.toNat = l.val.size)
    (h_acc_size : acc.val.size = (positive_indices l i.toNat).length)
    (h_acc_inv :
        ∀ (k : Nat) (hk : k < acc.val.size),
          ∃ (hbi : (positive_indices l i.toNat).getD k 0 < l.val.size),
              acc.val[k]'hk = l.val[(positive_indices l i.toNat).getD k 0]'hbi) :
    acc.val.size = (positive_indices l l.val.size).length ∧
    (∀ (k : Nat) (hk : k < acc.val.size),
        ∃ (hbi : (positive_indices l l.val.size).getD k 0 < l.val.size),
            acc.val[k]'hk = l.val[(positive_indices l l.val.size).getD k 0]'hbi) := by
  have h_bi_eq : positive_indices l i.toNat = positive_indices l l.val.size := by
    rw [hi_eq]
  have h_getD_eq : ∀ k : Nat,
      (positive_indices l i.toNat).getD k 0 =
        (positive_indices l l.val.size).getD k 0 := by
    intro k; rw [h_bi_eq]
  refine ⟨?_, ?_⟩
  · rw [h_acc_size, h_bi_eq]
  · intro k hk
    obtain ⟨hbi, hacc_eq⟩ := h_acc_inv k hk
    have hbi' : (positive_indices l l.val.size).getD k 0 < l.val.size := by
      rw [← h_getD_eq k]; exact hbi
    refine ⟨hbi', ?_⟩
    have h_rewrite :
        l.val[(positive_indices l l.val.size).getD k 0]'hbi' =
          l.val[(positive_indices l i.toNat).getD k 0]'hbi := by
      congr 1
      exact (h_getD_eq k).symm
    rw [h_rewrite]
    exact hacc_eq

/-! ## Strong induction over `collect_at`. -/

private theorem collect_at_correct_strong (l : RustSlice i64) :
    ∀ (n : Nat) (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (v : alloc.vec.Vec i64 alloc.alloc.Global),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      acc.val.size = (positive_indices l i.toNat).length →
      (∀ (k : Nat) (hk : k < acc.val.size),
          ∃ (hbi : (positive_indices l i.toNat).getD k 0 < l.val.size),
              acc.val[k]'hk = l.val[(positive_indices l i.toNat).getD k 0]'hbi) →
      clever_029_get_positive.collect_at l i acc = RustM.ok v →
      v.val.size = (positive_indices l l.val.size).length ∧
      (∀ (k : Nat) (hk : k < v.val.size),
          ∃ (hbi : (positive_indices l l.val.size).getD k 0 < l.val.size),
              v.val[k]'hk = l.val[(positive_indices l l.val.size).getD k 0]'hbi) := by
  intro n
  induction n with
  | zero =>
    intro i acc v hm hi_le h_acc_size h_acc_inv hres
    have hi_eq : i.toNat = l.val.size := by omega
    have hi_ge : l.val.size ≤ i.toNat := by omega
    rw [collect_at_oob l i acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    exact collect_at_oob_finish l i acc hi_eq h_acc_size h_acc_inv
  | succ n ih =>
    intro i acc v hm hi_le h_acc_size h_acc_inv hres
    by_cases hi_ge : l.val.size ≤ i.toNat
    · have hi_eq : i.toNat = l.val.size := by omega
      rw [collect_at_oob l i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      exact collect_at_oob_finish l i acc hi_eq h_acc_size h_acc_inv
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_acc_le_i : acc.val.size ≤ i.toNat := by
        rw [h_acc_size]; exact positive_indices_length_le l i.toNat
      have h_acc_succ : acc.val.size + 1 < USize64.size := by
        rw [h_usize_size]; omega
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_meas : l.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      by_cases hpos : (l.val[i.toNat]'hi_lt).toInt > 0
      · -- Keep branch: predicate holds, positive_indices grows by [i.toNat].
        rw [collect_at_step_keep l i acc hi_lt hpos h_acc_succ] at hres
        have h_pi_succ_keep :
            positive_indices l (i.toNat + 1) =
              positive_indices l i.toNat ++ [i.toNat] := by
          show (if h : i.toNat < l.val.size then
                  (if (l.val[i.toNat]'h).toInt > 0 then
                     positive_indices l i.toNat ++ [i.toNat]
                   else positive_indices l i.toNat)
                else positive_indices l i.toNat) = _
          rw [dif_pos hi_lt, if_pos hpos]
        have h_acc'_size :
            (push_one acc (l.val[i.toNat]'hi_lt) h_acc_succ).val.size =
              (positive_indices l (i + 1).toNat).length := by
          show (acc.val ++ #[l.val[i.toNat]'hi_lt]).size =
            (positive_indices l (i + 1).toNat).length
          rw [Array.size_append, h_i1, h_pi_succ_keep, List.length_append]
          show acc.val.size + 1 = (positive_indices l i.toNat).length + [i.toNat].length
          rw [h_acc_size]; rfl
        have h_acc'_inv :
            ∀ (k : Nat)
              (hk : k < (push_one acc (l.val[i.toNat]'hi_lt) h_acc_succ).val.size),
              ∃ (hbi : (positive_indices l (i + 1).toNat).getD k 0 < l.val.size),
                (push_one acc (l.val[i.toNat]'hi_lt) h_acc_succ).val[k]'hk =
                  l.val[(positive_indices l (i + 1).toNat).getD k 0]'hbi := by
          intro k hk
          have h_pi_i1_eq :
              positive_indices l (i + 1).toNat =
                positive_indices l i.toNat ++ [i.toNat] := by
            rw [h_i1]; exact h_pi_succ_keep
          show ∃ (hbi : (positive_indices l (i + 1).toNat).getD k 0 < l.val.size),
                ((acc.val ++ #[l.val[i.toNat]'hi_lt])[k]'hk) =
                  l.val[(positive_indices l (i + 1).toNat).getD k 0]'hbi
          by_cases hk_lt : k < acc.val.size
          · have hk_lt_pi : k < (positive_indices l i.toNat).length := by
              rw [← h_acc_size]; exact hk_lt
            have h_getD_eq :
                (positive_indices l (i + 1).toNat).getD k 0 =
                  (positive_indices l i.toNat).getD k 0 := by
              rw [h_pi_i1_eq]
              exact list_getD_append_left _ _ k 0 hk_lt_pi
            obtain ⟨hbi, hacc_eq⟩ := h_acc_inv k hk_lt
            have hbi' : (positive_indices l (i + 1).toNat).getD k 0 < l.val.size := by
              rw [h_getD_eq]; exact hbi
            refine ⟨hbi', ?_⟩
            rw [Array.getElem_append_left hk_lt]
            have h_rhs_eq :
                l.val[(positive_indices l (i + 1).toNat).getD k 0]'hbi' =
                  l.val[(positive_indices l i.toNat).getD k 0]'hbi := by
              simp only [h_getD_eq]
            rw [h_rhs_eq]
            exact hacc_eq
          · have h_size_raw :
                (acc.val ++ #[l.val[i.toNat]'hi_lt]).size = acc.val.size + 1 := by
              rw [Array.size_append]; rfl
            have hk_eq_acc : k = acc.val.size := by
              have : k < acc.val.size + 1 := by rw [← h_size_raw]; exact hk
              omega
            have h_getD_eq :
                (positive_indices l (i + 1).toNat).getD k 0 = i.toNat := by
              rw [h_pi_i1_eq, hk_eq_acc, h_acc_size]
              exact list_getD_append_singleton_at_len _ _ 0
            have hbi' : (positive_indices l (i + 1).toNat).getD k 0 < l.val.size := by
              rw [h_getD_eq]; exact hi_lt
            refine ⟨hbi', ?_⟩
            have h_rhs_eq :
                l.val[(positive_indices l (i + 1).toNat).getD k 0]'hbi' =
                  l.val[i.toNat]'hi_lt := by
              simp only [h_getD_eq]
            rw [h_rhs_eq]
            subst hk_eq_acc
            rw [Array.getElem_append_right (Nat.le_refl _)]
            simp only [Nat.sub_self]
            rfl
        exact ih (i + 1) _ v h_meas h_i1_le h_acc'_size h_acc'_inv hres
      · -- Skip branch: predicate fails, positive_indices unchanged.
        rw [collect_at_step_skip l i acc hi_lt hpos] at hres
        have h_pi_succ_skip :
            positive_indices l (i.toNat + 1) = positive_indices l i.toNat := by
          show (if h : i.toNat < l.val.size then
                  (if (l.val[i.toNat]'h).toInt > 0 then
                     positive_indices l i.toNat ++ [i.toNat]
                   else positive_indices l i.toNat)
                else positive_indices l i.toNat) = _
          rw [dif_pos hi_lt, if_neg hpos]
        have h_pi_i1_eq :
            positive_indices l (i + 1).toNat = positive_indices l i.toNat := by
          rw [h_i1]; exact h_pi_succ_skip
        have h_acc'_size :
            acc.val.size = (positive_indices l (i + 1).toNat).length := by
          rw [h_pi_i1_eq]; exact h_acc_size
        have h_acc'_inv :
            ∀ (k : Nat) (hk : k < acc.val.size),
              ∃ (hbi : (positive_indices l (i + 1).toNat).getD k 0 < l.val.size),
                acc.val[k]'hk =
                  l.val[(positive_indices l (i + 1).toNat).getD k 0]'hbi := by
          intro k hk
          obtain ⟨hbi, hacc_eq⟩ := h_acc_inv k hk
          have h_getD_eq :
              (positive_indices l (i + 1).toNat).getD k 0 =
                (positive_indices l i.toNat).getD k 0 := by
            rw [h_pi_i1_eq]
          have hbi' :
              (positive_indices l (i + 1).toNat).getD k 0 < l.val.size := by
            rw [h_getD_eq]; exact hbi
          refine ⟨hbi', ?_⟩
          have h_rhs_eq :
              l.val[(positive_indices l (i + 1).toNat).getD k 0]'hbi' =
                l.val[(positive_indices l i.toNat).getD k 0]'hbi := by
            simp only [h_getD_eq]
          rw [h_rhs_eq]
          exact hacc_eq
        exact ih (i + 1) acc v h_meas h_i1_le h_acc'_size h_acc'_inv hres

/-- Specialise to the initial state `i = 0, acc = #[]` to relate the output
    of `get_positive` directly to `positive_indices l l.val.size`. -/
private theorem collect_at_correspondence (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_029_get_positive.get_positive l = RustM.ok v) :
    v.val.size = (positive_indices l l.val.size).length ∧
    (∀ (k : Nat) (hk : k < v.val.size),
        ∃ (hi : (positive_indices l l.val.size).getD k 0 < l.val.size),
            v.val[k]'hk = l.val[(positive_indices l l.val.size).getD k 0]'hi) := by
  unfold clever_029_get_positive.get_positive at hres
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new, RustM_ok_bind] at hres
  let acc0 : alloc.vec.Vec i64 alloc.alloc.Global := ⟨(List.nil).toArray, by grind⟩
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_acc0_size :
      acc0.val.size = (positive_indices l (0 : usize).toNat).length := by
    show (List.nil : List i64).toArray.size = (positive_indices l (0 : usize).toNat).length
    rw [h_zero_toNat]
    show 0 = ([] : List Nat).length
    rfl
  have h_acc0_inv :
      ∀ (k : Nat) (hk : k < acc0.val.size),
        ∃ (hbi : (positive_indices l (0 : usize).toNat).getD k 0 < l.val.size),
          acc0.val[k]'hk =
            l.val[(positive_indices l (0 : usize).toNat).getD k 0]'hbi := by
    intro k hk
    exfalso
    have h0 : acc0.val.size = 0 := rfl
    rw [h0] at hk
    omega
  have h_meas : l.val.size - (0 : usize).toNat ≤ l.val.size := by
    rw [h_zero_toNat]; omega
  have h_i_le : (0 : usize).toNat ≤ l.val.size := by
    rw [h_zero_toNat]; omega
  exact collect_at_correct_strong l l.val.size (0 : usize) acc0 v
    h_meas h_i_le h_acc0_size h_acc0_inv hres

/-! ## Top-level obligations on `get_positive`. -/

/-- Boundary contract: when the input slice is empty, the output `Vec`
    is empty. Captures the proptest `empty_input_yields_empty`. -/
theorem empty_input_yields_empty
    (l : RustSlice i64) (h_empty : l.val.size = 0)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_029_get_positive.get_positive l = RustM.ok v) :
    v.val.size = 0 := by
  obtain ⟨hsize, _⟩ := collect_at_correspondence l v hres
  rw [hsize]
  have h_pi_empty : positive_indices l l.val.size = positive_indices l 0 := by
    rw [h_empty]
  rw [h_pi_empty]
  show ([] : List Nat).length = 0
  rfl

/-- Soundness: every element of the output is strictly positive. Captures
    the soundness part of `matches_filter_reference`. -/
theorem every_output_is_positive
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_029_get_positive.get_positive l = RustM.ok v)
    (k : Nat) (hk : k < v.val.size) :
    (v.val[k]'hk).toInt > 0 := by
  obtain ⟨hsize, hcorr⟩ := collect_at_correspondence l v hres
  obtain ⟨hi, hveq⟩ := hcorr k hk
  rw [hveq]
  have hk' : k < (positive_indices l l.val.size).length := by
    rw [← hsize]; exact hk
  have h_getD_elem :
      (positive_indices l l.val.size).getD k 0 =
        (positive_indices l l.val.size)[k]'hk' :=
    (List.getElem_eq_getD (l := positive_indices l l.val.size)
                          (i := k) (h := hk') 0).symm
  have h_mem :
      (positive_indices l l.val.size).getD k 0
        ∈ positive_indices l l.val.size := by
    rw [h_getD_elem]; exact List.getElem_mem _
  obtain ⟨_, _, hpos⟩ :=
    (positive_indices_mem l l.val.size _).mp h_mem
  exact hpos

/-- Order-preservation postcondition: the output is a subsequence of the
    input. Captures the order/no-reorder/no-duplicate part of
    `matches_filter_reference`. -/
theorem output_is_subsequence_of_input
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_029_get_positive.get_positive l = RustM.ok v) :
    ∃ idx : Nat → Nat,
      (∀ k₁ k₂ : Nat, k₁ < k₂ → k₂ < v.val.size → idx k₁ < idx k₂) ∧
      (∀ k : Nat, ∀ (hk : k < v.val.size),
          ∃ (hi : idx k < l.val.size),
              v.val[k]'hk = l.val[idx k]'hi) := by
  obtain ⟨hsize, hcorr⟩ := collect_at_correspondence l v hres
  refine ⟨fun k => (positive_indices l l.val.size).getD k 0, ?_, ?_⟩
  · intro k₁ k₂ hk_lt hk₂_lt
    have hk₂' : k₂ < (positive_indices l l.val.size).length := by
      rw [← hsize]; exact hk₂_lt
    exact positive_indices_strict_mono l l.val.size k₁ k₂ hk_lt hk₂'
  · intro k hk
    exact hcorr k hk

/-- Completeness postcondition: every strictly-positive input entry
    appears at some output position. -/
theorem every_positive_input_is_in_output
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_029_get_positive.get_positive l = RustM.ok v)
    (i : Nat) (hi : i < l.val.size)
    (h_pos : (l.val[i]'hi).toInt > 0) :
    ∃ k : Nat, ∃ (hk : k < v.val.size), v.val[k]'hk = l.val[i]'hi := by
  obtain ⟨hsize, hcorr⟩ := collect_at_correspondence l v hres
  have h_i_mem : i ∈ positive_indices l l.val.size :=
    (positive_indices_mem l l.val.size i).mpr ⟨hi, hi, h_pos⟩
  obtain ⟨n, hn_lt, hget⟩ := List.mem_iff_getElem.mp h_i_mem
  have hn_v : n < v.val.size := by rw [hsize]; exact hn_lt
  refine ⟨n, hn_v, ?_⟩
  obtain ⟨hi', hveq⟩ := hcorr n hn_v
  rw [hveq]
  have h_getD_eq :
      (positive_indices l l.val.size).getD n 0 = i := by
    rw [(List.getElem_eq_getD (l := positive_indices l l.val.size)
                              (i := n) (h := hn_lt) 0).symm]
    exact hget
  exact getElem_congr_idx h_getD_eq

end Clever_029_get_positiveObligations
