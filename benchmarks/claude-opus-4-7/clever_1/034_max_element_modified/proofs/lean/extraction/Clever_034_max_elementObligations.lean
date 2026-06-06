-- Companion obligations file for the `clever_034_max_element` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_034_max_element

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_034_max_elementObligations

/-! ## Helpers (pattern transferred from `rescale_to_unit_modified` / `clever_009_rolling_max_modified`). -/

/-- `RustM.ok x >>= f = f x`. The library's `pure_bind` simp lemma only
    matches literal `Pure.pure`; this rewrite handles the `RustM.ok` form
    produced after reducing definitions. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

/-! ## `is_empty` reductions on a slice (both branches).

The Rust `max_element` opens with `if l.is_empty()`. The Hax-extracted
encoding routes this through `core_models.slice.Impl.is_empty`, which
unfolds to `(len s) ==? (0 : usize)`. We pre-prove both reduction lemmas
so the top-level proof can rewrite the branch directly. -/

private theorem is_empty_true_of_empty (l : RustSlice i64) (h : l.val.size = 0) :
    core_models.slice.Impl.is_empty i64 l = RustM.ok true := by
  show ((core_models.slice.Impl.len i64 l : RustM usize) >>= fun len =>
          (rust_primitives.cmp.eq len (0 : usize) : RustM Bool)) = _
  show ((rust_primitives.slice.slice_length i64 l : RustM usize) >>= fun len =>
          (rust_primitives.cmp.eq len (0 : usize) : RustM Bool)) = _
  show (pure (USize64.ofNat l.val.size) >>= fun len =>
          (rust_primitives.cmp.eq len (0 : usize) : RustM Bool)) = _
  rw [pure_bind]
  show (pure ((USize64.ofNat l.val.size) == (0 : usize)) : RustM Bool) = RustM.ok true
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_eq : USize64.ofNat l.val.size = (0 : usize) := by
    apply USize64.toNat_inj.mp
    rw [h_ofNat, h]; rfl
  rw [h_eq]
  rfl

private theorem is_empty_false_of_nonempty (l : RustSlice i64) (h : 0 < l.val.size) :
    core_models.slice.Impl.is_empty i64 l = RustM.ok false := by
  show ((core_models.slice.Impl.len i64 l : RustM usize) >>= fun len =>
          (rust_primitives.cmp.eq len (0 : usize) : RustM Bool)) = _
  show ((rust_primitives.slice.slice_length i64 l : RustM usize) >>= fun len =>
          (rust_primitives.cmp.eq len (0 : usize) : RustM Bool)) = _
  show (pure (USize64.ofNat l.val.size) >>= fun len =>
          (rust_primitives.cmp.eq len (0 : usize) : RustM Bool)) = _
  rw [pure_bind]
  show (pure ((USize64.ofNat l.val.size) == (0 : usize)) : RustM Bool) = RustM.ok false
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_ne : USize64.ofNat l.val.size ≠ (0 : usize) := by
    intro he
    have h_toNat_eq : (USize64.ofNat l.val.size).toNat = (0 : usize).toNat := by rw [he]
    rw [h_ofNat] at h_toNat_eq
    -- (0 : usize).toNat = 0 by rfl
    show False
    have : l.val.size = 0 := h_toNat_eq
    omega
  rw [show ((USize64.ofNat l.val.size) == (0 : usize)) = false from by
    rw [beq_eq_false_iff_ne]; exact h_ne]
  rfl

/-! ## Step lemmas for `max_at`.

Three branches of the recursive body:
* `i ≥ size` ⇒ returns `m`
* `i < size` and `l[i] > m`  ⇒ recurses with `m := l[i]`
* `i < size` and `l[i] ≤ m`  ⇒ recurses with same `m`
-/

private theorem max_at_oob (l : RustSlice i64) (i : usize) (m : i64)
    (hi : l.val.size ≤ i.toNat) :
    clever_034_max_element.max_at l i m = RustM.ok m := by
  conv => lhs; unfold clever_034_max_element.max_at
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

private theorem max_at_step_gt (l : RustSlice i64) (i : usize) (m : i64)
    (hi : i.toNat < l.val.size)
    (hgt : m.toInt < (l.val[i.toNat]'hi).toInt) :
    clever_034_max_element.max_at l i m =
      clever_034_max_element.max_at l (i + 1) (l.val[i.toNat]'hi) := by
  conv => lhs; unfold clever_034_max_element.max_at
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
    rw [dif_pos hi]
    rfl
  have h_gt_cond : decide ((l.val[i.toNat]'hi) > m) = true := by
    rw [decide_eq_true_iff]
    exact Int64.lt_iff_toInt_lt.mpr hgt
  have h_no_overflow_i : i.toNat + 1 < 2^64 := by
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
  have h_add_eq : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
    show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
    show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
          then (.fail .integerOverflow : RustM usize)
          else pure (i + 1)) = _
    rw [h_no_bv_i]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, rust_primitives.cmp.gt, h_gt_cond, h_add_eq]

private theorem max_at_step_le (l : RustSlice i64) (i : usize) (m : i64)
    (hi : i.toNat < l.val.size)
    (hle : (l.val[i.toNat]'hi).toInt ≤ m.toInt) :
    clever_034_max_element.max_at l i m =
      clever_034_max_element.max_at l (i + 1) m := by
  conv => lhs; unfold clever_034_max_element.max_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle'
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle'
    omega
  have h_idx : (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_gt_cond : decide ((l.val[i.toNat]'hi) > m) = false := by
    rw [decide_eq_false_iff_not]
    intro h_gt
    have h_lt : m.toInt < (l.val[i.toNat]'hi).toInt := Int64.lt_iff_toInt_lt.mp h_gt
    omega
  have h_no_overflow_i : i.toNat + 1 < 2^64 := by
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
  have h_add_eq : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
    show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
    show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
          then (.fail .integerOverflow : RustM usize)
          else pure (i + 1)) = _
    rw [h_no_bv_i]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx, rust_primitives.cmp.gt, h_gt_cond, h_add_eq]

/-! ## Strong induction for `max_at`.

For input `max_at l i m`, the result `r : i64` satisfies a
*maximum-over-suffix-of-l* property — the exact dual of `min_at_correct`
in `rescale_to_unit_modified`:
  - `m.toInt ≤ r.toInt` (the result dominates the seed)
  - `(l[j]).toInt ≤ r.toInt` for every `j ∈ [i, size)`
  - either `r = m`, or `r = l[j]` for some `j ∈ [i, size)`
-/

private theorem max_at_correct (l : RustSlice i64) :
    ∀ (k : Nat) (i : usize) (m : i64),
      l.val.size - i.toNat ≤ k →
      i.toNat ≤ l.val.size →
      ∃ r : i64,
        clever_034_max_element.max_at l i m = RustM.ok r ∧
        m.toInt ≤ r.toInt ∧
        (∀ (j : Nat) (hj : j < l.val.size), i.toNat ≤ j →
            (l.val[j]'hj).toInt ≤ r.toInt) ∧
        (r = m ∨
            ∃ (j : Nat) (hj : j < l.val.size),
              i.toNat ≤ j ∧ r = l.val[j]'hj) := by
  intro k
  induction k with
  | zero =>
    intro i m hm hi_le
    have hi_eq : i.toNat = l.val.size := by omega
    have hi_ge : l.val.size ≤ i.toNat := by omega
    refine ⟨m, max_at_oob l i m hi_ge, Int.le_refl _, ?_, Or.inl rfl⟩
    intro j hj h_ile
    rw [hi_eq] at h_ile
    omega
  | succ k ih =>
    intro i m hm hi_le
    by_cases hi_ge : l.val.size ≤ i.toNat
    · refine ⟨m, max_at_oob l i m hi_ge, Int.le_refl _, ?_, Or.inl rfl⟩
      intro j hj h_ile
      omega
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_k_le : l.val.size - (i + 1).toNat ≤ k := by rw [h_i1]; omega
      by_cases hgt : m.toInt < (l.val[i.toNat]'hi_lt).toInt
      · -- Take the "gt" branch: recurse with new seed l[i].
        have h_step := max_at_step_gt l i m hi_lt hgt
        obtain ⟨r, hres, h_r_ge_seed, h_r_ub, h_r_eq⟩ :=
          ih (i + 1) (l.val[i.toNat]'hi_lt) h_k_le h_i1_le
        refine ⟨r, ?_, ?_, ?_, ?_⟩
        · rw [h_step]; exact hres
        · -- m.toInt < l[i].toInt ≤ r.toInt
          have := h_r_ge_seed
          omega
        · intro j hj h_ile
          by_cases h_jeq : j = i.toNat
          · -- l[j].toInt = l[i].toInt ≤ r.toInt from h_r_ge_seed
            subst h_jeq; exact h_r_ge_seed
          · have h_jgt : i.toNat + 1 ≤ j := by omega
            have h_jgt' : (i + 1).toNat ≤ j := by rw [h_i1]; exact h_jgt
            exact h_r_ub j hj h_jgt'
        · rcases h_r_eq with h_r_eq_seed | ⟨j, hj, h_jle, h_r_eq_j⟩
          · -- r = l[i]; witness j = i.toNat
            refine Or.inr ⟨i.toNat, hi_lt, Nat.le_refl _, h_r_eq_seed⟩
          · -- r = l[j] with (i+1).toNat ≤ j; j ≥ i.toNat too
            rw [h_i1] at h_jle
            refine Or.inr ⟨j, hj, by omega, h_r_eq_j⟩
      · -- Take the "le" branch: keep m.
        have hle : (l.val[i.toNat]'hi_lt).toInt ≤ m.toInt := by omega
        have h_step := max_at_step_le l i m hi_lt hle
        obtain ⟨r, hres, h_r_ge_seed, h_r_ub, h_r_eq⟩ :=
          ih (i + 1) m h_k_le h_i1_le
        refine ⟨r, ?_, h_r_ge_seed, ?_, ?_⟩
        · rw [h_step]; exact hres
        · intro j hj h_ile
          by_cases h_jeq : j = i.toNat
          · -- l[i].toInt ≤ m.toInt ≤ r.toInt
            subst h_jeq; omega
          · have h_jgt : (i + 1).toNat ≤ j := by rw [h_i1]; omega
            exact h_r_ub j hj h_jgt
        · rcases h_r_eq with h_r_eq_m | ⟨j, hj, h_jle, h_r_eq_j⟩
          · exact Or.inl h_r_eq_m
          · rw [h_i1] at h_jle
            refine Or.inr ⟨j, hj, by omega, h_r_eq_j⟩

/-! ## Auxiliary lemma for the non-empty case of `max_element`. -/

private theorem max_element_aux_nonempty
    (l : RustSlice i64) (hne : 0 < l.val.size) :
    ∃ r : i64,
      clever_034_max_element.max_element l = RustM.ok r ∧
      (∀ (j : Nat) (hj : j < l.val.size), (l.val[j]'hj).toInt ≤ r.toInt) ∧
      (∃ (j : Nat) (hj : j < l.val.size), r = l.val[j]'hj) := by
  unfold clever_034_max_element.max_element
  -- Reduce is_empty to ok false.
  rw [is_empty_false_of_nonempty l hne]
  simp only [RustM_ok_bind, Bool.false_eq_true, ↓reduceIte]
  -- Reduce indexing at 0.
  have h_zero_lt : (0 : Nat) < l.val.size := hne
  have h_zero_lt_usize : (0 : usize).toNat < l.val.size := h_zero_lt
  have h_idx_0 : (l[(0 : usize)]_? : RustM i64) = RustM.ok (l.val[0]'h_zero_lt) := by
    show (if h : (0 : usize).toNat < l.val.size then pure (l.val[(0 : usize)])
            else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[0]'h_zero_lt)
    rw [dif_pos h_zero_lt_usize]
    rfl
  rw [h_idx_0]
  simp only [RustM_ok_bind]
  -- Apply max_at_correct at (1 : usize) with seed l[0].
  have h_one_le : (1 : usize).toNat ≤ l.val.size := by
    rw [usize_one_toNat]; omega
  have h_meas : l.val.size - (1 : usize).toNat ≤ l.val.size := by
    rw [usize_one_toNat]; omega
  obtain ⟨r, hres, h_r_ge_seed, h_r_ub_suffix, h_r_eq⟩ :=
    max_at_correct l l.val.size (1 : usize) (l.val[0]'h_zero_lt) h_meas h_one_le
  refine ⟨r, hres, ?_, ?_⟩
  · -- upper-bound clause for all j
    intro j hj
    rcases Nat.lt_or_ge j 1 with h_j0 | h_j1
    · have hj_eq : j = 0 := by omega
      subst hj_eq
      exact h_r_ge_seed
    · have h_j_ge_one : (1 : usize).toNat ≤ j := by rw [usize_one_toNat]; exact h_j1
      exact h_r_ub_suffix j hj h_j_ge_one
  · -- existential witness clause
    rcases h_r_eq with h_r_eq_seed | ⟨j, hj, _, h_r_eq_j⟩
    · exact ⟨0, h_zero_lt, h_r_eq_seed⟩
    · exact ⟨j, hj, h_r_eq_j⟩

/-! ## Top-level theorems. -/

/-- Empty-slice boundary contract: `max_element []` returns the sentinel
    value `0`.  Captures the `empty_list_returns_zero` unit test. -/
theorem max_element_empty_returns_zero
    (l : RustSlice i64) (hempty : l.val.size = 0) :
    clever_034_max_element.max_element l = RustM.ok (0 : i64) := by
  unfold clever_034_max_element.max_element
  rw [is_empty_true_of_empty l hempty]
  simp only [RustM_ok_bind, ↓reduceIte]
  rfl

/-- Totality: `max_element` produces an `ok` result on every input
    (including the empty slice).  Captures the `never_panics` proptest
    — it asserts that the function neither faults on indexing nor
    overflows on the recursion's `usize` increment. -/
theorem max_element_total
    (l : RustSlice i64) :
    ∃ r : i64, clever_034_max_element.max_element l = RustM.ok r := by
  by_cases hempty : l.val.size = 0
  · exact ⟨(0 : i64), max_element_empty_returns_zero l hempty⟩
  · have hne : 0 < l.val.size := by omega
    obtain ⟨r, hres, _, _⟩ := max_element_aux_nonempty l hne
    exact ⟨r, hres⟩

/-- Postcondition (non-empty, "element-of"): the returned value is one of
    the slice's actual elements.  Captures the proptest
    `result_is_an_element_of_the_list`.  This is independent of the
    upper-bound clause: an impl that returned `i64::MAX` (or `r := max + 1`)
    would still dominate every element but would not be present in `l`. -/
theorem max_element_returned_is_an_element_of_the_list
    (l : RustSlice i64) (hne : 0 < l.val.size)
    (r : i64)
    (hres : clever_034_max_element.max_element l = RustM.ok r) :
    ∃ (j : Nat) (hj : j < l.val.size), r = l.val[j]'hj := by
  obtain ⟨r', hres', _, hwit⟩ := max_element_aux_nonempty l hne
  rw [hres'] at hres
  injection hres with h_eq
  injection h_eq with h_eq'
  subst h_eq'
  exact hwit

/-- Postcondition (upper bound): the returned value dominates every element
    of `l`.  Captures the proptest `result_is_an_upper_bound`.  Stated for
    arbitrary `l`: for the empty case `l.val.size = 0` the universal
    quantifier over `j < l.val.size` is vacuous, so no separate boundary
    hypothesis is needed.  This is independent of the "in the list" clause:
    an impl that returned `l[0]` (i.e. always the head) would still lie
    inside `l` but would not be an upper bound for arbitrary inputs. -/
theorem max_element_is_an_upper_bound
    (l : RustSlice i64)
    (r : i64)
    (hres : clever_034_max_element.max_element l = RustM.ok r)
    (j : Nat) (hj : j < l.val.size) :
    (l.val[j]'hj).toInt ≤ r.toInt := by
  -- j < l.val.size forces l non-empty.
  have hne : 0 < l.val.size := by omega
  obtain ⟨r', hres', hub, _⟩ := max_element_aux_nonempty l hne
  rw [hres'] at hres
  injection hres with h_eq
  injection h_eq with h_eq'
  subst h_eq'
  exact hub j hj

end Clever_034_max_elementObligations
