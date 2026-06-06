-- Companion obligations file for the `clever_041_incr_list` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_041_incr_list

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_041_incr_listObligations

/-! ## Helpers (pattern reused from `clever_021_rescale_to_unit` and
     `clever_009_rolling_max`). -/

/-- `RustM.ok x >>= f = f x`. The library's `pure_bind` simp lemma only
    matches literal `Pure.pure`; this rewrite handles the `RustM.ok` form
    produced after reducing definitions. -/
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

private theorem i64_one_toInt : (1 : i64).toInt = 1 := by decide

/-! ## Push helper for `Vec` (`extend_from_slice` of a 1-element chunk). -/

/-- Push a single element by `extend_from_slice` with a typed 1-element chunk. -/
private def push_one (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec i64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

/-! ## Step lemmas for `incr_at`.

Three branches:
* `i ≥ size` ⇒ returns `RustM.ok acc`.
* `i < size` and no overflow at `numbers[i] + 1` ⇒ extend by `numbers[i] + 1` and recurse.
* `i < size` and overflow at `numbers[i] + 1` ⇒ fail with `integerOverflow`.
-/

/-- Out-of-bounds step: returns the accumulator. -/
private theorem incr_at_oob (numbers : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : numbers.val.size ≤ i.toNat) :
    clever_041_incr_list.incr_at numbers i acc = RustM.ok acc := by
  conv => lhs; unfold clever_041_incr_list.incr_at
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' numbers.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat numbers.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- Successful recursion step: no overflow at `numbers[i] + 1`. -/
private theorem incr_at_step (numbers : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < numbers.val.size)
    (hno_add : ¬ Int64.addOverflow (numbers.val[i.toNat]'hi) (1 : i64))
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_041_incr_list.incr_at numbers i acc =
      clever_041_incr_list.incr_at numbers (i + 1)
        (push_one acc ((numbers.val[i.toNat]'hi) + (1 : i64)) h_acc) := by
  conv => lhs; unfold clever_041_incr_list.incr_at
  have h_size_lt : numbers.val.size < USize64.size := numbers.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond : decide (USize64.ofNat numbers.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (numbers[i]_? : RustM i64) = RustM.ok (numbers.val[i.toNat]'hi) := by
    show (if h : i.toNat < numbers.val.size then pure (numbers.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (numbers.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_no_bv_add :
      BitVec.saddOverflow (numbers.val[i.toNat]'hi).toBitVec (1 : i64).toBitVec = false := by
    cases hb : BitVec.saddOverflow (numbers.val[i.toNat]'hi).toBitVec (1 : i64).toBitVec with
    | false => rfl
    | true => exact absurd hb hno_add
  have h_add_eq :
      ((numbers.val[i.toNat]'hi) +? (1 : i64) : RustM i64) =
        RustM.ok ((numbers.val[i.toNat]'hi) + (1 : i64)) := by
    show (rust_primitives.ops.arith.Add.add (numbers.val[i.toNat]'hi) (1 : i64) : RustM i64) = _
    show (if BitVec.saddOverflow (numbers.val[i.toNat]'hi).toBitVec (1 : i64).toBitVec
          then (.fail .integerOverflow : RustM i64)
          else pure ((numbers.val[i.toNat]'hi) + (1 : i64))) = _
    rw [h_no_bv_add]; rfl
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
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_add_eq]
  -- Reduce unsize and extend_from_slice using the 1-chunk pattern.
  rw [show (rust_primitives.unsize
            (RustArray.ofVec #v[(numbers.val[i.toNat]'hi) + (1 : i64)] : RustArray i64 1)
            : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[(numbers.val[i.toNat]'hi) + (1 : i64)], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size :
      acc.val.size +
        (#[(numbers.val[i.toNat]'hi) + (1 : i64)] : Array i64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size
    exact h_acc
  rw [show (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
              ⟨#[(numbers.val[i.toNat]'hi) + (1 : i64)], one_lt_usize_size⟩
            : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
        = RustM.ok (push_one acc ((numbers.val[i.toNat]'hi) + (1 : i64)) h_acc) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  simp only [RustM_ok_bind]
  rw [h_add_i]
  rfl

/-- Failure step: overflow at `numbers[i] + 1` ⇒ `RustM.fail integerOverflow`. -/
private theorem incr_at_step_fail (numbers : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < numbers.val.size)
    (hov : Int64.addOverflow (numbers.val[i.toNat]'hi) (1 : i64)) :
    clever_041_incr_list.incr_at numbers i acc = RustM.fail Error.integerOverflow := by
  conv => lhs; unfold clever_041_incr_list.incr_at
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' numbers.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat numbers.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (numbers[i]_? : RustM i64) = RustM.ok (numbers.val[i.toNat]'hi) := by
    show (if h : i.toNat < numbers.val.size then pure (numbers.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (numbers.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_bv_true :
      BitVec.saddOverflow (numbers.val[i.toNat]'hi).toBitVec (1 : i64).toBitVec = true := hov
  have h_add_fail :
      ((numbers.val[i.toNat]'hi) +? (1 : i64) : RustM i64) =
        RustM.fail Error.integerOverflow := by
    show (rust_primitives.ops.arith.Add.add (numbers.val[i.toNat]'hi) (1 : i64) : RustM i64) = _
    show (if BitVec.saddOverflow (numbers.val[i.toNat]'hi).toBitVec (1 : i64).toBitVec
          then (.fail .integerOverflow : RustM i64)
          else pure ((numbers.val[i.toNat]'hi) + (1 : i64))) = _
    rw [h_bv_true]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_add_fail]
  rfl

/-! ## Strong induction for `incr_at` — success case.

Mirrors `shift_at_correct` from `clever_021_rescale_to_unit`: at any starting
`(i, acc)` where `acc.val.size = i.toNat` and `acc.val[j].toInt = numbers.val[j].toInt + 1`
for all `j < acc.val.size`, the recursion under the no-overflow precondition
returns a Vec of length `numbers.val.size` with the same elementwise
increment-by-one property extended to the full input. -/

private theorem incr_at_correct (numbers : RustSlice i64)
    (hfit : ∀ (j : Nat) (hj : j < numbers.val.size),
              ¬ Int64.addOverflow (numbers.val[j]'hj) (1 : i64)) :
    ∀ (k : Nat) (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global),
      numbers.val.size - i.toNat ≤ k →
      i.toNat ≤ numbers.val.size →
      acc.val.size = i.toNat →
      (∀ (j : Nat) (hj : j < acc.val.size) (hj_n : j < numbers.val.size),
          (acc.val[j]'hj).toInt = (numbers.val[j]'hj_n).toInt + 1) →
      ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
        clever_041_incr_list.incr_at numbers i acc = RustM.ok v ∧
        v.val.size = numbers.val.size ∧
        (∀ (j : Nat) (hj : j < v.val.size) (hj_n : j < numbers.val.size),
            (v.val[j]'hj).toInt = (numbers.val[j]'hj_n).toInt + 1) := by
  intro k
  induction k with
  | zero =>
    intro i acc hk hi_le h_acc_size h_acc_chunk
    have hi_eq : i.toNat = numbers.val.size := by omega
    have hi_ge : numbers.val.size ≤ i.toNat := by omega
    refine ⟨acc, incr_at_oob numbers i acc hi_ge, ?_, ?_⟩
    · rw [h_acc_size, hi_eq]
    · intros j hj hj_n; exact h_acc_chunk j hj hj_n
  | succ k ih =>
    intro i acc hk hi_le h_acc_size h_acc_chunk
    by_cases hi_ge : numbers.val.size ≤ i.toNat
    · have hi_eq : i.toNat = numbers.val.size := by omega
      refine ⟨acc, incr_at_oob numbers i acc hi_ge, ?_, ?_⟩
      · rw [h_acc_size, hi_eq]
      · intros j hj hj_n; exact h_acc_chunk j hj hj_n
    · have hi_lt : i.toNat < numbers.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : numbers.val.size < USize64.size := numbers.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_acc_succ : acc.val.size + 1 < USize64.size := by
        rw [h_acc_size, h_usize_size]; omega
      have hno_add_i : ¬ Int64.addOverflow (numbers.val[i.toNat]'hi_lt) (1 : i64) :=
        hfit i.toNat hi_lt
      have h_step := incr_at_step numbers i acc hi_lt hno_add_i h_acc_succ
      rw [h_step]
      -- Establish acc' invariants for IH.
      have h_acc'_size :
          (push_one acc ((numbers.val[i.toNat]'hi_lt) + (1 : i64)) h_acc_succ).val.size
            = (i + 1).toNat := by
        show (acc.val ++ #[_]).size = (i + 1).toNat
        rw [Array.size_append, h_i1, h_acc_size]
        rfl
      have h_acc'_chunk :
          ∀ (j : Nat)
            (hj : j <
              (push_one acc ((numbers.val[i.toNat]'hi_lt) + (1 : i64)) h_acc_succ).val.size)
            (hj_n : j < numbers.val.size),
            ((push_one acc ((numbers.val[i.toNat]'hi_lt) + (1 : i64)) h_acc_succ).val[j]'hj).toInt
              = (numbers.val[j]'hj_n).toInt + 1 := by
        intro j hj hj_n
        show ((acc.val ++ #[(numbers.val[i.toNat]'hi_lt) + (1 : i64)])[j]'hj).toInt = _
        by_cases hjlt : j < acc.val.size
        · rw [Array.getElem_append_left hjlt]
          exact h_acc_chunk j hjlt hj_n
        · -- j = acc.val.size = i.toNat
          have h_size_raw :
              (acc.val ++ #[(numbers.val[i.toNat]'hi_lt) + (1 : i64)]).size
                = acc.val.size + 1 := by rw [Array.size_append]; rfl
          have hj_eq : j = acc.val.size := by
            have : j < acc.val.size + 1 := by rw [← h_size_raw]; exact hj
            omega
          subst hj_eq
          rw [Array.getElem_append_right (Nat.le_refl _)]
          simp only [Nat.sub_self]
          show ((numbers.val[i.toNat]'hi_lt) + (1 : i64)).toInt = _
          rw [Int64.toInt_add_of_not_addOverflow hno_add_i, i64_one_toInt]
          have h_num_eq :
              numbers.val[i.toNat]'hi_lt = numbers.val[acc.val.size]'hj_n :=
            getElem_congr_idx h_acc_size.symm
          rw [h_num_eq]
      have h_i1_le : (i + 1).toNat ≤ numbers.val.size := by rw [h_i1]; omega
      have h_k_le : numbers.val.size - (i + 1).toNat ≤ k := by rw [h_i1]; omega
      exact ih (i + 1) _ h_k_le h_i1_le h_acc'_size h_acc'_chunk

/-! ## Strong induction for `incr_at` — failure case.

If there exists some `j ∈ [i.toNat, numbers.val.size)` whose `numbers[j] + 1`
overflows in `i64`, then `incr_at numbers i acc` fails with
`Error.integerOverflow`. The proof is by strong induction on
`numbers.val.size - i.toNat`. At each step we either fail at `i.toNat`
directly (via `incr_at_step_fail`) or, if `i.toNat` itself doesn't overflow,
step forward and apply the IH at `i + 1`. -/

private theorem incr_at_fails_when_overflow (numbers : RustSlice i64) :
    ∀ (k : Nat) (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global),
      numbers.val.size - i.toNat ≤ k →
      i.toNat ≤ numbers.val.size →
      acc.val.size = i.toNat →
      (∃ (j : Nat) (hj : j < numbers.val.size), i.toNat ≤ j ∧
        Int64.addOverflow (numbers.val[j]'hj) (1 : i64)) →
      clever_041_incr_list.incr_at numbers i acc = RustM.fail Error.integerOverflow := by
  intro k
  induction k with
  | zero =>
    intro i acc hk hi_le h_acc_size hov
    exfalso
    obtain ⟨j, hj, h_ji, _⟩ := hov
    -- i.toNat = numbers.val.size, but j < size and i.toNat ≤ j ⇒ contradiction
    omega
  | succ k ih =>
    intro i acc hk hi_le h_acc_size hov
    obtain ⟨j, hj, h_ji, hov_at_j⟩ := hov
    have hi_lt : i.toNat < numbers.val.size := by omega
    have h_size_lt : numbers.val.size < USize64.size := numbers.size_lt_usizeSize
    have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
    -- Case-split on overflow at i.toNat itself.
    by_cases hov_at_i : Int64.addOverflow (numbers.val[i.toNat]'hi_lt) (1 : i64)
    · -- Failure at current index: apply step_fail.
      exact incr_at_step_fail numbers i acc hi_lt hov_at_i
    · -- No overflow at i.toNat: the witness j must be > i.toNat. Step forward and IH.
      have h_j_gt_i : i.toNat < j := by
        rcases Nat.lt_or_ge i.toNat j with h | h
        · exact h
        · -- h : j ≤ i.toNat, combined with h_ji : i.toNat ≤ j gives j = i.toNat,
          -- so overflow at j = overflow at i.toNat — contradicts hov_at_i.
          exfalso
          have h_j_eq : j = i.toNat := by omega
          apply hov_at_i
          have h_num_eq : numbers.val[j]'hj = numbers.val[i.toNat]'hi_lt :=
            getElem_congr_idx h_j_eq
          rw [← h_num_eq]; exact hov_at_j
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_acc_succ : acc.val.size + 1 < USize64.size := by
        rw [h_acc_size, h_usize_size]; omega
      have h_step := incr_at_step numbers i acc hi_lt hov_at_i h_acc_succ
      rw [h_step]
      -- IH at i+1.
      have h_acc'_size :
          (push_one acc ((numbers.val[i.toNat]'hi_lt) + (1 : i64)) h_acc_succ).val.size
            = (i + 1).toNat := by
        show (acc.val ++ #[_]).size = (i + 1).toNat
        rw [Array.size_append, h_i1, h_acc_size]
        rfl
      have h_i1_le : (i + 1).toNat ≤ numbers.val.size := by rw [h_i1]; omega
      have h_k_le : numbers.val.size - (i + 1).toNat ≤ k := by rw [h_i1]; omega
      have h_j_ge_next : (i + 1).toNat ≤ j := by rw [h_i1]; omega
      exact ih (i + 1) _ h_k_le h_i1_le h_acc'_size
              ⟨j, hj, h_j_ge_next, hov_at_j⟩

/-! ## Bridge from `incr_at` to `incr_list`. -/

/-- Combined success-case auxiliary: `incr_list` returns `RustM.ok` of a Vec
    whose elements are `numbers[j].toInt + 1`. -/
private theorem incr_list_aux
    (numbers : RustSlice i64)
    (hfit : ∀ (j : Nat) (hj : j < numbers.val.size),
              ¬ Int64.addOverflow (numbers.val[j]'hj) (1 : i64)) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_041_incr_list.incr_list numbers = RustM.ok v ∧
      v.val.size = numbers.val.size ∧
      (∀ (j : Nat) (hj_v : j < v.val.size) (hj_n : j < numbers.val.size),
          (v.val[j]'hj_v).toInt = (numbers.val[j]'hj_n).toInt + 1) := by
  unfold clever_041_incr_list.incr_list
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new, RustM_ok_bind]
  let acc0 : alloc.vec.Vec i64 alloc.alloc.Global := ⟨(List.nil).toArray, by grind⟩
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_acc0_size : acc0.val.size = (0 : usize).toNat := by
    show (List.nil : List i64).toArray.size = 0
    rfl
  have h_acc0_chunk :
      ∀ (j : Nat) (hj : j < acc0.val.size) (hj_n : j < numbers.val.size),
        (acc0.val[j]'hj).toInt = (numbers.val[j]'hj_n).toInt + 1 := by
    intros j hj _
    exfalso
    have h0 : acc0.val.size = 0 := rfl
    rw [h0] at hj
    omega
  have h_k_le : numbers.val.size - (0 : usize).toNat ≤ numbers.val.size := by
    rw [h_zero_toNat]; omega
  have h_i_le : (0 : usize).toNat ≤ numbers.val.size := by
    rw [h_zero_toNat]; omega
  exact incr_at_correct numbers hfit numbers.val.size (0 : usize) acc0
          h_k_le h_i_le h_acc0_size h_acc0_chunk

/-- Combined failure-case auxiliary: if any element of `numbers` overflows
    on `+1`, then `incr_list numbers` fails with `Error.integerOverflow`. -/
private theorem incr_list_fail_aux
    (numbers : RustSlice i64)
    (hov : ∃ (j : Nat) (hj : j < numbers.val.size),
             Int64.addOverflow (numbers.val[j]'hj) (1 : i64)) :
    clever_041_incr_list.incr_list numbers = RustM.fail Error.integerOverflow := by
  unfold clever_041_incr_list.incr_list
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new, RustM_ok_bind]
  let acc0 : alloc.vec.Vec i64 alloc.alloc.Global := ⟨(List.nil).toArray, by grind⟩
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_acc0_size : acc0.val.size = (0 : usize).toNat := by
    show (List.nil : List i64).toArray.size = 0
    rfl
  have h_k_le : numbers.val.size - (0 : usize).toNat ≤ numbers.val.size := by
    rw [h_zero_toNat]; omega
  have h_i_le : (0 : usize).toNat ≤ numbers.val.size := by
    rw [h_zero_toNat]; omega
  obtain ⟨j, hj, hov_at_j⟩ := hov
  apply incr_at_fails_when_overflow numbers numbers.val.size (0 : usize) acc0
    h_k_le h_i_le h_acc0_size
  refine ⟨j, hj, ?_, hov_at_j⟩
  rw [h_zero_toNat]; omega

/-! ## Postcondition theorems

These capture the proptest `incr_list_matches_elementwise_increment`. The
single Rust assertion `prop_assert_eq!(incr_list(&numbers), expected)`
encodes three independent claims a buggy implementation might violate:

* totality — a Vec is returned at all (rather than a panic / fail);
* length preservation — the returned Vec has the same length as the input;
* per-index value — each output element equals `numbers[i] + 1`.

Each one is stated as its own theorem so a partial proof can still close
the others. The precondition is the per-element overflow guard: for every
in-bounds `j`, the i64 addition `numbers[j] + 1` does not overflow. -/

/-- Totality: under the per-element no-overflow precondition, `incr_list`
    returns `RustM.ok` of some Vec. -/
theorem incr_list_total
    (numbers : RustSlice i64)
    (hfit : ∀ (j : Nat) (hj : j < numbers.val.size),
              ¬ Int64.addOverflow (numbers.val[j]'hj) (1 : i64)) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_041_incr_list.incr_list numbers = RustM.ok v := by
  obtain ⟨v, hres, _, _⟩ := incr_list_aux numbers hfit
  exact ⟨v, hres⟩

/-- Length preservation: whenever `incr_list` succeeds, the returned Vec
    has the same size as the input slice. -/
theorem incr_list_length
    (numbers : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_041_incr_list.incr_list numbers = RustM.ok v) :
    v.val.size = numbers.val.size := by
  -- Case-split on whether any element overflows. If yes, the function would
  -- fail rather than succeed — contradiction with `hres`. If no, apply the aux.
  by_cases hany_ov :
      ∃ (j : Nat) (hj : j < numbers.val.size),
        Int64.addOverflow (numbers.val[j]'hj) (1 : i64)
  · exfalso
    have h_fail := incr_list_fail_aux numbers hany_ov
    rw [h_fail] at hres
    cases hres
  · have hfit : ∀ (j : Nat) (hj : j < numbers.val.size),
                  ¬ Int64.addOverflow (numbers.val[j]'hj) (1 : i64) := by
      intro j hj h_ov
      exact hany_ov ⟨j, hj, h_ov⟩
    obtain ⟨v', hres', hlen, _⟩ := incr_list_aux numbers hfit
    rw [hres'] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    exact hlen

/-- Elementwise increment: whenever `incr_list` succeeds, the `j`-th element
    of the returned Vec equals `numbers[j] + 1` (compared as `Int`s, which
    avoids the spec itself overflowing). -/
theorem incr_list_elementwise
    (numbers : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_041_incr_list.incr_list numbers = RustM.ok v)
    (j : Nat) (hj_v : j < v.val.size) (hj_n : j < numbers.val.size) :
    (v.val[j]'hj_v).toInt = (numbers.val[j]'hj_n).toInt + 1 := by
  by_cases hany_ov :
      ∃ (k : Nat) (hk : k < numbers.val.size),
        Int64.addOverflow (numbers.val[k]'hk) (1 : i64)
  · exfalso
    have h_fail := incr_list_fail_aux numbers hany_ov
    rw [h_fail] at hres
    cases hres
  · have hfit : ∀ (k : Nat) (hk : k < numbers.val.size),
                  ¬ Int64.addOverflow (numbers.val[k]'hk) (1 : i64) := by
      intro k hk h_ov
      exact hany_ov ⟨k, hk, h_ov⟩
    obtain ⟨v', hres', _, helem⟩ := incr_list_aux numbers hfit
    rw [hres'] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    exact helem j hj_v hj_n

/-! ## Failure condition

Captures the `#[should_panic]` test `incr_list_panics_on_i64_max_element`,
which exhibits the slice `[0, 1, i64::MAX, 2]`. The general contract clause
is that whenever any element of the input would overflow `i64` on `+1`, the
function fails with `Error.integerOverflow` rather than silently returning a
wrong value. -/

/-- Overflow failure: if some element of `numbers` causes `+1` to overflow
    in `i64`, then `incr_list` fails with `Error.integerOverflow`. -/
theorem incr_list_overflow_fails
    (numbers : RustSlice i64)
    (hov : ∃ (j : Nat) (hj : j < numbers.val.size),
             Int64.addOverflow (numbers.val[j]'hj) (1 : i64)) :
    clever_041_incr_list.incr_list numbers = RustM.fail Error.integerOverflow :=
  incr_list_fail_aux numbers hov

end Clever_041_incr_listObligations
