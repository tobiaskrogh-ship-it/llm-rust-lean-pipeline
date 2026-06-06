-- Companion obligations file for the `clever_021_rescale_to_unit` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_021_rescale_to_unit

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_021_rescale_to_unitObligations

/-! ## Helpers (pattern reused from `clever_009_rolling_max` + `below_zero`). -/

/-- `RustM.ok x >>= f = f x`. The library's `pure_bind` simp lemma only
    matches literal `Pure.pure`; this rewrite handles the `RustM.ok` form
    produced after reducing definitions. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

private theorem usize_two_toNat : (2 : usize).toNat = 2 := rfl

private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide

private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide

/-! ## Push helper for `Vec` (`extend_from_slice` of a 1-element chunk). -/

/-- Push a single element. -/
private def push_one (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec i64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

/-! ## Min oracle (Int-valued running minimum of a slice).

`slice_min_int numbers i m` is the minimum, taken in `Int`, of `m` together
with `numbers[i], numbers[i+1], …, numbers[size-1]`. This is the value
returned by `min_at numbers i m` (as an `Int`, via `.toInt`). -/

private def slice_min_int (numbers : RustSlice i64) (m : Int) : Nat → Int
  | 0     => m
  | k + 1 =>
      if h : k < numbers.val.size then
        let r := slice_min_int numbers m k
        if (numbers.val[k]'h).toInt < r then (numbers.val[k]'h).toInt else r
      else
        slice_min_int numbers m k

/-! Note on the indexing convention.

`slice_min_int numbers m k` is the running minimum after considering the
first `k` slice entries together with the initial value `m`. The recursion
in `min_at numbers i m` walks `i, i+1, …, size-1`, so the result of
`min_at numbers 0 numbers[0]` equals `slice_min_int numbers numbers[0].toInt size`.
For the top-level call `min_at numbers 1 numbers[0]`, the result equals the
minimum over `numbers[0..size]` — i.e. `slice_min_int` viewing index `1` as
the "have seen `numbers[0]` already" boundary. -/

/-! ## Step lemmas for `min_at`.

Three branches of the recursive body:
* `i ≥ size` ⇒ returns `m`
* `i < size` and `numbers[i] < m` ⇒ recurses with `m := numbers[i]`
* `i < size` and `numbers[i] ≥ m` ⇒ recurses with same `m`
-/

private theorem min_at_oob (numbers : RustSlice i64) (i : usize) (m : i64)
    (hi : numbers.val.size ≤ i.toNat) :
    clever_021_rescale_to_unit.min_at numbers i m = RustM.ok m := by
  conv => lhs; unfold clever_021_rescale_to_unit.min_at
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

private theorem min_at_step_lt (numbers : RustSlice i64) (i : usize) (m : i64)
    (hi : i.toNat < numbers.val.size)
    (hlt : (numbers.val[i.toNat]'hi).toInt < m.toInt) :
    clever_021_rescale_to_unit.min_at numbers i m =
      clever_021_rescale_to_unit.min_at numbers (i + 1) (numbers.val[i.toNat]'hi) := by
  conv => lhs; unfold clever_021_rescale_to_unit.min_at
  have h_size_lt : numbers.val.size < USize64.size := numbers.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat numbers.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (numbers[i]_? : RustM i64) = RustM.ok (numbers.val[i.toNat]'hi) := by
    show (if h : i.toNat < numbers.val.size then pure (numbers.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (numbers.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
  have h_lt_cond : decide ((numbers.val[i.toNat]'hi) < m) = true := by
    rw [decide_eq_true_iff]
    rw [Int64.lt_iff_toInt_lt]
    exact hlt
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
             h_idx, rust_primitives.cmp.lt, h_lt_cond, h_add_eq]

private theorem min_at_step_ge (numbers : RustSlice i64) (i : usize) (m : i64)
    (hi : i.toNat < numbers.val.size)
    (hge : m.toInt ≤ (numbers.val[i.toNat]'hi).toInt) :
    clever_021_rescale_to_unit.min_at numbers i m =
      clever_021_rescale_to_unit.min_at numbers (i + 1) m := by
  conv => lhs; unfold clever_021_rescale_to_unit.min_at
  have h_size_lt : numbers.val.size < USize64.size := numbers.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat numbers.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (numbers[i]_? : RustM i64) = RustM.ok (numbers.val[i.toNat]'hi) := by
    show (if h : i.toNat < numbers.val.size then pure (numbers.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (numbers.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_lt_cond : decide ((numbers.val[i.toNat]'hi) < m) = false := by
    rw [decide_eq_false_iff_not]
    rw [Int64.lt_iff_toInt_lt]
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
             h_idx, rust_primitives.cmp.lt, h_lt_cond, h_add_eq]

/-! ## Strong induction for `min_at`.

For input `min_at numbers i m`, the result `r : i64` satisfies a
*minimum-over-suffix-of-numbers* property:
  - `r.toInt ≤ m.toInt` (the result is bounded above by the seed)
  - `r.toInt ≤ numbers[j].toInt` for every `j ∈ [i, size)`
  - `r.toInt = m.toInt`, or `r.toInt = numbers[j].toInt` for some `j ∈ [i, size)`
-/

private theorem min_at_correct (numbers : RustSlice i64) :
    ∀ (k : Nat) (i : usize) (m : i64),
      numbers.val.size - i.toNat ≤ k →
      i.toNat ≤ numbers.val.size →
      ∃ r : i64,
        clever_021_rescale_to_unit.min_at numbers i m = RustM.ok r ∧
        r.toInt ≤ m.toInt ∧
        (∀ (j : Nat) (hj : j < numbers.val.size), i.toNat ≤ j →
            r.toInt ≤ (numbers.val[j]'hj).toInt) ∧
        (r.toInt = m.toInt ∨
            ∃ (j : Nat) (hj : j < numbers.val.size),
              i.toNat ≤ j ∧ r.toInt = (numbers.val[j]'hj).toInt) := by
  intro k
  induction k with
  | zero =>
    intro i m hm hi_le
    have hi_eq : i.toNat = numbers.val.size := by omega
    have hi_ge : numbers.val.size ≤ i.toNat := by omega
    refine ⟨m, min_at_oob numbers i m hi_ge, by omega, ?_, Or.inl rfl⟩
    intro j hj h_ile
    -- i.toNat = size ≤ j and j < size is contradictory
    rw [hi_eq] at h_ile
    omega
  | succ k ih =>
    intro i m hm hi_le
    by_cases hi_ge : numbers.val.size ≤ i.toNat
    · refine ⟨m, min_at_oob numbers i m hi_ge, by omega, ?_, Or.inl rfl⟩
      intro j hj h_ile
      omega
    · have hi_lt : i.toNat < numbers.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : numbers.val.size < USize64.size := numbers.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ numbers.val.size := by rw [h_i1]; omega
      have h_k_le : numbers.val.size - (i + 1).toNat ≤ k := by rw [h_i1]; omega
      by_cases hlt : (numbers.val[i.toNat]'hi_lt).toInt < m.toInt
      · -- Take the "lt" branch: recurse with new seed `numbers[i]`.
        have h_step := min_at_step_lt numbers i m hi_lt hlt
        obtain ⟨r, hres, h_r_le, h_r_lb, h_r_eq⟩ :=
          ih (i + 1) (numbers.val[i.toNat]'hi_lt) h_k_le h_i1_le
        refine ⟨r, ?_, ?_, ?_, ?_⟩
        · rw [h_step]; exact hres
        · -- r ≤ numbers[i] ≤ m (the new seed was smaller, and r ≤ new seed)
          have := h_r_le
          omega
        · intro j hj h_ile
          by_cases h_jeq : j = i.toNat
          · -- r ≤ numbers[i] from h_r_le
            subst h_jeq; exact h_r_le
          · have h_jgt : i.toNat + 1 ≤ j := by omega
            have h_jgt' : (i + 1).toNat ≤ j := by rw [h_i1]; exact h_jgt
            exact h_r_lb j hj h_jgt'
        · rcases h_r_eq with h_r_eq_m | ⟨j, hj, h_jle, h_r_eq_j⟩
          · -- r = numbers[i].toInt; witness j = i.toNat
            refine Or.inr ⟨i.toNat, hi_lt, Nat.le_refl _, h_r_eq_m⟩
          · -- r = numbers[j].toInt with (i+1).toNat ≤ j; j ≥ i.toNat too
            rw [h_i1] at h_jle
            refine Or.inr ⟨j, hj, by omega, h_r_eq_j⟩
      · -- Take the "ge" branch: keep `m`.
        have hge : m.toInt ≤ (numbers.val[i.toNat]'hi_lt).toInt := by omega
        have h_step := min_at_step_ge numbers i m hi_lt hge
        obtain ⟨r, hres, h_r_le, h_r_lb, h_r_eq⟩ :=
          ih (i + 1) m h_k_le h_i1_le
        refine ⟨r, ?_, h_r_le, ?_, ?_⟩
        · rw [h_step]; exact hres
        · intro j hj h_ile
          by_cases h_jeq : j = i.toNat
          · -- r ≤ m ≤ numbers[i]
            subst h_jeq; omega
          · have h_jgt : (i + 1).toNat ≤ j := by rw [h_i1]; omega
            exact h_r_lb j hj h_jgt
        · rcases h_r_eq with h_r_eq_m | ⟨j, hj, h_jle, h_r_eq_j⟩
          · exact Or.inl h_r_eq_m
          · rw [h_i1] at h_jle
            refine Or.inr ⟨j, hj, by omega, h_r_eq_j⟩

/-! ## Step lemmas for `shift_at`. -/

private theorem shift_at_oob (numbers : RustSlice i64) (delta : i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : numbers.val.size ≤ i.toNat) :
    clever_021_rescale_to_unit.shift_at numbers delta i acc = RustM.ok acc := by
  conv => lhs; unfold clever_021_rescale_to_unit.shift_at
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

private theorem shift_at_step (numbers : RustSlice i64) (delta : i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < numbers.val.size)
    (hno_sub : ¬ Int64.subOverflow (numbers.val[i.toNat]'hi) delta)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_021_rescale_to_unit.shift_at numbers delta i acc =
      clever_021_rescale_to_unit.shift_at numbers delta (i + 1)
        (push_one acc ((numbers.val[i.toNat]'hi) - delta) h_acc) := by
  conv => lhs; unfold clever_021_rescale_to_unit.shift_at
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
  have h_no_bv_sub :
      BitVec.ssubOverflow (numbers.val[i.toNat]'hi).toBitVec delta.toBitVec = false := by
    have hno' : ¬ (BitVec.ssubOverflow (numbers.val[i.toNat]'hi).toBitVec
                                       delta.toBitVec = true) := hno_sub
    cases hb : BitVec.ssubOverflow (numbers.val[i.toNat]'hi).toBitVec delta.toBitVec with
    | false => rfl
    | true => exact absurd hb hno'
  have h_sub_eq :
      ((numbers.val[i.toNat]'hi) -? delta : RustM i64) =
        RustM.ok ((numbers.val[i.toNat]'hi) - delta) := by
    show (rust_primitives.ops.arith.Sub.sub (numbers.val[i.toNat]'hi) delta : RustM i64) = _
    show (if BitVec.ssubOverflow (numbers.val[i.toNat]'hi).toBitVec delta.toBitVec
          then (.fail .integerOverflow : RustM i64)
          else pure ((numbers.val[i.toNat]'hi) - delta)) = _
    rw [h_no_bv_sub]; rfl
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
  have h_add_eq : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
    show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
    show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
          then (.fail .integerOverflow : RustM usize)
          else pure (i + 1)) = _
    rw [h_no_bv_i]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_sub_eq]
  -- Reduce unsize and extend_from_slice using the 1-chunk pattern.
  rw [show (rust_primitives.unsize
              (RustArray.ofVec #v[((numbers.val[i.toNat]'hi) - delta)] : RustArray i64 1)
              : RustM (rust_primitives.sequence.Seq i64))
            = RustM.ok ⟨#[((numbers.val[i.toNat]'hi) - delta)], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size :
      acc.val.size +
        (#[((numbers.val[i.toNat]'hi) - delta)] : Array i64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size
    exact h_acc
  rw [show (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
              ⟨#[((numbers.val[i.toNat]'hi) - delta)], one_lt_usize_size⟩
            : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
        = RustM.ok (push_one acc ((numbers.val[i.toNat]'hi) - delta) h_acc) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  simp only [RustM_ok_bind]
  rw [h_add_eq]
  rfl

/-! ## Strong induction for `shift_at`.

Match the `rolling_max_at_correct` invariant exactly: each call requires
`acc.val.size = i.toNat`, i.e. acc has been filled with exactly the prefix
of shifted elements so far. The final result then has `v.val.size = size`
and `v.val[j] = numbers.val[j] - delta` for all `j ∈ [0, size)`. -/

private theorem shift_at_correct (numbers : RustSlice i64) (delta : i64)
    (hno : ∀ (j : Nat) (hj : j < numbers.val.size),
              ¬ Int64.subOverflow (numbers.val[j]'hj) delta) :
    ∀ (k : Nat) (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global),
      numbers.val.size - i.toNat ≤ k →
      i.toNat ≤ numbers.val.size →
      acc.val.size = i.toNat →
      (∀ (j : Nat) (hj : j < acc.val.size) (hj_n : j < numbers.val.size),
          (acc.val[j]'hj).toInt = (numbers.val[j]'hj_n).toInt - delta.toInt) →
      ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
        clever_021_rescale_to_unit.shift_at numbers delta i acc = RustM.ok v ∧
        v.val.size = numbers.val.size ∧
        (∀ (j : Nat) (hj : j < v.val.size) (hj_n : j < numbers.val.size),
            (v.val[j]'hj).toInt = (numbers.val[j]'hj_n).toInt - delta.toInt) := by
  intro k
  induction k with
  | zero =>
    intro i acc hk hi_le h_acc_size h_acc_chunk
    have hi_eq : i.toNat = numbers.val.size := by omega
    have hi_ge : numbers.val.size ≤ i.toNat := by omega
    refine ⟨acc, shift_at_oob numbers delta i acc hi_ge, ?_, ?_⟩
    · rw [h_acc_size, hi_eq]
    · intros j hj hj_n; exact h_acc_chunk j hj hj_n
  | succ k ih =>
    intro i acc hk hi_le h_acc_size h_acc_chunk
    by_cases hi_ge : numbers.val.size ≤ i.toNat
    · have hi_eq : i.toNat = numbers.val.size := by omega
      refine ⟨acc, shift_at_oob numbers delta i acc hi_ge, ?_, ?_⟩
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
      have hno_sub_i : ¬ Int64.subOverflow (numbers.val[i.toNat]'hi_lt) delta :=
        hno i.toNat hi_lt
      have h_step := shift_at_step numbers delta i acc hi_lt hno_sub_i h_acc_succ
      rw [h_step]
      -- Apply IH with the extended acc.
      have h_acc'_size :
          (push_one acc ((numbers.val[i.toNat]'hi_lt) - delta) h_acc_succ).val.size
            = (i + 1).toNat := by
        show (acc.val ++ #[_]).size = (i + 1).toNat
        rw [Array.size_append, h_i1, h_acc_size]
        rfl
      have h_acc'_chunk :
          ∀ (j : Nat)
            (hj : j < (push_one acc ((numbers.val[i.toNat]'hi_lt) - delta) h_acc_succ).val.size)
            (hj_n : j < numbers.val.size),
            ((push_one acc ((numbers.val[i.toNat]'hi_lt) - delta) h_acc_succ).val[j]'hj).toInt
              = (numbers.val[j]'hj_n).toInt - delta.toInt := by
        intro j hj hj_n
        show ((acc.val ++ #[(numbers.val[i.toNat]'hi_lt) - delta])[j]'hj).toInt = _
        by_cases hjlt : j < acc.val.size
        · rw [Array.getElem_append_left hjlt]
          exact h_acc_chunk j hjlt hj_n
        · -- j = acc.val.size = i.toNat
          have h_size_raw :
              (acc.val ++ #[(numbers.val[i.toNat]'hi_lt) - delta]).size
                = acc.val.size + 1 := by rw [Array.size_append]; rfl
          have hj_eq : j = acc.val.size := by
            have : j < acc.val.size + 1 := by rw [← h_size_raw]; exact hj
            omega
          subst hj_eq
          rw [Array.getElem_append_right (Nat.le_refl _)]
          simp only [Nat.sub_self]
          show ((numbers.val[i.toNat]'hi_lt) - delta).toInt = _
          rw [Int64.toInt_sub_of_not_subOverflow hno_sub_i]
          -- Goal: numbers.val[i.toNat]'hi_lt.toInt - delta.toInt = numbers.val[acc.val.size]'hj_n.toInt - delta.toInt
          have h_num_eq :
              numbers.val[i.toNat]'hi_lt = numbers.val[acc.val.size]'hj_n :=
            getElem_congr_idx h_acc_size.symm
          rw [h_num_eq]
      have h_i1_le : (i + 1).toNat ≤ numbers.val.size := by rw [h_i1]; omega
      have h_k_le : numbers.val.size - (i + 1).toNat ≤ k := by rw [h_i1]; omega
      exact ih (i + 1) _ h_k_le h_i1_le h_acc'_size h_acc'_chunk

/-! ## Top-level theorems. -/

/-- Short-input boundary clause: when `numbers.val.size < 2`, the function
    returns successfully an empty `Vec`. Captures the proptest
    `short_input_returns_empty`. -/
theorem short_input_returns_empty
    (numbers : RustSlice i64)
    (hshort : numbers.val.size < 2) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_021_rescale_to_unit.rescale_to_unit numbers = RustM.ok v ∧
      v.val.size = 0 := by
  unfold clever_021_rescale_to_unit.rescale_to_unit
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' numbers.size_lt_usizeSize
  have h_two_toNat : (2 : usize).toNat = 2 := usize_two_toNat
  have h_cond : decide ((USize64.ofNat numbers.val.size) < (2 : usize)) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.lt_iff_toNat_lt, h_ofNat, h_two_toNat]
    exact hshort
  refine ⟨⟨(List.nil : List i64).toArray, by grind⟩, ?_, ?_⟩
  · simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
               rust_primitives.cmp.lt, pure_bind,
               h_cond, ↓reduceIte]
    rfl
  · rfl

/-! ## Auxiliary lemma combining `min_at` + `shift_at` for `len ≥ 2`. -/

private theorem rescale_to_unit_aux
    (numbers : RustSlice i64)
    (hlen : 2 ≤ numbers.val.size)
    (hfit : ∀ (i j : Nat) (hi : i < numbers.val.size) (hj : j < numbers.val.size),
              -(2^63 : Int) ≤ (numbers.val[i]'hi).toInt - (numbers.val[j]'hj).toInt
              ∧ (numbers.val[i]'hi).toInt - (numbers.val[j]'hj).toInt < 2^63) :
    ∃ (m : i64) (v : alloc.vec.Vec i64 alloc.alloc.Global),
      clever_021_rescale_to_unit.rescale_to_unit numbers = RustM.ok v ∧
      v.val.size = numbers.val.size ∧
      (∀ (j : Nat) (hj : j < numbers.val.size),
          m.toInt ≤ (numbers.val[j]'hj).toInt) ∧
      (∃ (j : Nat) (hj : j < numbers.val.size),
          m.toInt = (numbers.val[j]'hj).toInt) ∧
      (∀ (k : Nat) (hk_v : k < v.val.size) (hk_n : k < numbers.val.size),
          (v.val[k]'hk_v).toInt = (numbers.val[k]'hk_n).toInt - m.toInt) := by
  unfold clever_021_rescale_to_unit.rescale_to_unit
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' numbers.size_lt_usizeSize
  have h_two_toNat : (2 : usize).toNat = 2 := usize_two_toNat
  have h_cond : decide ((USize64.ofNat numbers.val.size) < (2 : usize)) = false := by
    rw [decide_eq_false_iff_not]
    intro hl
    rw [USize64.lt_iff_toNat_lt, h_ofNat, h_two_toNat] at hl
    omega
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.lt, pure_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte]
  have h_zero_lt : (0 : Nat) < numbers.val.size := by omega
  have h_zero_lt_usize : (0 : usize).toNat < numbers.val.size := h_zero_lt
  have h_idx_0 : (numbers[(0 : usize)]_? : RustM i64) = RustM.ok (numbers.val[0]'h_zero_lt) := by
    show (if h : (0 : usize).toNat < numbers.val.size then pure (numbers.val[(0 : usize)])
            else .fail .arrayOutOfBounds)
        = RustM.ok (numbers.val[0]'h_zero_lt)
    rw [dif_pos h_zero_lt_usize]
    rfl
  rw [h_idx_0]
  simp only [RustM_ok_bind]
  -- Apply min_at_correct at (1 : usize) starting with numbers[0]
  have h_one_le : (1 : usize).toNat ≤ numbers.val.size := by
    rw [usize_one_toNat]; omega
  have h_meas_min :
      numbers.val.size - (1 : usize).toNat ≤ numbers.val.size := by
    rw [usize_one_toNat]; omega
  obtain ⟨m, h_min_eq, h_m_le_n0, h_m_lb_suffix, h_m_eq⟩ :=
    min_at_correct numbers numbers.val.size (1 : usize) (numbers.val[0]'h_zero_lt)
      h_meas_min h_one_le
  rw [h_min_eq]
  simp only [RustM_ok_bind]
  -- Apply shift_at_correct at (0 : usize) with initial empty vec.
  let acc0 : alloc.vec.Vec i64 alloc.alloc.Global :=
    ⟨(List.nil : List i64).toArray, by grind⟩
  have h_acc0_new :
    (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
      RustM (alloc.vec.Vec i64 alloc.alloc.Global)) = RustM.ok acc0 := rfl
  rw [h_acc0_new]
  simp only [RustM_ok_bind]
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_acc0_size : acc0.val.size = 0 := rfl
  have h_acc0_size_iToNat : acc0.val.size = (0 : usize).toNat := rfl
  have h_size_lt : numbers.val.size < USize64.size := numbers.size_lt_usizeSize
  have h_zero_le : (0 : usize).toNat ≤ numbers.val.size := by rw [h_zero_toNat]; omega
  -- Show all subtractions numbers[j] - m don't overflow.
  -- We have m.toInt = numbers[j*].toInt for some j* by h_m_eq + the
  -- "m ≤ numbers[0]" branch. Either case lets us apply hfit on the pair (j, j*).
  have h_m_witness :
      ∃ (j_star : Nat) (hj_star : j_star < numbers.val.size),
        m.toInt = (numbers.val[j_star]'hj_star).toInt := by
    rcases h_m_eq with h_eq_n0 | ⟨j, hj, h_jge, h_eq⟩
    · exact ⟨0, h_zero_lt, h_eq_n0⟩
    · exact ⟨j, hj, h_eq⟩
  obtain ⟨j_star, hj_star, h_m_eq_j_star⟩ := h_m_witness
  have h_no_sub :
      ∀ (j : Nat) (hj : j < numbers.val.size),
          ¬ Int64.subOverflow (numbers.val[j]'hj) m := by
    intro j hj
    rw [Int64.subOverflow_iff]
    rw [h_m_eq_j_star]
    have h_fit_pair := hfit j j_star hj hj_star
    intro hov
    rcases hov with hov_pos | hov_neg
    · -- (numbers[j] - numbers[j*]) ≥ 2^63 — contradicts hfit
      have := h_fit_pair.2; omega
    · have := h_fit_pair.1; omega
  have h_acc0_chunk :
      ∀ (j : Nat) (hj : j < acc0.val.size) (hj_n : j < numbers.val.size),
        (acc0.val[j]'hj).toInt = (numbers.val[j]'hj_n).toInt - m.toInt := by
    intros j hj _; exfalso; rw [h_acc0_size] at hj; omega
  obtain ⟨v, hres, h_v_size, h_v_chunk⟩ :=
    shift_at_correct numbers m h_no_sub numbers.val.size (0 : usize) acc0
      (by rw [h_zero_toNat]; omega) h_zero_le h_acc0_size_iToNat h_acc0_chunk
  -- Build the witnesses.
  refine ⟨m, v, hres, h_v_size, ?_, ?_, ?_⟩
  · -- m.toInt ≤ numbers[j].toInt for all j
    intro j hj
    rcases Nat.lt_or_ge j 1 with h_jzero | h_jpos
    · -- j = 0: m.toInt ≤ numbers[0].toInt comes from h_m_le_n0
      have h_j_eq : j = 0 := by omega
      subst h_j_eq
      exact h_m_le_n0
    · -- j ≥ 1: use h_m_lb_suffix at j
      have h_j_ge_one : (1 : usize).toNat ≤ j := by rw [usize_one_toNat]; exact h_jpos
      exact h_m_lb_suffix j hj h_j_ge_one
  · -- ∃ j, m.toInt = numbers[j].toInt
    exact ⟨j_star, hj_star, h_m_eq_j_star⟩
  · -- elementwise: v[k] = numbers[k] - m
    intro k hk_v hk_n
    exact h_v_chunk k hk_v hk_n

/-- Length postcondition (len ≥ 2). -/
theorem preserves_length
    (numbers : RustSlice i64)
    (hlen : 2 ≤ numbers.val.size)
    (hfit : ∀ (i j : Nat) (hi : i < numbers.val.size) (hj : j < numbers.val.size),
              -(2^63 : Int) ≤ (numbers.val[i]'hi).toInt - (numbers.val[j]'hj).toInt
              ∧ (numbers.val[i]'hi).toInt - (numbers.val[j]'hj).toInt < 2^63) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_021_rescale_to_unit.rescale_to_unit numbers = RustM.ok v ∧
      v.val.size = numbers.val.size := by
  obtain ⟨m, v, hres, hlen', _, _, _⟩ := rescale_to_unit_aux numbers hlen hfit
  exact ⟨v, hres, hlen'⟩

/-- Min-zero postcondition (len ≥ 2). -/
theorem output_min_is_zero
    (numbers : RustSlice i64)
    (hlen : 2 ≤ numbers.val.size)
    (hfit : ∀ (i j : Nat) (hi : i < numbers.val.size) (hj : j < numbers.val.size),
              -(2^63 : Int) ≤ (numbers.val[i]'hi).toInt - (numbers.val[j]'hj).toInt
              ∧ (numbers.val[i]'hi).toInt - (numbers.val[j]'hj).toInt < 2^63) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_021_rescale_to_unit.rescale_to_unit numbers = RustM.ok v ∧
      (∀ (k : Nat) (hk : k < v.val.size), 0 ≤ (v.val[k]'hk).toInt) ∧
      (∃ (k : Nat) (hk : k < v.val.size), (v.val[k]'hk).toInt = 0) := by
  obtain ⟨m, v, hres, hlen', h_m_lb, ⟨j_star, hj_star, h_m_eq⟩, h_chunk⟩ :=
    rescale_to_unit_aux numbers hlen hfit
  refine ⟨v, hres, ?_, ?_⟩
  · intro k hk_v
    have hk_n : k < numbers.val.size := by rw [hlen'] at hk_v; exact hk_v
    rw [h_chunk k hk_v hk_n]
    have := h_m_lb k hk_n
    omega
  · -- Witness j_star where numbers[j_star] = m, then v[j_star] = numbers[j_star] - m = 0
    have hj_star_v : j_star < v.val.size := by rw [hlen']; exact hj_star
    refine ⟨j_star, hj_star_v, ?_⟩
    rw [h_chunk j_star hj_star_v hj_star]
    rw [← h_m_eq]
    omega

/-- Uniform-shift postcondition (len ≥ 2). -/
theorem is_uniform_shift
    (numbers : RustSlice i64)
    (hlen : 2 ≤ numbers.val.size)
    (hfit : ∀ (i j : Nat) (hi : i < numbers.val.size) (hj : j < numbers.val.size),
              -(2^63 : Int) ≤ (numbers.val[i]'hi).toInt - (numbers.val[j]'hj).toInt
              ∧ (numbers.val[i]'hi).toInt - (numbers.val[j]'hj).toInt < 2^63) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_021_rescale_to_unit.rescale_to_unit numbers = RustM.ok v ∧
      v.val.size = numbers.val.size ∧
      (∀ (i : Nat) (hi_v : i < v.val.size) (h0_v : 0 < v.val.size)
         (hi_n : i < numbers.val.size) (h0_n : 0 < numbers.val.size),
         (v.val[i]'hi_v).toInt - (v.val[0]'h0_v).toInt =
           (numbers.val[i]'hi_n).toInt - (numbers.val[0]'h0_n).toInt) := by
  obtain ⟨m, v, hres, hlen', _, _, h_chunk⟩ :=
    rescale_to_unit_aux numbers hlen hfit
  refine ⟨v, hres, hlen', ?_⟩
  intro i hi_v h0_v hi_n h0_n
  rw [h_chunk i hi_v hi_n, h_chunk 0 h0_v h0_n]
  omega

end Clever_021_rescale_to_unitObligations
