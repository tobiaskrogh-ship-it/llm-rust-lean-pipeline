-- Companion obligations file for the `clever_005_intersperse` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_005_intersperse

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_005_intersperseObligations

/-! ## Helper lemmas (shared infrastructure) -/

/-- `RustM.ok x >>= f = f x`. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

/-- `(1 : usize).toNat = 1`. -/
private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

/-- `(0 : usize).toNat = 0`. -/
private theorem usize_zero_toNat : (0 : usize).toNat = 0 := rfl

/-- `(i + 1).toNat = i.toNat + 1` when no overflow. -/
private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

/-- No-overflow of `i +? 1` in BitVec form, given the bound on `i.toNat`. -/
private theorem usize_add_one_no_bv (i : usize) (h : i.toNat + 1 < 2^64) :
    BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
  generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
  cases bo with
  | false => rfl
  | true =>
    exfalso
    have hi := (USize64.uaddOverflow_iff i 1).mp hbo
    rw [usize_one_toNat] at hi
    omega

/-! ## Step lemmas for `intersperse_at` -/

/-- Out-of-bounds step: when `i.toNat ≥ numbers.val.size`, the function
    returns `RustM.ok acc` immediately. -/
private theorem intersperse_at_oob
    (numbers : RustSlice i64) (delimiter : i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : numbers.val.size ≤ i.toNat) :
    clever_005_intersperse.intersperse_at numbers delimiter i acc
      = RustM.ok acc := by
  conv => lhs; unfold clever_005_intersperse.intersperse_at
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

/-- Helper: produce the new accumulator from `acc` and a single element. -/
private def acc_push_one (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h : acc.val.size + 1 < 2 ^ 64) : alloc.vec.Vec i64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have heq : USize64.size = 2 ^ 64 := by decide
    have h_append : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      simp
    rw [h_append, heq]; exact h⟩

/-- Helper: produce the new accumulator from `acc` and two elements. -/
private def acc_push_two (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x y : i64)
    (h : acc.val.size + 2 < 2 ^ 64) : alloc.vec.Vec i64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x, y], by
    have heq : USize64.size = 2 ^ 64 := by decide
    have h_append : (acc.val ++ #[x, y]).size = acc.val.size + 2 := by
      simp
    rw [h_append, heq]; exact h⟩

/-- Size of `acc_push_one`. -/
@[simp]
private theorem acc_push_one_size
    (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h : acc.val.size + 1 < 2 ^ 64) :
    (acc_push_one acc x h).val.size = acc.val.size + 1 := by
  show (acc.val ++ #[x]).size = acc.val.size + 1
  simp

/-- Size of `acc_push_two`. -/
@[simp]
private theorem acc_push_two_size
    (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x y : i64)
    (h : acc.val.size + 2 < 2 ^ 64) :
    (acc_push_two acc x y h).val.size = acc.val.size + 2 := by
  show (acc.val ++ #[x, y]).size = acc.val.size + 2
  simp

/-- The `.val` of `acc_push_one` is the append. -/
private theorem acc_push_one_val
    (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h : acc.val.size + 1 < 2 ^ 64) :
    (acc_push_one acc x h).val = acc.val ++ #[x] := rfl

/-- The `.val` of `acc_push_two` is the append. -/
private theorem acc_push_two_val
    (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x y : i64)
    (h : acc.val.size + 2 < 2 ^ 64) :
    (acc_push_two acc x y h).val = acc.val ++ #[x, y] := rfl

/-- Step at `i = 0`: when `0 < numbers.val.size` and the append doesn't
    overflow, `intersperse_at` at `i = 0` recurses with `i = 1` and the
    accumulator extended by `[numbers.val[0]]`. -/
private theorem intersperse_at_step_zero
    (numbers : RustSlice i64) (delimiter : i64)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hn_pos : 0 < numbers.val.size)
    (h_size : acc.val.size + 1 < 2 ^ 64) :
    clever_005_intersperse.intersperse_at numbers delimiter (0 : usize) acc
      = clever_005_intersperse.intersperse_at numbers delimiter (1 : usize)
          (acc_push_one acc (numbers.val[0]'hn_pos) h_size) := by
  conv => lhs; unfold clever_005_intersperse.intersperse_at
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_n_pos_toNat : (0 : usize).toNat < numbers.val.size := by
    rw [h_zero_toNat]; exact hn_pos
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' numbers.size_lt_usizeSize
  have h_cond_ge : decide (USize64.ofNat numbers.val.size ≤ (0 : usize)) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    rw [h_zero_toNat] at hle
    omega
  have h_idx :
      (numbers[(0 : usize)]_? : RustM i64)
        = RustM.ok (numbers.val[0]'hn_pos) := by
    show (if h : (0 : usize).toNat < numbers.val.size
            then pure (numbers.val[(0 : usize)])
            else .fail .arrayOutOfBounds)
        = RustM.ok (numbers.val[0]'hn_pos)
    rw [dif_pos h_n_pos_toNat]
    rfl
  have h_eq_zero :
      ((0 : usize) ==? (0 : usize) : RustM Bool) = RustM.ok true := by
    show (rust_primitives.cmp.eq (0 : usize) (0 : usize) : RustM Bool) = RustM.ok true
    show (pure ((0 : usize) == (0 : usize)) : RustM Bool) = RustM.ok true
    rfl
  have h_no_bv_one :
      BitVec.uaddOverflow (0 : usize).toBitVec (1 : usize).toBitVec = false := by
    have h_pre : (0 : usize).toNat + 1 < 2 ^ 64 := by rw [h_zero_toNat]; omega
    exact usize_add_one_no_bv (0 : usize) h_pre
  have h_add_one :
      ((0 : usize) +? (1 : usize) : RustM usize) = RustM.ok (1 : usize) := by
    show (rust_primitives.ops.arith.Add.add (0 : usize) (1 : usize) : RustM usize)
       = RustM.ok (1 : usize)
    show (if BitVec.uaddOverflow (0 : usize).toBitVec (1 : usize).toBitVec
          then (.fail .integerOverflow : RustM usize)
          else pure ((0 : usize) + (1 : usize))) = RustM.ok (1 : usize)
    rw [h_no_bv_one]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_ge, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_eq_zero, h_add_one]
  simp only [rust_primitives.unsize, alloc.vec.Impl_2.extend_from_slice,
             pure_bind]
  have h_size_USize : acc.val.size + 1 < USize64.size := by
    have heq : USize64.size = 2 ^ 64 := by decide
    rw [heq]; exact h_size
  have h_size_arr : acc.val.size + (#[numbers.val[0]'hn_pos] : Array i64).size
                    < USize64.size := by
    show acc.val.size + 1 < USize64.size
    exact h_size_USize
  rw [dif_pos h_size_arr]
  simp only [pure_bind]
  congr 1

/-- Step at `i > 0`, in bounds. -/
private theorem intersperse_at_step_pos
    (numbers : RustSlice i64) (delimiter : i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi_pos : 0 < i.toNat) (hi_lt : i.toNat < numbers.val.size)
    (h_no_overflow : i.toNat + 1 < 2 ^ 64)
    (h_size : acc.val.size + 2 < 2 ^ 64) :
    clever_005_intersperse.intersperse_at numbers delimiter i acc
      = clever_005_intersperse.intersperse_at numbers delimiter (i + 1)
          (acc_push_two acc delimiter (numbers.val[i.toNat]'hi_lt) h_size) := by
  conv => lhs; unfold clever_005_intersperse.intersperse_at
  have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' numbers.size_lt_usizeSize
  have h_cond_ge : decide (USize64.ofNat numbers.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx :
      (numbers[i]_? : RustM i64)
        = RustM.ok (numbers.val[i.toNat]'hi_lt) := by
    show (if h : i.toNat < numbers.val.size
            then pure (numbers.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (numbers.val[i.toNat]'hi_lt)
    rw [dif_pos hi_lt]
    rfl
  have h_neq_zero : ((i ==? (0 : usize)) : RustM Bool) = RustM.ok false := by
    show (rust_primitives.cmp.eq i (0 : usize) : RustM Bool) = RustM.ok false
    show (pure (i == (0 : usize)) : RustM Bool) = RustM.ok false
    have h_ne : i ≠ (0 : usize) := by
      intro heq
      have h0 : i.toNat = 0 := by rw [heq]; rfl
      omega
    have h_decide : (i == (0 : usize)) = false := by
      rw [beq_eq_false_iff_ne]; exact h_ne
    rw [h_decide]; rfl
  have h_no_bv_one :
      BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false :=
    usize_add_one_no_bv i h_no_overflow
  have h_add_one :
      (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
    show (rust_primitives.ops.arith.Add.add i (1 : usize) : RustM usize)
       = RustM.ok (i + 1)
    show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
          then (.fail .integerOverflow : RustM usize)
          else pure (i + 1)) = RustM.ok (i + 1)
    rw [h_no_bv_one]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_ge, Bool.false_eq_true, ↓reduceIte,
             h_idx, h_neq_zero, h_add_one]
  simp only [rust_primitives.unsize, alloc.vec.Impl_2.extend_from_slice,
             pure_bind]
  have h_size_USize : acc.val.size + 2 < USize64.size := by
    have heq : USize64.size = 2 ^ 64 := by decide
    rw [heq]; exact h_size
  have h_size_arr :
      acc.val.size + (#[delimiter, numbers.val[i.toNat]'hi_lt] : Array i64).size
        < USize64.size := by
    show acc.val.size + 2 < USize64.size
    exact h_size_USize
  rw [dif_pos h_size_arr]
  simp only [pure_bind]
  congr 1

/-! ## Array-indexing helpers for the pushed accumulator -/

/-- Indexing the push-one append at any `k < acc.val.size` returns the
    old element. -/
private theorem acc_push_one_getElem_lt
    (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h : acc.val.size + 1 < 2 ^ 64) (k : Nat) (hk : k < acc.val.size)
    (hk' : k < (acc_push_one acc x h).val.size) :
    (acc_push_one acc x h).val[k]'hk' = acc.val[k]'hk := by
  show (acc.val ++ #[x])[k]'_ = acc.val[k]'hk
  rw [Array.getElem_append_left hk]

/-- Indexing the push-one append at `k = acc.val.size` returns `x`. -/
private theorem acc_push_one_getElem_last
    (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h : acc.val.size + 1 < 2 ^ 64)
    (hk : acc.val.size < (acc_push_one acc x h).val.size) :
    (acc_push_one acc x h).val[acc.val.size]'hk = x := by
  show (acc.val ++ #[x])[acc.val.size]'_ = x
  have h_ge : acc.val.size ≥ acc.val.size := Nat.le_refl _
  rw [Array.getElem_append_right h_ge]
  simp

/-- Indexing the push-two append at any `k < acc.val.size` returns the
    old element. -/
private theorem acc_push_two_getElem_lt
    (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x y : i64)
    (h : acc.val.size + 2 < 2 ^ 64) (k : Nat) (hk : k < acc.val.size)
    (hk' : k < (acc_push_two acc x y h).val.size) :
    (acc_push_two acc x y h).val[k]'hk' = acc.val[k]'hk := by
  show (acc.val ++ #[x, y])[k]'_ = acc.val[k]'hk
  rw [Array.getElem_append_left hk]

/-- Indexing the push-two append at `acc.val.size` returns `x`. -/
private theorem acc_push_two_getElem_first
    (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x y : i64)
    (h : acc.val.size + 2 < 2 ^ 64)
    (hk : acc.val.size < (acc_push_two acc x y h).val.size) :
    (acc_push_two acc x y h).val[acc.val.size]'hk = x := by
  show (acc.val ++ #[x, y])[acc.val.size]'_ = x
  have h_ge : acc.val.size ≥ acc.val.size := Nat.le_refl _
  rw [Array.getElem_append_right h_ge]
  simp

/-- Indexing the push-two append at `acc.val.size + 1` returns `y`. -/
private theorem acc_push_two_getElem_second
    (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x y : i64)
    (h : acc.val.size + 2 < 2 ^ 64)
    (hk : acc.val.size + 1 < (acc_push_two acc x y h).val.size) :
    (acc_push_two acc x y h).val[acc.val.size + 1]'hk = y := by
  show (acc.val ++ #[x, y])[acc.val.size + 1]'_ = y
  have h_ge' : acc.val.size + 1 ≥ acc.val.size := by omega
  rw [Array.getElem_append_right h_ge']
  simp

/-- Generalised indexing: at any `j = acc.val.size`, return `x`. -/
private theorem acc_push_two_getElem_first_at
    (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x y : i64)
    (h : acc.val.size + 2 < 2 ^ 64) (j : Nat) (hj : j = acc.val.size)
    (hj' : j < (acc_push_two acc x y h).val.size) :
    (acc_push_two acc x y h).val[j]'hj' = x := by
  subst hj
  exact acc_push_two_getElem_first acc x y h hj'

/-- Generalised indexing: at any `j = acc.val.size + 1`, return `y`. -/
private theorem acc_push_two_getElem_second_at
    (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x y : i64)
    (h : acc.val.size + 2 < 2 ^ 64) (j : Nat) (hj : j = acc.val.size + 1)
    (hj' : j < (acc_push_two acc x y h).val.size) :
    (acc_push_two acc x y h).val[j]'hj' = y := by
  subst hj
  exact acc_push_two_getElem_second acc x y h hj'

/-- Generalised indexing: at any `j = acc.val.size`, return `x` (push-one). -/
private theorem acc_push_one_getElem_last_at
    (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h : acc.val.size + 1 < 2 ^ 64) (j : Nat) (hj : j = acc.val.size)
    (hj' : j < (acc_push_one acc x h).val.size) :
    (acc_push_one acc x h).val[j]'hj' = x := by
  subst hj
  exact acc_push_one_getElem_last acc x h hj'

/-! ## Master invariant — combined totality + length + content -/

/-- Strong-induction master lemma: under the size precondition
    `2 * numbers.val.size ≤ 2 ^ 64`, the recursion of `intersperse_at`
    terminates with a result whose length is `2 * numbers.val.size - 1`
    (for non-empty) or `0` (for empty), and whose even/odd indices match
    the contract.

    The invariant on `acc` at each step is:
    * its length is `if i.toNat = 0 then 0 else 2 * i.toNat - 1`,
    * its even slots `2*k` (for `k < i.toNat`) recover `numbers.val[k]`,
    * its odd slots `2*k+1` (for `k+1 < i.toNat`) are `delimiter`. -/
private theorem intersperse_at_full
    (numbers : RustSlice i64) (delimiter : i64)
    (h_bound : 2 * numbers.val.size ≤ 2 ^ 64) :
    ∀ (m : Nat) (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global),
      numbers.val.size - i.toNat ≤ m →
      i.toNat ≤ numbers.val.size →
      acc.val.size = (if i.toNat = 0 then 0 else 2 * i.toNat - 1) →
      (∀ k, k < i.toNat → ∀ (h2k : 2 * k < acc.val.size)
              (hk : k < numbers.val.size),
            acc.val[2 * k]'h2k = numbers.val[k]'hk) →
      (∀ k, k + 1 < i.toNat → ∀ (h2k1 : 2 * k + 1 < acc.val.size),
            acc.val[2 * k + 1]'h2k1 = delimiter) →
      ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
        clever_005_intersperse.intersperse_at numbers delimiter i acc = RustM.ok v ∧
        v.val.size = (if numbers.val.size = 0 then 0 else 2 * numbers.val.size - 1) ∧
        (∀ k, k < numbers.val.size → ∀ (h2k : 2 * k < v.val.size)
                (hk : k < numbers.val.size),
              v.val[2 * k]'h2k = numbers.val[k]'hk) ∧
        (∀ k, k + 1 < numbers.val.size → ∀ (h2k1 : 2 * k + 1 < v.val.size),
              v.val[2 * k + 1]'h2k1 = delimiter) := by
  intro m
  induction m with
  | zero =>
    intro i acc hm hin h_acc_size h_acc_even h_acc_odd
    have h_i_ge_n : i.toNat ≥ numbers.val.size := by omega
    have h_i_eq_n : i.toNat = numbers.val.size := by omega
    refine ⟨acc, intersperse_at_oob numbers delimiter i acc h_i_ge_n, ?_, ?_, ?_⟩
    · rw [h_acc_size, h_i_eq_n]
    · intro k hk h2k hk_n
      rw [h_i_eq_n] at h_acc_even
      exact h_acc_even k hk h2k hk_n
    · intro k hk h2k1
      rw [h_i_eq_n] at h_acc_odd
      exact h_acc_odd k hk h2k1
  | succ m ih =>
    intro i acc hm hin h_acc_size h_acc_even h_acc_odd
    by_cases h_i_ge : i.toNat ≥ numbers.val.size
    · have h_i_eq_n : i.toNat = numbers.val.size := by omega
      refine ⟨acc, intersperse_at_oob numbers delimiter i acc h_i_ge, ?_, ?_, ?_⟩
      · rw [h_acc_size, h_i_eq_n]
      · intro k hk h2k hk_n
        rw [h_i_eq_n] at h_acc_even
        exact h_acc_even k hk h2k hk_n
      · intro k hk h2k1
        rw [h_i_eq_n] at h_acc_odd
        exact h_acc_odd k hk h2k1
    · have hi_lt : i.toNat < numbers.val.size := Nat.lt_of_not_le h_i_ge
      have h_size_lt : numbers.val.size < 2 ^ 64 := numbers.size_lt_usizeSize
      have h_no_overflow_i : i.toNat + 1 < 2 ^ 64 := by omega
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 :=
        usize_add_one_toNat i h_no_overflow_i
      have h_one : (1 : usize).toNat = 1 := rfl
      have h_USize : USize64.size = 2 ^ 64 := by decide
      by_cases hi_zero : i.toNat = 0
      · -- i = 0 case
        have hi_eq : i = (0 : usize) := by
          apply USize64.toNat_inj.mp
          show i.toNat = (0 : usize).toNat
          rw [hi_zero]; rfl
        have h_acc_zero : acc.val.size = 0 := by
          rw [h_acc_size, if_pos hi_zero]
        have hn_pos : 0 < numbers.val.size := by omega
        have h_no : acc.val.size + 1 < 2 ^ 64 := by rw [h_acc_zero]; omega
        rw [hi_eq, intersperse_at_step_zero numbers delimiter acc hn_pos h_no]
        have h_acc'_size :
            (acc_push_one acc (numbers.val[0]'hn_pos) h_no).val.size = 1 := by
          rw [acc_push_one_size, h_acc_zero]
        have h_acc'_size_inv :
            (acc_push_one acc (numbers.val[0]'hn_pos) h_no).val.size
              = (if (1 : usize).toNat = 0 then 0 else 2 * (1 : usize).toNat - 1) := by
          rw [h_acc'_size]
          simp [h_one]
        have h_acc'_even :
            ∀ k, k < (1 : usize).toNat →
              ∀ (h2k : 2 * k < (acc_push_one acc (numbers.val[0]'hn_pos) h_no).val.size)
                (hk : k < numbers.val.size),
              (acc_push_one acc (numbers.val[0]'hn_pos) h_no).val[2 * k]'h2k
                = numbers.val[k]'hk := by
          intro k hk h2k hk_n
          rw [h_one] at hk
          have hk0 : k = 0 := by omega
          subst hk0
          have h_idx_eq : (2 * 0 : Nat) = acc.val.size := by rw [h_acc_zero]
          exact acc_push_one_getElem_last_at acc (numbers.val[0]'hn_pos) h_no (2 * 0)
            h_idx_eq h2k
        have h_acc'_odd :
            ∀ k, k + 1 < (1 : usize).toNat →
              ∀ (h2k1 : 2 * k + 1 < (acc_push_one acc (numbers.val[0]'hn_pos) h_no).val.size),
              (acc_push_one acc (numbers.val[0]'hn_pos) h_no).val[2 * k + 1]'h2k1
                = delimiter := by
          intro k hk
          rw [h_one] at hk
          omega
        have h_measure : numbers.val.size - (1 : usize).toNat ≤ m := by
          rw [h_one]; omega
        have h_in : (1 : usize).toNat ≤ numbers.val.size := by
          rw [h_one]; omega
        exact ih (1 : usize) (acc_push_one acc (numbers.val[0]'hn_pos) h_no)
          h_measure h_in h_acc'_size_inv h_acc'_even h_acc'_odd
      · -- i > 0 case
        have hi_pos : 0 < i.toNat := Nat.pos_of_ne_zero hi_zero
        have h_acc_size_val : acc.val.size = 2 * i.toNat - 1 := by
          rw [h_acc_size, if_neg hi_zero]
        -- Need acc.val.size + 2 < 2^64.
        -- acc.val.size + 2 = 2 * i.toNat - 1 + 2 = 2 * i.toNat + 1.
        -- Since i.toNat < numbers.val.size and 2 * numbers.val.size ≤ 2^64,
        -- 2 * i.toNat + 1 ≤ 2 * numbers.val.size - 1 < 2^64.
        have h_no : acc.val.size + 2 < 2 ^ 64 := by
          rw [h_acc_size_val]
          omega
        rw [intersperse_at_step_pos numbers delimiter i acc hi_pos hi_lt h_no_overflow_i h_no]
        have h_acc'_size_eq :
            (acc_push_two acc delimiter (numbers.val[i.toNat]'hi_lt) h_no).val.size
              = acc.val.size + 2 :=
          acc_push_two_size acc delimiter (numbers.val[i.toNat]'hi_lt) h_no
        have h_acc'_size_val :
            (acc_push_two acc delimiter (numbers.val[i.toNat]'hi_lt) h_no).val.size
              = 2 * (i + 1).toNat - 1 := by
          rw [h_acc'_size_eq, h_acc_size_val, h_i1_toNat]
          omega
        have h_acc'_size_inv :
            (acc_push_two acc delimiter (numbers.val[i.toNat]'hi_lt) h_no).val.size
              = (if (i + 1).toNat = 0 then 0 else 2 * (i + 1).toNat - 1) := by
          rw [h_acc'_size_val]
          have h_i1_ne_zero : (i + 1).toNat ≠ 0 := by rw [h_i1_toNat]; omega
          rw [if_neg h_i1_ne_zero]
        have h_acc'_even :
            ∀ k, k < (i + 1).toNat →
              ∀ (h2k : 2 * k <
                    (acc_push_two acc delimiter (numbers.val[i.toNat]'hi_lt) h_no).val.size)
                (hk : k < numbers.val.size),
              (acc_push_two acc delimiter (numbers.val[i.toNat]'hi_lt) h_no).val[2 * k]'h2k
                = numbers.val[k]'hk := by
          intro k hk h2k hk_n
          rw [h_i1_toNat] at hk
          by_cases hki : k < i.toNat
          · have h2k_lt : 2 * k < acc.val.size := by
              rw [h_acc_size_val]; omega
            show (acc.val ++ #[delimiter, numbers.val[i.toNat]'hi_lt])[2 * k]'_
                  = numbers.val[k]'hk_n
            rw [Array.getElem_append_left h2k_lt]
            exact h_acc_even k hki h2k_lt hk_n
          · have hki_eq : k = i.toNat := by omega
            subst hki_eq
            have h_idx_eq : (2 * i.toNat : Nat) = acc.val.size + 1 := by
              rw [h_acc_size_val]; omega
            exact acc_push_two_getElem_second_at acc delimiter
              (numbers.val[i.toNat]'hi_lt) h_no (2 * i.toNat) h_idx_eq h2k
        have h_acc'_odd :
            ∀ k, k + 1 < (i + 1).toNat →
              ∀ (h2k1 : 2 * k + 1 <
                    (acc_push_two acc delimiter (numbers.val[i.toNat]'hi_lt) h_no).val.size),
              (acc_push_two acc delimiter (numbers.val[i.toNat]'hi_lt) h_no).val[2 * k + 1]'h2k1
                = delimiter := by
          intro k hk h2k1
          rw [h_i1_toNat] at hk
          by_cases hki_strict : k + 1 < i.toNat
          · have h2k1_lt : 2 * k + 1 < acc.val.size := by
              rw [h_acc_size_val]; omega
            show (acc.val ++ #[delimiter, numbers.val[i.toNat]'hi_lt])[2 * k + 1]'_
                  = delimiter
            rw [Array.getElem_append_left h2k1_lt]
            exact h_acc_odd k hki_strict h2k1_lt
          · have hki_eq : k + 1 = i.toNat := by omega
            have h_idx_eq : (2 * k + 1 : Nat) = acc.val.size := by
              rw [h_acc_size_val]; omega
            exact acc_push_two_getElem_first_at acc delimiter
              (numbers.val[i.toNat]'hi_lt) h_no (2 * k + 1) h_idx_eq h2k1
        have h_measure : numbers.val.size - (i + 1).toNat ≤ m := by
          rw [h_i1_toNat]; omega
        have h_in : (i + 1).toNat ≤ numbers.val.size := by
          rw [h_i1_toNat]; omega
        exact ih (i + 1) (acc_push_two acc delimiter (numbers.val[i.toNat]'hi_lt) h_no)
          h_measure h_in h_acc'_size_inv h_acc'_even h_acc'_odd

/-- Closure of `intersperse`: under the size bound, the function returns
    `RustM.ok v` with the contract properties on `v`. -/
private theorem intersperse_correct
    (numbers : RustSlice i64) (delimiter : i64)
    (h_bound : 2 * numbers.val.size ≤ 2 ^ 64) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_005_intersperse.intersperse numbers delimiter = RustM.ok v ∧
      v.val.size = (if numbers.val.size = 0 then 0 else 2 * numbers.val.size - 1) ∧
      (∀ k, k < numbers.val.size → ∀ (h2k : 2 * k < v.val.size)
              (hk : k < numbers.val.size),
            v.val[2 * k]'h2k = numbers.val[k]'hk) ∧
      (∀ k, k + 1 < numbers.val.size → ∀ (h2k1 : 2 * k + 1 < v.val.size),
            v.val[2 * k + 1]'h2k1 = delimiter) := by
  unfold clever_005_intersperse.intersperse
  simp only [alloc.vec.Impl.new, pure_bind]
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  let init_acc : alloc.vec.Vec i64 alloc.alloc.Global :=
    ⟨(List.nil : List i64).toArray, by decide⟩
  obtain ⟨v, hv_eq, hv_size, hv_even, hv_odd⟩ :=
    intersperse_at_full numbers delimiter h_bound
      numbers.val.size (0 : usize) init_acc
      (by rw [h_zero_toNat]; omega)
      (by rw [h_zero_toNat]; omega)
      (by show (List.nil : List i64).toArray.size
                = (if (0 : usize).toNat = 0 then 0 else _)
          rw [h_zero_toNat]; rfl)
      (by intro k hk; rw [h_zero_toNat] at hk; omega)
      (by intro k hk; rw [h_zero_toNat] at hk; omega)
  exact ⟨v, hv_eq, hv_size, hv_even, hv_odd⟩

/-! ## Obligations -/

-- Postcondition clause 1 (length):
--   • empty input → empty output;
--   • non-empty input of size n → output of size `2 * n - 1`.
theorem intersperse_length (s : RustSlice i64) (delim : i64) :
    ⦃ ⌜ 2 * s.val.size ≤ USize64.size ⌝ ⦄
    clever_005_intersperse.intersperse s delim
    ⦃ ⇓ r => ⌜ r.val.size = if s.val.size = 0 then 0 else 2 * s.val.size - 1 ⌝ ⦄ := by
  intro hP
  have h_USize : USize64.size = 2 ^ 64 := by decide
  have h_bound : 2 * s.val.size ≤ 2 ^ 64 := by rw [← h_USize]; exact hP
  obtain ⟨v, hv_eq, hv_size, _, _⟩ := intersperse_correct s delim h_bound
  rw [hv_eq]
  exact hv_size

-- Postcondition clause 2 (even indices preserve the input in order):
--   for every `i < s.val.size`, `result[2 * i] = s[i]`.
theorem intersperse_even_indices_original (s : RustSlice i64) (delim : i64) :
    ⦃ ⌜ 2 * s.val.size ≤ USize64.size ⌝ ⦄
    clever_005_intersperse.intersperse s delim
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < s.val.size → r.val[2 * i]? = s.val[i]? ⌝ ⦄ := by
  intro hP
  have h_USize : USize64.size = 2 ^ 64 := by decide
  have h_bound : 2 * s.val.size ≤ 2 ^ 64 := by rw [← h_USize]; exact hP
  obtain ⟨v, hv_eq, hv_size, hv_even, _⟩ := intersperse_correct s delim h_bound
  rw [hv_eq]
  intro i hi
  -- s.val[i]? = some s.val[i]
  have h_s_get : s.val[i]? = some (s.val[i]'hi) := by
    rw [Array.getElem?_eq_getElem hi]
  -- 2 * i < v.val.size since v.val.size = 2 * s.val.size - 1 and i < s.val.size
  have hs_pos : 0 < s.val.size := Nat.zero_lt_of_lt hi
  have hs_ne : s.val.size ≠ 0 := Nat.ne_of_gt hs_pos
  have hv_size' : v.val.size = 2 * s.val.size - 1 := by
    rw [hv_size, if_neg hs_ne]
  have h2i_lt : 2 * i < v.val.size := by
    rw [hv_size']; omega
  have h_v_get : v.val[2 * i]? = some (v.val[2 * i]'h2i_lt) := by
    rw [Array.getElem?_eq_getElem h2i_lt]
  rw [h_v_get, h_s_get]
  congr 1
  exact hv_even i hi h2i_lt hi

-- Postcondition clause 3 (odd indices are the delimiter):
--   for every `i + 1 < s.val.size`, `result[2 * i + 1] = delimiter`.
theorem intersperse_odd_indices_delim (s : RustSlice i64) (delim : i64) :
    ⦃ ⌜ 2 * s.val.size ≤ USize64.size ⌝ ⦄
    clever_005_intersperse.intersperse s delim
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i + 1 < s.val.size → r.val[2 * i + 1]? = some delim ⌝ ⦄ := by
  intro hP
  have h_USize : USize64.size = 2 ^ 64 := by decide
  have h_bound : 2 * s.val.size ≤ 2 ^ 64 := by rw [← h_USize]; exact hP
  obtain ⟨v, hv_eq, hv_size, _, hv_odd⟩ := intersperse_correct s delim h_bound
  rw [hv_eq]
  intro i hi
  have hs_pos : 0 < s.val.size := by omega
  have hs_ne : s.val.size ≠ 0 := Nat.ne_of_gt hs_pos
  have hv_size' : v.val.size = 2 * s.val.size - 1 := by
    rw [hv_size, if_neg hs_ne]
  have h2i1_lt : 2 * i + 1 < v.val.size := by
    rw [hv_size']; omega
  have h_v_get : v.val[2 * i + 1]? = some (v.val[2 * i + 1]'h2i1_lt) := by
    rw [Array.getElem?_eq_getElem h2i1_lt]
  rw [h_v_get]
  congr 1
  exact hv_odd i hi h2i1_lt

end Clever_005_intersperseObligations
