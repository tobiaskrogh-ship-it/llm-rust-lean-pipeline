-- Companion obligations file for the `clever_032_sort_third` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_032_sort_third

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_032_sort_thirdObligations

/-! ## Specification oracle: values at indices divisible by 3, as a list.

`third_values_aux a k` is the list of values `a[j]` for indices `j < k` with
`j % 3 = 0`, taken in increasing order of `j`. The `dite` on `k < a.size`
keeps the definition total — every theorem below applies it with
`k ≤ a.size`, so the bounded indices always exist. -/

private def third_values_aux (a : Array i64) : Nat → List i64
  | 0     => []
  | k + 1 =>
      if h : k < a.size then
        if k % 3 = 0 then
          third_values_aux a k ++ [a[k]'h]
        else
          third_values_aux a k
      else
        third_values_aux a k

/-- The list of values at indices divisible by 3 in `a`, in input order. -/
private def third_values (a : Array i64) : List i64 :=
  third_values_aux a a.size

/-! ## Standard scaffolding (transferred from `clever_009_rolling_max`,
     `clever_021_rescale_to_unit`, `clever_025_remove_duplicates`). -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem RustM_fail_bind {α β : Type} (e : Error) (f : α → RustM β) :
    (RustM.fail e : RustM α) >>= f = RustM.fail e := rfl

private theorem RustM_div_bind {α β : Type} (f : α → RustM β) :
    (RustM.div : RustM α) >>= f = RustM.div := rfl

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide

private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide

private theorem two_lt_usize_size : (2 : Nat) < USize64.size := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

/-- Push a single element onto a `Vec`. -/
private def push_one (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec i64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

/-! ## `i %? 3 = 0` reduction.

For unsigned `usize`, `i %? 3` is `pure (i % 3)` because `(3 : usize) ≠ 0`.
The Boolean `(i % 3 ==? 0)` is `pure ((i % 3) == 0 : Bool)`. We bridge this
to `decide (i.toNat % 3 = 0)`. -/

private theorem usize_mod_3_succeeds (i : usize) :
    (i %? (3 : usize) : RustM usize) = RustM.ok (i % 3) := by
  show (rust_primitives.ops.arith.Rem.rem i 3 : RustM usize) = _
  show (if (3 : usize) = 0 then (.fail .divisionByZero : RustM usize)
        else pure (i % 3)) = _
  have h3 : (3 : usize) ≠ 0 := by decide
  rw [if_neg h3]
  rfl

/-- `(i % 3 : usize).toNat = i.toNat % 3`. -/
private theorem usize_mod_3_toNat (i : usize) :
    (i % (3 : usize)).toNat = i.toNat % 3 := by
  show ((⟨i.toBitVec % (3 : usize).toBitVec⟩ : usize)).toNat = _
  show (i.toBitVec % (3 : usize).toBitVec).toNat = _
  rw [BitVec.toNat_umod]
  show i.toNat % (3 : usize).toBitVec.toNat = _
  rfl

/-- `(i % 3 == (0 : usize)) = decide (i.toNat % 3 = 0)`. -/
private theorem usize_mod_3_beq_zero (i : usize) :
    ((i % (3 : usize)) == (0 : usize)) = decide (i.toNat % 3 = 0) := by
  rw [show ((i % (3 : usize)) == (0 : usize)) = decide ((i % (3 : usize)) = 0) from rfl]
  by_cases h : i.toNat % 3 = 0
  · have h_eq : (i % (3 : usize)) = 0 := by
      apply USize64.toNat_inj.mp
      rw [usize_mod_3_toNat]; rw [h]; rfl
    rw [decide_eq_true h_eq, decide_eq_true h]
  · have h_ne : (i % (3 : usize)) ≠ 0 := by
      intro hn
      apply h
      have := USize64.toNat_inj.mpr hn
      rw [usize_mod_3_toNat] at this
      simpa using this
    rw [decide_eq_false h_ne, decide_eq_false h]

/-! ## Step lemmas for `rebuild_at`.

Three branches: out-of-bounds, third-step (i % 3 = 0, push sorted[j]),
non-third step (i % 3 ≠ 0, push l[i]). -/

/-- Out-of-bounds step. -/
private theorem rebuild_at_oob
    (l sorted : RustSlice i64) (i j : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : l.val.size ≤ i.toNat) :
    clever_032_sort_third.rebuild_at l sorted i j acc = RustM.ok acc := by
  conv => lhs; unfold clever_032_sort_third.rebuild_at
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

/-- Third-step (i % 3 = 0): pushes `sorted[j]` and increments both i and j.
    Requires `j.toNat < sorted.val.size` for the inner `sorted[j]_?` to
    succeed, and `acc.val.size + 1 < USize64.size` for `extend_from_slice`. -/
private theorem rebuild_at_step_third
    (l sorted : RustSlice i64) (i j : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < l.val.size)
    (hi_mod : i.toNat % 3 = 0)
    (hj : j.toNat < sorted.val.size)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_032_sort_third.rebuild_at l sorted i j acc =
      clever_032_sort_third.rebuild_at l sorted (i + 1) (j + 1)
        (push_one acc (sorted.val[j.toNat]'hj) h_acc) := by
  conv => lhs; unfold clever_032_sort_third.rebuild_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_mod_eq := usize_mod_3_succeeds i
  have h_beq_3 : ((i % (3 : usize)) == (0 : usize)) = true := by
    rw [usize_mod_3_beq_zero]; exact decide_eq_true hi_mod
  have h_idx_sorted : (sorted[j]_? : RustM i64) = RustM.ok (sorted.val[j.toNat]'hj) := by
    show (if h : j.toNat < sorted.val.size then pure (sorted.val[j])
            else .fail .arrayOutOfBounds)
        = RustM.ok (sorted.val[j.toNat]'hj)
    rw [dif_pos hj]
    rfl
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
  -- For j+1 we don't pre-show no overflow; we just produce the same shape
  -- as the function, because the j+1 use is *after* the recursive call —
  -- actually it's an argument. So we DO need j+1 to not overflow.
  -- However, since j.toNat < sorted.val.size < 2^64, j.toNat + 1 ≤ 2^64.
  -- We only need it strictly less.
  have h_sorted_size_lt : sorted.val.size < USize64.size := sorted.size_lt_usizeSize
  have h_no_ov_j : j.toNat + 1 < 2^64 := by
    rw [h_usize_size] at h_sorted_size_lt; omega
  have h_no_bv_j :
      BitVec.uaddOverflow j.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow j.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hjj := (USize64.uaddOverflow_iff j 1).mp hbo
      rw [usize_one_toNat] at hjj
      omega
  have h_add_j : (j +? (1 : usize) : RustM usize) = RustM.ok (j + 1) := by
    show (rust_primitives.ops.arith.Add.add j 1 : RustM usize) = RustM.ok (j + 1)
    show (if BitVec.uaddOverflow j.toBitVec (1 : usize).toBitVec
          then (.fail .integerOverflow : RustM usize)
          else pure (j + 1)) = _
    rw [h_no_bv_j]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_mod_eq,
             rust_primitives.cmp.eq, h_beq_3,
             h_idx_sorted]
  rw [show (rust_primitives.unsize
            (RustArray.ofVec #v[sorted.val[j.toNat]'hj] : RustArray i64 1)
            : RustM (rust_primitives.sequence.Seq i64))
          = RustM.ok ⟨#[sorted.val[j.toNat]'hj], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  have h_app_size :
      acc.val.size + (#[sorted.val[j.toNat]'hj] : Array i64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size
    exact h_acc
  rw [show (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global acc
              ⟨#[sorted.val[j.toNat]'hj], one_lt_usize_size⟩
            : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
        = RustM.ok (push_one acc (sorted.val[j.toNat]'hj) h_acc) from by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]
    rfl]
  simp only [RustM_ok_bind]
  rw [h_add_i, h_add_j]
  rfl

/-- Non-third step (i % 3 ≠ 0): pushes `l[i]`, increments only i. -/
private theorem rebuild_at_step_nonthird
    (l sorted : RustSlice i64) (i j : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < l.val.size)
    (hi_mod : i.toNat % 3 ≠ 0)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_032_sort_third.rebuild_at l sorted i j acc =
      clever_032_sort_third.rebuild_at l sorted (i + 1) j
        (push_one acc (l.val[i.toNat]'hi) h_acc) := by
  conv => lhs; unfold clever_032_sort_third.rebuild_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_mod_eq := usize_mod_3_succeeds i
  have h_beq_3 : ((i % (3 : usize)) == (0 : usize)) = false := by
    rw [usize_mod_3_beq_zero]; exact decide_eq_false hi_mod
  have h_idx_l : (l[i]_? : RustM i64) = RustM.ok (l.val[i.toNat]'hi) := by
    show (if h : i.toNat < l.val.size then pure (l.val[i])
            else .fail .arrayOutOfBounds)
        = RustM.ok (l.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
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
             h_mod_eq,
             rust_primitives.cmp.eq, h_beq_3,
             h_idx_l]
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

/-- Failure-propagation lemma for the third branch: if `sorted[j]_?` fails
    because `j.toNat ≥ sorted.val.size`, then `rebuild_at` at this position
    also fails. Used to invert `rebuild_at = ok` and extract `j` in range. -/
private theorem rebuild_at_third_idx_fail
    (l sorted : RustSlice i64) (i j : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < l.val.size)
    (hi_mod : i.toNat % 3 = 0)
    (hj : sorted.val.size ≤ j.toNat) :
    clever_032_sort_third.rebuild_at l sorted i j acc =
      RustM.fail .arrayOutOfBounds := by
  conv => lhs; unfold clever_032_sort_third.rebuild_at
  have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat l.val.size).toNat = l.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat l.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_mod_eq := usize_mod_3_succeeds i
  have h_beq_3 : ((i % (3 : usize)) == (0 : usize)) = true := by
    rw [usize_mod_3_beq_zero]; exact decide_eq_true hi_mod
  have h_idx_sorted : (sorted[j]_? : RustM i64) =
      RustM.fail Error.arrayOutOfBounds := by
    show (if h : j.toNat < sorted.val.size then pure (sorted.val[j])
            else (RustM.fail Error.arrayOutOfBounds : RustM i64))
        = RustM.fail Error.arrayOutOfBounds
    rw [dif_neg (by omega)]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_mod_eq,
             rust_primitives.cmp.eq, h_beq_3,
             h_idx_sorted]
  rfl

/-! ## Strong induction for `rebuild_at`.

Captures the invariant: the output has size `l.val.size` and at non-third
indices equals the input. The induction takes `hres = RustM.ok v` as a
hypothesis; in the third branch, we extract `j.toNat < sorted.val.size`
by inverting on `hres` (otherwise `rebuild_at` would fail). -/

private theorem rebuild_at_correct (l sorted : RustSlice i64) :
    ∀ (n : Nat) (i j : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
      (v : alloc.vec.Vec i64 alloc.alloc.Global),
      l.val.size - i.toNat ≤ n →
      i.toNat ≤ l.val.size →
      acc.val.size = i.toNat →
      (∀ (k : Nat) (hk : k < acc.val.size) (hk_l : k < l.val.size),
          k % 3 ≠ 0 → acc.val[k]'hk = l.val[k]'hk_l) →
      clever_032_sort_third.rebuild_at l sorted i j acc = RustM.ok v →
      v.val.size = l.val.size ∧
      (∀ (k : Nat) (hk_v : k < v.val.size) (hk_l : k < l.val.size),
          k % 3 ≠ 0 → v.val[k]'hk_v = l.val[k]'hk_l) := by
  intro n
  induction n with
  | zero =>
    intro i j acc v hm hi_le h_acc_size h_acc_inv hres
    have hi_eq : i.toNat = l.val.size := by omega
    have hi_ge : l.val.size ≤ i.toNat := by omega
    rw [rebuild_at_oob l sorted i j acc hi_ge] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    refine ⟨?_, ?_⟩
    · rw [h_acc_size]; exact hi_eq
    · intro k hk_v hk_l hmod
      exact h_acc_inv k hk_v hk_l hmod
  | succ n ih =>
    intro i j acc v hm hi_le h_acc_size h_acc_inv hres
    by_cases hi_ge : l.val.size ≤ i.toNat
    · have hi_eq : i.toNat = l.val.size := by omega
      rw [rebuild_at_oob l sorted i j acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'
      refine ⟨?_, ?_⟩
      · rw [h_acc_size]; exact hi_eq
      · intro k hk_v hk_l hmod
        exact h_acc_inv k hk_v hk_l hmod
    · have hi_lt : i.toNat < l.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : l.val.size < USize64.size := l.size_lt_usizeSize
      have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [h_usize_size] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_acc_succ : acc.val.size + 1 < USize64.size := by
        rw [h_acc_size, h_usize_size]; omega
      have h_i1_le : (i + 1).toNat ≤ l.val.size := by rw [h_i1]; omega
      have h_meas : l.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      by_cases hmod_i : i.toNat % 3 = 0
      · -- Third branch. Need j.toNat < sorted.val.size; extract from hres.
        by_cases hj_lt : j.toNat < sorted.val.size
        · rw [rebuild_at_step_third l sorted i j acc hi_lt hmod_i hj_lt h_acc_succ] at hres
          have h_acc'_size :
              (push_one acc (sorted.val[j.toNat]'hj_lt) h_acc_succ).val.size = (i + 1).toNat := by
            show (acc.val ++ #[_]).size = (i + 1).toNat
            rw [Array.size_append, h_i1, h_acc_size]
            rfl
          have h_acc'_inv :
              ∀ (k : Nat)
                (hk : k < (push_one acc (sorted.val[j.toNat]'hj_lt) h_acc_succ).val.size)
                (hk_l : k < l.val.size),
                k % 3 ≠ 0 →
                (push_one acc (sorted.val[j.toNat]'hj_lt) h_acc_succ).val[k]'hk = l.val[k]'hk_l := by
            intro k hk hk_l hkmod
            show ((acc.val ++ #[sorted.val[j.toNat]'hj_lt])[k]'hk) = _
            by_cases hk_lt : k < acc.val.size
            · rw [Array.getElem_append_left hk_lt]
              exact h_acc_inv k hk_lt hk_l hkmod
            · -- k = acc.val.size = i.toNat, but i.toNat % 3 = 0 and hkmod
              exfalso
              have h_size_raw :
                  (acc.val ++ #[sorted.val[j.toNat]'hj_lt]).size = acc.val.size + 1 := by
                rw [Array.size_append]; rfl
              have hk_eq : k = acc.val.size := by
                have : k < acc.val.size + 1 := by rw [← h_size_raw]; exact hk
                omega
              rw [hk_eq, h_acc_size] at hkmod
              exact hkmod hmod_i
          exact ih (i + 1) (j + 1) _ v h_meas h_i1_le h_acc'_size h_acc'_inv hres
        · -- j out of range: rebuild_at fails — contradicts hres = ok.
          exfalso
          have hj_ge : sorted.val.size ≤ j.toNat := Nat.le_of_not_lt hj_lt
          rw [rebuild_at_third_idx_fail l sorted i j acc hi_lt hmod_i hj_ge] at hres
          cases hres
      · -- Non-third branch.
        rw [rebuild_at_step_nonthird l sorted i j acc hi_lt hmod_i h_acc_succ] at hres
        have h_acc'_size :
            (push_one acc (l.val[i.toNat]'hi_lt) h_acc_succ).val.size = (i + 1).toNat := by
          show (acc.val ++ #[_]).size = (i + 1).toNat
          rw [Array.size_append, h_i1, h_acc_size]
          rfl
        have h_acc'_inv :
            ∀ (k : Nat)
              (hk : k < (push_one acc (l.val[i.toNat]'hi_lt) h_acc_succ).val.size)
              (hk_l : k < l.val.size),
              k % 3 ≠ 0 →
              (push_one acc (l.val[i.toNat]'hi_lt) h_acc_succ).val[k]'hk = l.val[k]'hk_l := by
          intro k hk hk_l hkmod
          show ((acc.val ++ #[l.val[i.toNat]'hi_lt])[k]'hk) = _
          by_cases hk_lt : k < acc.val.size
          · rw [Array.getElem_append_left hk_lt]
            exact h_acc_inv k hk_lt hk_l hkmod
          · -- k = acc.val.size = i.toNat
            have h_size_raw :
                (acc.val ++ #[l.val[i.toNat]'hi_lt]).size = acc.val.size + 1 := by
              rw [Array.size_append]; rfl
            have hk_eq : k = acc.val.size := by
              have : k < acc.val.size + 1 := by rw [← h_size_raw]; exact hk
              omega
            subst hk_eq
            rw [Array.getElem_append_right (Nat.le_refl _)]
            simp only [Nat.sub_self]
            show l.val[i.toNat]'hi_lt = l.val[acc.val.size]'hk_l
            exact getElem_congr_idx h_acc_size.symm
        exact ih (i + 1) j _ v h_meas h_i1_le h_acc'_size h_acc'_inv hres

/-! ## Aux lemma extracting `(sorted, v)` from `sort_third l = ok v`.

`sort_third` is `do let sorted ← collect_thirds l 0 []; rebuild_at l sorted 0 0 []`.
So `sort_third l = ok v` implies `collect_thirds l 0 [] = ok sorted` for some
sorted, and `rebuild_at l sorted 0 0 [] = ok v`. -/

private theorem sort_third_decomp
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_032_sort_third.sort_third l = RustM.ok v) :
    ∃ (sorted : alloc.vec.Vec i64 alloc.alloc.Global),
      clever_032_sort_third.collect_thirds l (0 : usize)
        ⟨(List.nil : List i64).toArray, by grind⟩ = RustM.ok sorted ∧
      clever_032_sort_third.rebuild_at l sorted (0 : usize) (0 : usize)
        ⟨(List.nil : List i64).toArray, by grind⟩ = RustM.ok v := by
  unfold clever_032_sort_third.sort_third at hres
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil).toArray, by grind⟩ := rfl
  rw [h_new, RustM_ok_bind] at hres
  -- Generalize collect_thirds result everywhere (in hres AND in the goal).
  generalize h_ct : clever_032_sort_third.collect_thirds l (0 : usize)
      ⟨(List.nil : List i64).toArray, by grind⟩ = rct at hres ⊢
  cases rct with
  | none =>
    exfalso
    have h1 : (none : RustM (alloc.vec.Vec i64 alloc.alloc.Global)) = RustM.div := rfl
    rw [h1, RustM_div_bind] at hres
    cases hres
  | some res =>
    cases res with
    | error e =>
      exfalso
      have h1 : (some (Except.error e) : RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
          RustM.fail e := rfl
      rw [h1, RustM_fail_bind] at hres
      cases hres
    | ok sorted =>
      refine ⟨sorted, rfl, ?_⟩
      -- After unwinding, the `deref` is `pure sorted`. Then rebuild_at runs.
      have h_some : (some (Except.ok sorted) : RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
          RustM.ok sorted := rfl
      rw [h_some, RustM_ok_bind] at hres
      -- The deref of vec is just `pure sorted`. Reduce:
      have h_deref : (core_models.ops.deref.Deref.deref
          (alloc.vec.Vec i64 alloc.alloc.Global) sorted :
          RustM (alloc.vec.Vec i64 alloc.alloc.Global)) = RustM.ok sorted := rfl
      rw [h_deref, RustM_ok_bind] at hres
      exact hres

/-! ## Top-level theorems closed via `rebuild_at_correct`. -/

/-- Postcondition: the output has the same length as the input. Captures
    the proptest `length_preserved`. -/
theorem length_preserved
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_032_sort_third.sort_third l = RustM.ok v) :
    v.val.size = l.val.size := by
  obtain ⟨sorted, _, hreb⟩ := sort_third_decomp l v hres
  let acc0 : alloc.vec.Vec i64 alloc.alloc.Global :=
    ⟨(List.nil : List i64).toArray, by grind⟩
  have h_acc0_size : acc0.val.size = (0 : usize).toNat := rfl
  have h_acc0_inv :
      ∀ (k : Nat) (hk : k < acc0.val.size) (hk_l : k < l.val.size),
        k % 3 ≠ 0 → acc0.val[k]'hk = l.val[k]'hk_l := by
    intro k hk; exfalso
    have h0 : acc0.val.size = 0 := rfl
    rw [h0] at hk; omega
  have h_meas : l.val.size - (0 : usize).toNat ≤ l.val.size := by
    show l.val.size - 0 ≤ l.val.size; omega
  have h_i_le : (0 : usize).toNat ≤ l.val.size := by
    show 0 ≤ l.val.size; omega
  obtain ⟨h_size, _⟩ :=
    rebuild_at_correct l sorted l.val.size (0 : usize) (0 : usize) acc0 v
      h_meas h_i_le h_acc0_size h_acc0_inv hreb
  exact h_size

/-- Postcondition: at indices `i` with `i % 3 ≠ 0`, the output equals the
    input element-for-element. Captures the proptest
    `non_third_indices_unchanged`. -/
theorem non_third_indices_unchanged
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_032_sort_third.sort_third l = RustM.ok v)
    (i : Nat) (hi_l : i < l.val.size) (hi_v : i < v.val.size)
    (hmod : i % 3 ≠ 0) :
    v.val[i]'hi_v = l.val[i]'hi_l := by
  obtain ⟨sorted, _, hreb⟩ := sort_third_decomp l v hres
  let acc0 : alloc.vec.Vec i64 alloc.alloc.Global :=
    ⟨(List.nil : List i64).toArray, by grind⟩
  have h_acc0_size : acc0.val.size = (0 : usize).toNat := rfl
  have h_acc0_inv :
      ∀ (k : Nat) (hk : k < acc0.val.size) (hk_l : k < l.val.size),
        k % 3 ≠ 0 → acc0.val[k]'hk = l.val[k]'hk_l := by
    intro k hk; exfalso
    have h0 : acc0.val.size = 0 := rfl
    rw [h0] at hk; omega
  have h_meas : l.val.size - (0 : usize).toNat ≤ l.val.size := by
    show l.val.size - 0 ≤ l.val.size; omega
  have h_i_le : (0 : usize).toNat ≤ l.val.size := by
    show 0 ≤ l.val.size; omega
  obtain ⟨_, h_inv⟩ :=
    rebuild_at_correct l sorted l.val.size (0 : usize) (0 : usize) acc0 v
      h_meas h_i_le h_acc0_size h_acc0_inv hreb
  exact h_inv i hi_v hi_l hmod

/-! ## Structural-unblock scaffolding for `third_indices_sorted` and
    `third_indices_are_permutation`.

The two remaining obligations both reduce — via the elementwise structure
of `rebuild_at` (which writes `sorted.val[k/3]` at output index `3*k`) —
to invariants on the *output of `collect_thirds`*. Specifically:

  * `third_indices_sorted` holds iff `sorted` (returned by
    `collect_thirds l 0 []`) is sorted in ascending order.
  * `third_indices_are_permutation` holds iff `sorted` is a permutation
    of `third_values l.val` (the input third-index values, in any order).

Both of these in turn reduce — via the recursive structure of
`collect_thirds` (which inserts `l.val[i]` into the running `sorted` via
`insert_sorted` when `i % 3 = 0`) — to invariants on `insert_sorted_at`:

  * Inserting `x` into a sorted vec yields a sorted vec, with `x`
    placed at a position that maintains sortedness.
  * Inserting `x` into a vec preserves the multiset and adds one copy of `x`.

The needed helper lemmas are stated below as `private theorem`s with their
own `sorry`s, so a future pass can attack them directly. The shapes they
take (and how they compose into the two top-level obligations) are:

  insert_sorted_at_correct :
    insert_sorted_at v x 0 false [] yields a vec that is
    (a) sorted whenever v is sorted, and (b) a multiset-permutation of v ++ [x].

  collect_thirds_correct :
    collect_thirds l 0 [] yields a vec that is
    (a) sorted, and (b) a multiset-permutation of third_values l.val.

  rebuild_at_third_value :
    For k < l.val.size with k % 3 = 0,
    v.val[k] = sorted.val[(k+2)/3]  (the (k/3)-th third index used so far).

The two top-level theorems then chain these together. We leave them as
`sorry` after the substantive attempt in this file. -/

/-- Stub: the result of `collect_thirds l 0 []` is sorted. To be proved
    by induction over `collect_thirds`, dispatching to a similar invariant
    on `insert_sorted_at`. -/
private theorem collect_thirds_sorted_stub
    (l : RustSlice i64)
    (sorted : alloc.vec.Vec i64 alloc.alloc.Global)
    (hct : clever_032_sort_third.collect_thirds l (0 : usize)
        ⟨(List.nil : List i64).toArray, by grind⟩ = RustM.ok sorted) :
    ∀ (a b : Nat) (ha : a < sorted.val.size) (hb : b < sorted.val.size),
      a < b → (sorted.val[a]'ha).toInt ≤ (sorted.val[b]'hb).toInt := by
  /- Stuck: requires a strong-induction proof that `insert_sorted_at v x 0
     false []` produces a sorted vec whenever `v` is sorted (the
     "insertion sort step preserves sortedness" property). This in turn
     needs a careful invariant tracking, in `insert_sorted_at`'s strong
     induction, both the position of insertion and the sortedness
     boundary; not closed in this pass. -/
  sorry

/-- Stub: the result of `collect_thirds l 0 []` is a multiset-permutation
    of the input third-index values, expressed via `List.count`. -/
private theorem collect_thirds_perm_stub
    (l : RustSlice i64)
    (sorted : alloc.vec.Vec i64 alloc.alloc.Global)
    (hct : clever_032_sort_third.collect_thirds l (0 : usize)
        ⟨(List.nil : List i64).toArray, by grind⟩ = RustM.ok sorted) :
    ∀ x : i64,
      (sorted.val.toList.count x) = ((third_values l.val).count x) := by
  /- Stuck: requires the "insert_sorted_at preserves multiset and adds
     one copy of x" invariant, lifted across the `collect_thirds`
     recursion. Not closed in this pass. -/
  sorry

/-- Stub: at output third indices, `rebuild_at` writes the corresponding
    entry of `sorted` in order. Specifically, for the call
    `rebuild_at l sorted 0 0 [] = ok v`, the j-th output third index
    (i.e. position `3 * j`) holds `sorted.val[j]`. -/
private theorem rebuild_at_third_value_stub
    (l : RustSlice i64)
    (sorted : alloc.vec.Vec i64 alloc.alloc.Global)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hreb : clever_032_sort_third.rebuild_at l sorted (0 : usize) (0 : usize)
        ⟨(List.nil : List i64).toArray, by grind⟩ = RustM.ok v) :
    ∀ (k : Nat) (hk_v : k < v.val.size),
      k % 3 = 0 →
      ∃ (hj : (k / 3) < sorted.val.size),
          v.val[k]'hk_v = sorted.val[k / 3]'hj := by
  /- Stuck: needs a strengthened `rebuild_at_correct` that additionally
     tracks the third-index-value invariant (acc.val[k] = sorted.val[k/3]
     for k % 3 = 0 in [0, i.toNat)). The strengthening is mechanical given
     the existing `rebuild_at_correct`; left for a future pass to keep
     this attempt focused. -/
  sorry

/-- Postcondition: at indices `i` with `i % 3 = 0`, the output values
    appear in ascending order. Captures the proptest
    `third_indices_sorted`.

    Stuck at: requires `collect_thirds_sorted_stub` (see above). The
    structural unblock is to prove `insert_sorted_at_correct` (the
    insertion-sort invariant: inserting an element into a sorted vec
    yields a sorted vec). With that lemma, `collect_thirds_sorted_stub`
    follows by induction over `collect_thirds`, and combined with
    `rebuild_at_third_value_stub` (also straightforward to prove by
    strengthening `rebuild_at_correct`) closes this obligation. -/
theorem third_indices_sorted
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_032_sort_third.sort_third l = RustM.ok v)
    (i j : Nat) (hi_v : i < v.val.size) (hj_v : j < v.val.size)
    (hlt : i < j) (hi_mod : i % 3 = 0) (hj_mod : j % 3 = 0) :
    (v.val[i]'hi_v).toInt ≤ (v.val[j]'hj_v).toInt := by
  obtain ⟨sorted, hct, hreb⟩ := sort_third_decomp l v hres
  -- Use the third-value lemma: v[i] = sorted[i/3], v[j] = sorted[j/3].
  obtain ⟨hi_s, hi_eq⟩ := rebuild_at_third_value_stub l sorted v hreb i hi_v hi_mod
  obtain ⟨hj_s, hj_eq⟩ := rebuild_at_third_value_stub l sorted v hreb j hj_v hj_mod
  rw [hi_eq, hj_eq]
  -- Now show sorted[i/3] ≤ sorted[j/3], using i/3 < j/3 (since i < j and
  -- i, j both divisible by 3).
  have hidiv_lt : i / 3 < j / 3 := by
    have h_i := Nat.div_add_mod i 3
    have h_j := Nat.div_add_mod j 3
    omega
  exact collect_thirds_sorted_stub l sorted hct (i / 3) (j / 3) hi_s hj_s hidiv_lt

/-- Postcondition: the multiset of values at indices divisible by 3 in the
    output equals the multiset of values at those same indices in the
    input. Captures the proptest `third_indices_are_permutation`.

    Stuck at: requires `collect_thirds_perm_stub` (see above). The
    structural unblock is to prove `insert_sorted_at_correct`'s
    multiset-preservation half (inserting `x` into `v` yields a vec
    whose multiset is `v ++ [x]`'s multiset). With that lemma,
    `collect_thirds_perm_stub` follows by induction. We additionally
    need a bridge lemma `third_values_eq_via_rebuild_at` showing that
    `third_values v.val` equals `sorted.val.toList` when
    `rebuild_at l sorted 0 0 [] = ok v` — a corollary of the strengthened
    `rebuild_at_correct` that also tracks `acc.val[k] = sorted.val[k/3]`. -/
theorem third_indices_are_permutation
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_032_sort_third.sort_third l = RustM.ok v) :
    ∀ x : i64, (third_values v.val).count x = (third_values l.val).count x := by
  /- Stuck: this needs both
     (a) `collect_thirds_perm_stub` (third_values l.val ~ sorted.val), and
     (b) a bridge `third_values v.val = sorted.val.toList` (because
         rebuild_at writes sorted.val[k/3] at every third position of v).
     (a) requires the multiset-preservation half of insert_sorted_at_correct;
     (b) requires the strengthened rebuild_at_correct that tracks third
     positions. Neither is closed in this pass; both have stubs above. -/
  sorry

end Clever_032_sort_thirdObligations
