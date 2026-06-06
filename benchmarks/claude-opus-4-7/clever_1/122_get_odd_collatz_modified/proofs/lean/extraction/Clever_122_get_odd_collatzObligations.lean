-- Companion obligations file for the `clever_122_get_odd_collatz` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_122_get_odd_collatz

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_122_get_odd_collatzObligations

/-! ## Specification oracles for the postconditions.

The Rust source phrases its three contract-style proptests via two
auxiliary notions: (i) strict ascending order on the result vector, and
(ii) reachability under the Collatz step relation. We mirror both at
the `Nat` level so the obligations are independent of the
implementation under verification. -/

/-- Strictly ascending order on a `u64` array. Matches the proptest
    `prop_sorted_strictly_ascending`, which checks `r[i-1] < r[i]`. -/
private def strict_asc (arr : Array u64) : Prop :=
  ∀ (k₁ k₂ : Nat) (h₁ : k₁ < arr.size) (h₂ : k₂ < arr.size),
    k₁ < k₂ → (arr[k₁]'h₁).toNat < (arr[k₂]'h₂).toNat

/-- One Collatz step on `Nat`. Matches the iteration body of the Rust
    `step_at` (and of the `reference` oracle in the test): `x/2` if `x`
    is even, `3 * x + 1` otherwise. -/
private def collatz_step (x : Nat) : Nat :=
  if x % 2 = 0 then x / 2 else 3 * x + 1

/-- Apply `collatz_step` `k` times. -/
private def collatz_iter : Nat → Nat → Nat
  | 0,     x => x
  | k + 1, x => collatz_iter k (collatz_step x)

/-- `v` is reachable from `n` via some finite number of Collatz steps. -/
private def collatz_reachable (n v : Nat) : Prop :=
  ∃ k : Nat, collatz_iter k n = v

/-! ## Unit pins.

The Rust source includes three exact-input tests:
  * `zero_is_empty`  — `get_odd_collatz(0) = []`.
  * `known`          — `get_odd_collatz(1) = [1]` and `get_odd_collatz(5) = [1, 5]`.

Note(termination): `step_at` is extracted with `partial_fixpoint` since
total termination of the Collatz iteration is an open conjecture. The
function is nonetheless computable end-to-end on any concrete input
whose orbit reaches `1`: `native_decide` evaluates the fixpoint kernel
by kernel, threading `RustM` through each step. -/

/-- Anchor pin (from `zero_is_empty`): the empty input yields the empty
    vector. The `n = 0` branch short-circuits before `step_at`, so this
    holds independently of the partial-fixpoint termination. Stated
    existentially because `alloc.vec.Vec u64 _` is a Subtype carrying a
    proof component, so `DecidableEq` does not auto-derive cleanly. -/
theorem get_odd_collatz_zero_is_empty :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_122_get_odd_collatz.get_odd_collatz (0 : u64) = RustM.ok v
      ∧ v.val.toList = [] := by
  refine ⟨⟨(List.nil).toArray, by grind⟩, ?_, rfl⟩
  rfl

/-- Local DecidableEq instance for `Seq u64`: reduces to `DecidableEq (Array u64)`
    on the `.val` field; the `size_lt_usizeSize` proof field is propositionally
    irrelevant. Needed to make `native_decide` accept goals of the form
    `RustM.ok ⟨arr, _⟩ = RustM.ok ⟨arr', _⟩` in unit pins. -/
instance : DecidableEq (rust_primitives.sequence.Seq u64) := fun a b =>
  if h : a.val = b.val then
    isTrue (by cases a; cases b; cases h; rfl)
  else
    isFalse (by intro heq; cases heq; exact h rfl)

/-- Unit pin (from `known`): `get_odd_collatz(1) = [1]`. -/
theorem get_odd_collatz_at_one :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_122_get_odd_collatz.get_odd_collatz (1 : u64) = RustM.ok v
      ∧ v.val.toList = [(1 : u64)] := by
  refine ⟨⟨#[(1 : u64)], by decide⟩, ?_, rfl⟩
  native_decide

/-- Unit pin (from `known`): `get_odd_collatz(5) = [1, 5]`. -/
theorem get_odd_collatz_at_five :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_122_get_odd_collatz.get_odd_collatz (5 : u64) = RustM.ok v
      ∧ v.val.toList = [(1 : u64), (5 : u64)] := by
  refine ⟨⟨#[(1 : u64), (5 : u64)], by decide⟩, ?_, rfl⟩
  native_decide

/-! ## Standard scaffolding for universal proofs. -/

@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl
private theorem usize_zero_toNat : (0 : usize).toNat = 0 := rfl
private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

/-- Boolean: all elements of an `Array u64` are odd at the `Nat` level. -/
private def all_odd_pred (arr : Array u64) : Prop :=
  ∀ (k : Nat) (h : k < arr.size), (arr[k]'h).toNat % 2 = 1

/-- The empty array trivially satisfies `all_odd_pred`. -/
private theorem all_odd_pred_empty : all_odd_pred (#[] : Array u64) := by
  intro k h
  have h_size : (#[] : Array u64).size = 0 := rfl
  rw [h_size] at h
  exact absurd h (Nat.not_lt_zero _)

/-- Pushing an odd element preserves `all_odd_pred`. -/
private theorem all_odd_pred_append (acc : Array u64) (y : u64)
    (h_acc : all_odd_pred acc) (h_y : y.toNat % 2 = 1) :
    all_odd_pred (acc ++ #[y]) := by
  intro k hk
  rw [Array.size_append] at hk
  have h_one : (#[y] : Array u64).size = 1 := rfl
  by_cases h_lt : k < acc.size
  · rw [Array.getElem_append_left h_lt]
    exact h_acc k h_lt
  · have h_ge : acc.size ≤ k := Nat.le_of_not_lt h_lt
    rw [Array.getElem_append_right h_ge]
    have h_idx : k - acc.size = 0 := by omega
    have h_zero : (0 : Nat) < (#[y] : Array u64).size := by rw [h_one]; omega
    rw [show ((#[y] : Array u64)[k - acc.size]'(by rw [h_idx]; exact h_zero))
            = (#[y] : Array u64)[0]'h_zero from by simp [h_idx]]
    exact h_y

/-! ## Admissibility helpers for fixpoint induction.

`step_at.fixpoint_induct` and `insert_asc_at.fixpoint_induct` both require
an `admissible` proof for the motive. Our motives all have the shape
"for all inputs, if the function returns `RustM.ok v` then ψ v". Since
`RustM` uses the `FlatOrder` with bottom = `RustM.div`, any predicate
on `RustM α` that is vacuously true on `RustM.div` is admissible
(`admissible_flatOrder`). Composed with `admissible_pi` and
`admissible_apply` we get a recipe for the motive's admissibility. -/

open Lean.Order in
/-- Admissibility of `λ r, r = RustM.ok b → P` on `RustM α`. The bottom
    `RustM.div ≠ RustM.ok b`, so the predicate holds vacuously at the bot. -/
private theorem admissible_eq_ok_implies {α : Type} (b : α) (P : Prop) :
    Lean.Order.admissible (fun (r : RustM α) => r = RustM.ok b → P) := by
  apply Lean.Order.admissible_flatOrder
  intro h
  -- h : (none : RustM α) = RustM.ok b = some (Except.ok b). Impossible.
  cases h

/-! ## `insert_asc_at` step lemmas (adapted from `clever_103`'s pattern). -/

/-- Push a single element onto an `alloc.vec.Vec`. -/
private def push_one (acc : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec u64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

private theorem push_one_size (acc : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (h : acc.val.size + 1 < USize64.size) :
    (push_one acc x h).val.size = acc.val.size + 1 := by
  show (acc.val ++ #[x]).size = acc.val.size + 1
  rw [Array.size_append]; rfl

private theorem push_one_all_odd (acc : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (h : acc.val.size + 1 < USize64.size)
    (h_acc : all_odd_pred acc.val) (h_x : x.toNat % 2 = 1) :
    all_odd_pred (push_one acc x h).val := by
  show all_odd_pred (acc.val ++ #[x])
  exact all_odd_pred_append acc.val x h_acc h_x

private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide

private theorem usize_add_one_ok (i : usize) (h : i.toNat + 1 < 2^64) :
    (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
  show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
  show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
        then (.fail .integerOverflow : RustM usize)
        else pure (i + 1)) = _
  have h_no_bv :
      BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hii := (USize64.uaddOverflow_iff i 1).mp hbo
      rw [usize_one_toNat] at hii
      omega
  rw [h_no_bv]; rfl

private theorem insert_asc_at_oob_done (v : RustSlice u64) (x : u64)
    (i : usize) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat) :
    clever_122_get_odd_collatz.insert_asc_at v x i true acc = RustM.ok acc := by
  unfold clever_122_get_odd_collatz.insert_asc_at
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat v.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]; rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

private theorem insert_asc_at_oob_not_done (v : RustSlice u64) (x : u64)
    (i : usize) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_122_get_odd_collatz.insert_asc_at v x i false acc =
      RustM.ok (push_one acc x h_acc) := by
  unfold clever_122_get_odd_collatz.insert_asc_at
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat v.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]; rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  have h_app_size :
      acc.val.size + (#[x] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  have h_extend :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[x], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.ok (push_one acc x h_acc) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[x] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[x], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend]
  rfl

private theorem insert_asc_at_oob_not_done_fail (v : RustSlice u64) (x : u64)
    (i : usize) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_122_get_odd_collatz.insert_asc_at v x i false acc
      = RustM.fail .maximumSizeExceeded := by
  unfold clever_122_get_odd_collatz.insert_asc_at
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat v.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]; rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  have h_app_size_neg :
      ¬ acc.val.size + (#[x] : Array u64).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[x], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[x] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[x], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

/-! ## `vec_contains` step lemmas and characterization. -/

/-- Out-of-bounds: when `i.toNat ≥ v.val.size`, vec_contains returns `false`. -/
private theorem vec_contains_oob (v : RustSlice u64) (x : u64) (i : usize)
    (hi : v.val.size ≤ i.toNat) :
    clever_122_get_odd_collatz.vec_contains v x i = RustM.ok false := by
  conv => lhs; unfold clever_122_get_odd_collatz.vec_contains
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat v.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]; rw [USize64.le_iff_toNat_le, h_ofNat]; exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- Found step: when `i.toNat < v.val.size` and `v[i] = x`, returns `true`. -/
private theorem vec_contains_found (v : RustSlice u64) (x : u64) (i : usize)
    (hi : i.toNat < v.val.size) (h : v.val[i.toNat]'hi = x) :
    clever_122_get_odd_collatz.vec_contains v x i = RustM.ok true := by
  conv => lhs; unfold clever_122_get_odd_collatz.vec_contains
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM u64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_beq_true : (v.val[i.toNat]'hi == x) = true := by
    rw [beq_iff_eq]; exact h
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.cmp.eq, h_beq_true]
  rfl

/-- Recursion step: when `i.toNat < v.val.size` and `v[i] ≠ x`, recurse with i+1. -/
private theorem vec_contains_recurse (v : RustSlice u64) (x : u64) (i : usize)
    (hi : i.toNat < v.val.size) (h : v.val[i.toNat]'hi ≠ x) :
    clever_122_get_odd_collatz.vec_contains v x i =
      clever_122_get_odd_collatz.vec_contains v x (i + 1) := by
  conv => lhs; unfold clever_122_get_odd_collatz.vec_contains
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_no_overflow : i.toNat + 1 < 2^64 := by
    have h_eq : USize64.size = 2^64 := usize_size_eq
    rw [h_eq] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM u64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_beq_false : (v.val[i.toNat]'hi == x) = false := by
    rw [beq_eq_false_iff_ne]; exact h
  have h_add : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) :=
    usize_add_one_ok i h_no_overflow
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.cmp.eq, h_beq_false]
  rw [h_add]
  rfl

/-- Membership characterization of `vec_contains`: it returns `ok true` iff there is a
    witness index in [i.toNat, v.val.size) where `v[j] = x`. -/
private theorem vec_contains_iff (v : RustSlice u64) (x : u64) (i : usize) :
    clever_122_get_odd_collatz.vec_contains v x i = RustM.ok true ↔
    ∃ j : Nat, i.toNat ≤ j ∧ ∃ (hj : j < v.val.size), v.val[j]'hj = x := by
  induction hk : (v.val.size - i.toNat) using Nat.strongRecOn generalizing i with
  | _ k ih =>
    by_cases hbound : v.val.size ≤ i.toNat
    · rw [vec_contains_oob v x i hbound]
      apply iff_of_false
      · intro h; injection h with h1; injection h1 with h2; exact Bool.noConfusion h2
      · rintro ⟨j, hij, hjsize, hjeq⟩
        omega
    · have hbound' : i.toNat < v.val.size := Nat.lt_of_not_le hbound
      by_cases hit : v.val[i.toNat]'hbound' = x
      · rw [vec_contains_found v x i hbound' hit]
        constructor
        · intro _; exact ⟨i.toNat, Nat.le_refl _, hbound', hit⟩
        · intro _; rfl
      · rw [vec_contains_recurse v x i hbound' hit]
        have h_size : v.val.size < 2^64 := v.size_lt_usizeSize
        have h_no_overflow : i.toNat + 1 < 2^64 := by omega
        have h_i1_toNat : (i + 1).toNat = i.toNat + 1 :=
          usize_add_one_toNat i h_no_overflow
        have h_measure_lt : v.val.size - (i + 1).toNat < k := by
          rw [h_i1_toNat]; omega
        have ih_i1 := ih (v.val.size - (i + 1).toNat) h_measure_lt (i + 1) rfl
        rw [ih_i1]
        constructor
        · rintro ⟨j, hij, hjsize, hjeq⟩
          refine ⟨j, ?_, hjsize, hjeq⟩
          rw [h_i1_toNat] at hij; omega
        · rintro ⟨j, hij, hjsize, hjeq⟩
          refine ⟨j, ?_, hjsize, hjeq⟩
          rw [h_i1_toNat]
          rcases Nat.lt_or_ge i.toNat j with hlt | hge
          · omega
          · have hj_eq_i : j = i.toNat := by omega
            exfalso; apply hit
            rw [← hjeq]; congr 1; exact hj_eq_i.symm

/-- Negation characterization: `vec_contains v x i = ok false` iff no witness exists. -/
private theorem vec_contains_false_iff (v : RustSlice u64) (x : u64) (i : usize) :
    clever_122_get_odd_collatz.vec_contains v x i = RustM.ok false ↔
    ∀ j : Nat, i.toNat ≤ j → ∀ (hj : j < v.val.size), v.val[j]'hj ≠ x := by
  induction hk : (v.val.size - i.toNat) using Nat.strongRecOn generalizing i with
  | _ k ih =>
    by_cases hbound : v.val.size ≤ i.toNat
    · rw [vec_contains_oob v x i hbound]
      apply iff_of_true rfl
      intro j hij hj; omega
    · have hbound' : i.toNat < v.val.size := Nat.lt_of_not_le hbound
      by_cases hit : v.val[i.toNat]'hbound' = x
      · rw [vec_contains_found v x i hbound' hit]
        apply iff_of_false
        · intro h; injection h with h1; injection h1 with h2; exact Bool.noConfusion h2
        · intro hno
          exact hno i.toNat (Nat.le_refl _) hbound' hit
      · rw [vec_contains_recurse v x i hbound' hit]
        have h_size : v.val.size < 2^64 := v.size_lt_usizeSize
        have h_no_overflow : i.toNat + 1 < 2^64 := by omega
        have h_i1_toNat : (i + 1).toNat = i.toNat + 1 :=
          usize_add_one_toNat i h_no_overflow
        have h_measure_lt : v.val.size - (i + 1).toNat < k := by
          rw [h_i1_toNat]; omega
        have ih_i1 := ih (v.val.size - (i + 1).toNat) h_measure_lt (i + 1) rfl
        rw [ih_i1]
        constructor
        · intro hno j hij hj
          by_cases h_j : j = i.toNat
          · subst h_j; exact hit
          · apply hno j (by rw [h_i1_toNat]; omega) hj
        · intro hno j hij hj
          apply hno j (by rw [h_i1_toNat] at hij; omega) hj

/-- Convenience: vec_contains over a Vec (passed as RustSlice via deref). -/
private theorem vec_contains_vec_iff_true (acc : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64) :
    clever_122_get_odd_collatz.vec_contains
      ⟨acc.val, acc.size_lt_usizeSize⟩ x (0 : usize) = RustM.ok true ↔
    ∃ j : Nat, ∃ (hj : j < acc.val.size), acc.val[j]'hj = x := by
  rw [vec_contains_iff]
  show (∃ j, (0 : usize).toNat ≤ j ∧ ∃ (hj : j < acc.val.size), acc.val[j]'hj = x) ↔ _
  constructor
  · rintro ⟨j, _, hj, h⟩; exact ⟨j, hj, h⟩
  · rintro ⟨j, hj, h⟩; exact ⟨j, Nat.zero_le _, hj, h⟩

private theorem vec_contains_vec_iff_false (acc : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64) :
    clever_122_get_odd_collatz.vec_contains
      ⟨acc.val, acc.size_lt_usizeSize⟩ x (0 : usize) = RustM.ok false ↔
    ∀ j : Nat, ∀ (hj : j < acc.val.size), acc.val[j]'hj ≠ x := by
  rw [vec_contains_false_iff]
  constructor
  · intro h j hj; exact h j (Nat.zero_le _) hj
  · intro h j _ hj; exact h j hj

/-! ## `insert_asc_at` in-bounds step lemmas (5 cases).

The body of `insert_asc_at` in-bounds branches as follows. Given `v[i]`:
  * `done = true,  v[i] = x` — skip both pushes, recurse with same `acc`.
  * `done = true,  v[i] ≠ x` — push `v[i]`, recurse `(i+1, true, acc++[v[i]])`.
  * `done = false, v[i] < x` — push `v[i]`, recurse `(i+1, false, acc++[v[i]])`.
  * `done = false, v[i] = x` — push `x` (sets new_done=true); since `v[i]=x`,
                                skip second push, recurse `(i+1, true, acc++[x])`.
  * `done = false, v[i] > x` — push `x`, push `v[i]`, recurse `(i+1, true,
                                acc++[x]++[v[i]])`. -/

-- The common "outer cond / index / overflow" preamble.
section InsertAscAtSteps
variable (v : RustSlice u64) (x : u64) (i : usize) (acc : alloc.vec.Vec u64 alloc.alloc.Global)

private theorem insert_asc_at_step_skip_dup
    (hi : i.toNat < v.val.size) (h_eq : v.val[i.toNat]'hi = x) :
    clever_122_get_odd_collatz.insert_asc_at v x i true acc =
      clever_122_get_odd_collatz.insert_asc_at v x (i + 1) true acc := by
  conv => lhs; unfold clever_122_get_odd_collatz.insert_asc_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM u64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds) = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_add : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := usize_add_one_ok i h_no_ov_i
  -- v[i] = x ⇒ v[i] != x is false; with done=true, !done = false, so the push branch
  -- and the second-push condition both collapse.
  have h_bne_false : ((v.val[i.toNat]'hi) != x) = false := by
    simp [h_eq]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.hax.logical_op.not, Bool.not_true,
             rust_primitives.hax.logical_op.and, Bool.false_and,
             rust_primitives.hax.logical_op.or, Bool.false_or,
             rust_primitives.cmp.ne, h_bne_false]
  rw [h_add]
  rfl

private theorem insert_asc_at_step_done_push
    (hi : i.toNat < v.val.size) (h_neq : v.val[i.toNat]'hi ≠ x)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_122_get_odd_collatz.insert_asc_at v x i true acc =
      clever_122_get_odd_collatz.insert_asc_at v x (i + 1) true
        (push_one acc (v.val[i.toNat]'hi) h_acc) := by
  conv => lhs; unfold clever_122_get_odd_collatz.insert_asc_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM u64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds) = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_add : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := usize_add_one_ok i h_no_ov_i
  have h_bne_true : ((v.val[i.toNat]'hi) != x) = true := by
    simp [bne_iff_ne]; exact h_neq
  have h_app_size_vi :
      acc.val.size + (#[(v.val[i.toNat]'hi)] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  have h_extend_vi :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[(v.val[i.toNat]'hi)], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.ok (push_one acc (v.val[i.toNat]'hi) h_acc) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size_vi]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.hax.logical_op.not, Bool.not_true,
             rust_primitives.hax.logical_op.and, Bool.false_and,
             rust_primitives.hax.logical_op.or, Bool.false_or,
             rust_primitives.cmp.ne, h_bne_true]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[(v.val[i.toNat]'hi)] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[(v.val[i.toNat]'hi)], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_vi]
  simp only [RustM_ok_bind]
  rw [h_add]
  rfl

private theorem insert_asc_at_step_done_push_fail
    (hi : i.toNat < v.val.size) (h_neq : v.val[i.toNat]'hi ≠ x)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_122_get_odd_collatz.insert_asc_at v x i true acc = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_122_get_odd_collatz.insert_asc_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM u64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds) = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_bne_true : ((v.val[i.toNat]'hi) != x) = true := by
    simp [bne_iff_ne]; exact h_neq
  have h_app_size_vi_neg :
      ¬ acc.val.size + (#[(v.val[i.toNat]'hi)] : Array u64).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[(v.val[i.toNat]'hi)], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_vi_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.hax.logical_op.not, Bool.not_true,
             rust_primitives.hax.logical_op.and, Bool.false_and,
             rust_primitives.hax.logical_op.or, Bool.false_or,
             rust_primitives.cmp.ne, h_bne_true]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[(v.val[i.toNat]'hi)] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[(v.val[i.toNat]'hi)], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

private theorem insert_asc_at_step_pass
    (hi : i.toNat < v.val.size) (h_lt : (v.val[i.toNat]'hi).toNat < x.toNat)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_122_get_odd_collatz.insert_asc_at v x i false acc =
      clever_122_get_odd_collatz.insert_asc_at v x (i + 1) false
        (push_one acc (v.val[i.toNat]'hi) h_acc) := by
  conv => lhs; unfold clever_122_get_odd_collatz.insert_asc_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM u64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds) = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_add : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := usize_add_one_ok i h_no_ov_i
  -- v[i] < x means v[i] >= x is false; with done = false, the AND test gives false.
  have h_ge_false : (decide ((v.val[i.toNat]'hi) ≥ x)) = false := by
    rw [decide_eq_false_iff_not]
    rw [show ((v.val[i.toNat]'hi) ≥ x) = (x ≤ (v.val[i.toNat]'hi)) from rfl]
    rw [UInt64.le_iff_toNat_le]; omega
  have h_app_size_vi :
      acc.val.size + (#[(v.val[i.toNat]'hi)] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  have h_extend_vi :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[(v.val[i.toNat]'hi)], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.ok (push_one acc (v.val[i.toNat]'hi) h_acc) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size_vi]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.hax.logical_op.not, Bool.not_false,
             rust_primitives.hax.logical_op.and, h_ge_false, Bool.true_and,
             rust_primitives.hax.logical_op.or, Bool.true_or]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[(v.val[i.toNat]'hi)] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[(v.val[i.toNat]'hi)], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_vi]
  simp only [RustM_ok_bind]
  rw [h_add]
  rfl

private theorem insert_asc_at_step_pass_fail
    (hi : i.toNat < v.val.size) (h_lt : (v.val[i.toNat]'hi).toNat < x.toNat)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_122_get_odd_collatz.insert_asc_at v x i false acc = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_122_get_odd_collatz.insert_asc_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM u64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds) = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_ge_false : (decide ((v.val[i.toNat]'hi) ≥ x)) = false := by
    rw [decide_eq_false_iff_not]
    rw [show ((v.val[i.toNat]'hi) ≥ x) = (x ≤ (v.val[i.toNat]'hi)) from rfl]
    rw [UInt64.le_iff_toNat_le]; omega
  have h_app_size_vi_neg :
      ¬ acc.val.size + (#[(v.val[i.toNat]'hi)] : Array u64).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[(v.val[i.toNat]'hi)], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_vi_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.hax.logical_op.not, Bool.not_false,
             rust_primitives.hax.logical_op.and, h_ge_false, Bool.true_and,
             rust_primitives.hax.logical_op.or, Bool.true_or]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[(v.val[i.toNat]'hi)] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[(v.val[i.toNat]'hi)], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

private theorem insert_asc_at_step_insert_dup
    (hi : i.toNat < v.val.size) (h_eq : v.val[i.toNat]'hi = x)
    (h_acc : acc.val.size + 1 < USize64.size) :
    clever_122_get_odd_collatz.insert_asc_at v x i false acc =
      clever_122_get_odd_collatz.insert_asc_at v x (i + 1) true
        (push_one acc x h_acc) := by
  conv => lhs; unfold clever_122_get_odd_collatz.insert_asc_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM u64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds) = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_add : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := usize_add_one_ok i h_no_ov_i
  -- v[i] = x, so v[i] ≥ x is true (in fact equal). And v[i] != x is false.
  have h_ge_true : (decide ((v.val[i.toNat]'hi) ≥ x)) = true := by
    rw [decide_eq_true_iff]
    rw [show ((v.val[i.toNat]'hi) ≥ x) = (x ≤ (v.val[i.toNat]'hi)) from rfl]
    rw [h_eq, UInt64.le_iff_toNat_le]; exact Nat.le_refl _
  have h_bne_false : ((v.val[i.toNat]'hi) != x) = false := by
    simp [h_eq]
  have h_app_size_x :
      acc.val.size + (#[x] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc
  have h_extend_x :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[x], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.ok (push_one acc x h_acc) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size_x]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.hax.logical_op.not, Bool.not_false, Bool.not_true,
             rust_primitives.hax.logical_op.and, h_ge_true, Bool.true_and,
             rust_primitives.hax.logical_op.or, Bool.false_or,
             rust_primitives.cmp.ne, h_bne_false]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[x] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[x], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_x]
  simp only [RustM_ok_bind]
  rw [h_add]
  rfl

private theorem insert_asc_at_step_insert_dup_fail
    (hi : i.toNat < v.val.size) (h_eq : v.val[i.toNat]'hi = x)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_122_get_odd_collatz.insert_asc_at v x i false acc = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_122_get_odd_collatz.insert_asc_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM u64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds) = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_ge_true : (decide ((v.val[i.toNat]'hi) ≥ x)) = true := by
    rw [decide_eq_true_iff]
    rw [show ((v.val[i.toNat]'hi) ≥ x) = (x ≤ (v.val[i.toNat]'hi)) from rfl]
    rw [h_eq, UInt64.le_iff_toNat_le]; exact Nat.le_refl _
  have h_app_size_neg :
      ¬ acc.val.size + (#[x] : Array u64).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[x], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.hax.logical_op.not, Bool.not_false,
             rust_primitives.hax.logical_op.and, h_ge_true, Bool.true_and]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[x] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[x], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

private theorem insert_asc_at_step_insert
    (hi : i.toNat < v.val.size) (h_gt : x.toNat < (v.val[i.toNat]'hi).toNat)
    (h_acc : acc.val.size + 2 < USize64.size) :
    clever_122_get_odd_collatz.insert_asc_at v x i false acc =
      clever_122_get_odd_collatz.insert_asc_at v x (i + 1) true
        (push_one (push_one acc x (by omega)) (v.val[i.toNat]'hi)
          (by rw [push_one_size]; omega)) := by
  conv => lhs; unfold clever_122_get_odd_collatz.insert_asc_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_usize_size : USize64.size = 2 ^ 64 := usize_size_eq
  have h_no_ov_i : i.toNat + 1 < 2^64 := by rw [h_usize_size] at h_size_lt; omega
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM u64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds) = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_add : (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := usize_add_one_ok i h_no_ov_i
  -- v[i] > x ⇒ v[i] ≥ x is true; v[i] ≠ x is true.
  have h_ge_true : (decide ((v.val[i.toNat]'hi) ≥ x)) = true := by
    rw [decide_eq_true_iff]
    rw [show ((v.val[i.toNat]'hi) ≥ x) = (x ≤ (v.val[i.toNat]'hi)) from rfl]
    rw [UInt64.le_iff_toNat_le]; omega
  have h_bne_true : ((v.val[i.toNat]'hi) != x) = true := by
    simp [bne_iff_ne]; intro h_eq
    have : (v.val[i.toNat]'hi).toNat = x.toNat := by rw [h_eq]
    omega
  have h_acc_x : acc.val.size + 1 < USize64.size := by omega
  have h_acc_vi : (push_one acc x h_acc_x).val.size + 1 < USize64.size := by
    rw [push_one_size]; omega
  have h_app_size_x :
      acc.val.size + (#[x] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc_x
  have h_extend_x :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[x], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.ok (push_one acc x h_acc_x) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size_x]; rfl
  have h_app_size_vi :
      (push_one acc x h_acc_x).val.size +
        (#[(v.val[i.toNat]'hi)] : Array u64).size < USize64.size := by
    show (push_one acc x h_acc_x).val.size + 1 < USize64.size; exact h_acc_vi
  have h_extend_vi :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global (push_one acc x h_acc_x)
        ⟨#[(v.val[i.toNat]'hi)], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.ok (push_one (push_one acc x h_acc_x) (v.val[i.toNat]'hi) h_acc_vi) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size_vi]; rfl
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.hax.logical_op.not, Bool.not_false, Bool.not_true,
             rust_primitives.hax.logical_op.and, h_ge_true, Bool.true_and,
             rust_primitives.hax.logical_op.or, Bool.false_or,
             rust_primitives.cmp.ne, h_bne_true]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[x] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[x], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_x]
  simp only [RustM_ok_bind]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[(v.val[i.toNat]'hi)] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[(v.val[i.toNat]'hi)], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_vi]
  simp only [RustM_ok_bind]
  rw [h_add]
  rfl

-- The two fail variants of the insert branch (push x overflow / push v[i] overflow).
private theorem insert_asc_at_step_insert_fail_x
    (hi : i.toNat < v.val.size) (h_gt : x.toNat < (v.val[i.toNat]'hi).toNat)
    (h_big : USize64.size ≤ acc.val.size + 1) :
    clever_122_get_odd_collatz.insert_asc_at v x i false acc = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_122_get_odd_collatz.insert_asc_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM u64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds) = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_ge_true : (decide ((v.val[i.toNat]'hi) ≥ x)) = true := by
    rw [decide_eq_true_iff]
    rw [show ((v.val[i.toNat]'hi) ≥ x) = (x ≤ (v.val[i.toNat]'hi)) from rfl]
    rw [UInt64.le_iff_toNat_le]; omega
  have h_app_size_neg :
      ¬ acc.val.size + (#[x] : Array u64).size < USize64.size := by
    show ¬ acc.val.size + 1 < USize64.size; omega
  have h_extend_fail :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[x], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.hax.logical_op.not, Bool.not_false,
             rust_primitives.hax.logical_op.and, h_ge_true, Bool.true_and]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[x] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[x], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_fail]
  rfl

private theorem insert_asc_at_step_insert_fail_vi
    (hi : i.toNat < v.val.size) (h_gt : x.toNat < (v.val[i.toNat]'hi).toNat)
    (h_acc_x : acc.val.size + 1 < USize64.size)
    (h_big : USize64.size ≤ acc.val.size + 2) :
    clever_122_get_odd_collatz.insert_asc_at v x i false acc = RustM.fail .maximumSizeExceeded := by
  conv => lhs; unfold clever_122_get_odd_collatz.insert_asc_at
  have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' h_size_lt
  have h_cond_outer : decide (USize64.ofNat v.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle; rw [USize64.le_iff_toNat_le, h_ofNat] at hle; omega
  have h_idx : (v[i]_? : RustM u64) = RustM.ok (v.val[i.toNat]'hi) := by
    show (if h : i.toNat < v.val.size then pure (v.val[i])
            else .fail .arrayOutOfBounds) = RustM.ok (v.val[i.toNat]'hi)
    rw [dif_pos hi]; rfl
  have h_ge_true : (decide ((v.val[i.toNat]'hi) ≥ x)) = true := by
    rw [decide_eq_true_iff]
    rw [show ((v.val[i.toNat]'hi) ≥ x) = (x ≤ (v.val[i.toNat]'hi)) from rfl]
    rw [UInt64.le_iff_toNat_le]; omega
  have h_bne_true : ((v.val[i.toNat]'hi) != x) = true := by
    simp [bne_iff_ne]; intro h_eq
    have : (v.val[i.toNat]'hi).toNat = x.toNat := by rw [h_eq]
    omega
  have h_app_size_x :
      acc.val.size + (#[x] : Array u64).size < USize64.size := by
    show acc.val.size + 1 < USize64.size; exact h_acc_x
  have h_extend_x :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[x], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.ok (push_one acc x h_acc_x) := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_pos h_app_size_x]; rfl
  have h_app_size_vi_neg :
      ¬ (push_one acc x h_acc_x).val.size +
          (#[(v.val[i.toNat]'hi)] : Array u64).size < USize64.size := by
    rw [push_one_size]
    show ¬ acc.val.size + 1 + 1 < USize64.size; omega
  have h_extend_vi_fail :
      (alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global (push_one acc x h_acc_x)
        ⟨#[(v.val[i.toNat]'hi)], one_lt_usize_size⟩
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.fail .maximumSizeExceeded := by
    unfold alloc.vec.Impl_2.extend_from_slice
    rw [dif_neg h_app_size_vi_neg]
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond_outer, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.hax.logical_op.not, Bool.not_false, Bool.not_true,
             rust_primitives.hax.logical_op.and, h_ge_true, Bool.true_and,
             rust_primitives.hax.logical_op.or, Bool.false_or,
             rust_primitives.cmp.ne, h_bne_true]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[x] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[x], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_x]
  simp only [RustM_ok_bind]
  rw [show (rust_primitives.unsize (RustArray.ofVec #v[(v.val[i.toNat]'hi)] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
          = RustM.ok ⟨#[(v.val[i.toNat]'hi)], one_lt_usize_size⟩ from rfl]
  simp only [RustM_ok_bind]
  rw [h_extend_vi_fail]
  rfl

end InsertAscAtSteps

/-! ## Structural invariants of `insert_asc_at` (strong induction on the measure
    `v.val.size - i.toNat`). -/

/-- Empty Vec witness; used as starting acc in `insert_asc`. -/
private def emptyVec : alloc.vec.Vec u64 alloc.alloc.Global :=
  ⟨(List.nil).toArray, by grind⟩

private theorem emptyVec_size : emptyVec.val.size = 0 := rfl

private theorem emptyVec_all_odd : all_odd_pred emptyVec.val := all_odd_pred_empty

/-- Push-one preserves `all_odd_pred` (specialized variant). -/
private theorem all_odd_push_one (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (y : u64) (h : acc.val.size + 1 < USize64.size)
    (h_acc : all_odd_pred acc.val) (h_y : y.toNat % 2 = 1) :
    all_odd_pred (push_one acc y h).val :=
  all_odd_pred_append acc.val y h_acc h_y

/-- All-odd preservation by `insert_asc_at`. -/
private theorem insert_asc_at_all_odd_aux :
    ∀ (n : Nat) (v : RustSlice u64) (x : u64) (i : usize) (done : Bool)
      (acc r : alloc.vec.Vec u64 alloc.alloc.Global),
      v.val.size - i.toNat ≤ n →
      i.toNat ≤ v.val.size →
      clever_122_get_odd_collatz.insert_asc_at v x i done acc = RustM.ok r →
      all_odd_pred v.val →
      x.toNat % 2 = 1 →
      all_odd_pred acc.val →
      all_odd_pred r.val := by
  intro n
  induction n with
  | zero =>
    intro v x i done acc r hm hi_le hres h_v h_x h_acc
    have hi_ge : v.val.size ≤ i.toNat := by omega
    cases done with
    | true =>
      rw [insert_asc_at_oob_done v x i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'; exact h_acc
    | false =>
      by_cases h_size : acc.val.size + 1 < USize64.size
      · rw [insert_asc_at_oob_not_done v x i acc hi_ge h_size] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        exact all_odd_push_one acc x h_size h_acc h_x
      · exfalso
        have h_big : USize64.size ≤ acc.val.size + 1 := by omega
        rw [insert_asc_at_oob_not_done_fail v x i acc hi_ge h_big] at hres
        cases hres
  | succ n ih =>
    intro v x i done acc r hm hi_le hres h_v h_x h_acc
    by_cases hi_ge : v.val.size ≤ i.toNat
    · cases done with
      | true =>
        rw [insert_asc_at_oob_done v x i acc hi_ge] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'; exact h_acc
      | false =>
        by_cases h_size : acc.val.size + 1 < USize64.size
        · rw [insert_asc_at_oob_not_done v x i acc hi_ge h_size] at hres
          injection hres with h_eq
          injection h_eq with h_eq'
          subst h_eq'
          exact all_odd_push_one acc x h_size h_acc h_x
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_asc_at_oob_not_done_fail v x i acc hi_ge h_big] at hres
          cases hres
    · have hi_lt : i.toNat < v.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [usize_size_eq] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ v.val.size := by rw [h_i1]; omega
      have h_meas : v.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      -- v[i] is odd
      have h_vi_odd : (v.val[i.toNat]'hi_lt).toNat % 2 = 1 := h_v i.toNat hi_lt
      cases done with
      | true =>
        by_cases h_eq : v.val[i.toNat]'hi_lt = x
        · -- step_skip_dup: recurse with same acc
          rw [insert_asc_at_step_skip_dup v x i acc hi_lt h_eq] at hres
          exact ih v x (i + 1) true acc r h_meas h_i1_le hres h_v h_x h_acc
        · -- step_done_push: recurse with push_one acc v[i]
          by_cases h_sz : acc.val.size + 1 < USize64.size
          · rw [insert_asc_at_step_done_push v x i acc hi_lt h_eq h_sz] at hres
            have h_new_acc : all_odd_pred (push_one acc (v.val[i.toNat]'hi_lt) h_sz).val :=
              all_odd_push_one acc _ h_sz h_acc h_vi_odd
            exact ih v x (i + 1) true _ r h_meas h_i1_le hres h_v h_x h_new_acc
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 1 := by omega
            rw [insert_asc_at_step_done_push_fail v x i acc hi_lt h_eq h_big] at hres
            cases hres
      | false =>
        by_cases h_vi_lt : (v.val[i.toNat]'hi_lt).toNat < x.toNat
        · -- step_pass: recurse with push_one acc v[i], done stays false
          by_cases h_sz : acc.val.size + 1 < USize64.size
          · rw [insert_asc_at_step_pass v x i acc hi_lt h_vi_lt h_sz] at hres
            have h_new_acc : all_odd_pred (push_one acc (v.val[i.toNat]'hi_lt) h_sz).val :=
              all_odd_push_one acc _ h_sz h_acc h_vi_odd
            exact ih v x (i + 1) false _ r h_meas h_i1_le hres h_v h_x h_new_acc
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 1 := by omega
            rw [insert_asc_at_step_pass_fail v x i acc hi_lt h_vi_lt h_big] at hres
            cases hres
        · -- v[i] ≥ x
          have h_vi_ge : x.toNat ≤ (v.val[i.toNat]'hi_lt).toNat := by omega
          by_cases h_eq : v.val[i.toNat]'hi_lt = x
          · -- step_insert_dup: recurse with push_one acc x, done becomes true
            by_cases h_sz : acc.val.size + 1 < USize64.size
            · rw [insert_asc_at_step_insert_dup v x i acc hi_lt h_eq h_sz] at hres
              have h_new_acc : all_odd_pred (push_one acc x h_sz).val :=
                all_odd_push_one acc x h_sz h_acc h_x
              exact ih v x (i + 1) true _ r h_meas h_i1_le hres h_v h_x h_new_acc
            · exfalso
              have h_big : USize64.size ≤ acc.val.size + 1 := by omega
              rw [insert_asc_at_step_insert_dup_fail v x i acc hi_lt h_eq h_big] at hres
              cases hres
          · -- step_insert: v[i] > x strict, push x then v[i], done becomes true
            have h_vi_gt : x.toNat < (v.val[i.toNat]'hi_lt).toNat := by
              rcases Nat.eq_or_lt_of_le h_vi_ge with heq | hlt
              · exfalso; apply h_eq
                exact (UInt64.toNat_inj.mp heq.symm)
              · exact hlt
            by_cases h_sz : acc.val.size + 2 < USize64.size
            · rw [insert_asc_at_step_insert v x i acc hi_lt h_vi_gt h_sz] at hres
              have h_acc_x_size : acc.val.size + 1 < USize64.size := by omega
              have h_acc_vi_size : (push_one acc x h_acc_x_size).val.size + 1 < USize64.size := by
                rw [push_one_size]; omega
              have h_acc_x_all_odd : all_odd_pred (push_one acc x h_acc_x_size).val :=
                all_odd_push_one acc x h_acc_x_size h_acc h_x
              have h_acc_xvi_all_odd :
                  all_odd_pred (push_one (push_one acc x h_acc_x_size)
                    (v.val[i.toNat]'hi_lt) h_acc_vi_size).val :=
                all_odd_push_one _ _ h_acc_vi_size h_acc_x_all_odd h_vi_odd
              exact ih v x (i + 1) true _ r h_meas h_i1_le hres h_v h_x h_acc_xvi_all_odd
            · exfalso
              by_cases h_acc_x_size : acc.val.size + 1 < USize64.size
              · have h_big : USize64.size ≤ acc.val.size + 2 := by omega
                rw [insert_asc_at_step_insert_fail_vi v x i acc hi_lt h_vi_gt
                      h_acc_x_size h_big] at hres
                cases hres
              · have h_big : USize64.size ≤ acc.val.size + 1 := by omega
                rw [insert_asc_at_step_insert_fail_x v x i acc hi_lt h_vi_gt h_big] at hres
                cases hres

/-! ## Admissibility helper. -/

open Lean.Order in
/-- The motive shape `fun f => ∀ x y r, f x y = RustM.ok r → P x y r` is admissible for
    any `P`, by combining `admissible_pi`, `admissible_apply`, and
    `admissible_eq_ok_implies` (the FlatOrder bot `RustM.div` ≠ `RustM.ok r`). -/
private theorem admissible_ok_motive_2
    {α β γ : Type} (P : α → β → γ → Prop) :
    Lean.Order.admissible (fun (f : α → β → RustM γ) =>
        ∀ x y r, f x y = RustM.ok r → P x y r) := by
  apply Lean.Order.admissible_pi
  intro x
  apply Lean.Order.admissible_pi
  intro y
  apply Lean.Order.admissible_pi
  intro r
  exact Lean.Order.admissible_apply
    (fun (x' : α) (g : β → RustM γ) => g y = RustM.ok r → P x y r) x
    (Lean.Order.admissible_apply
      (fun (y' : β) (h : RustM γ) => h = RustM.ok r → P x y r) y
      (admissible_eq_ok_implies r (P x y r)))

/-- All-odd preservation by `insert_asc`. -/
private theorem insert_asc_all_odd (v : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (r : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_122_get_odd_collatz.insert_asc v x = RustM.ok r)
    (h_v_odd : all_odd_pred v.val) (h_x_odd : x.toNat % 2 = 1) :
    all_odd_pred r.val := by
  unfold clever_122_get_odd_collatz.insert_asc at hres
  have h_deref :
      (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u64 alloc.alloc.Global) v : RustM _) = RustM.ok v := rfl
  have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                RustM.ok emptyVec := rfl
  rw [h_deref, h_new] at hres
  simp only [RustM_ok_bind] at hres
  have h_zero_le : (0 : usize).toNat = 0 := rfl
  have h_meas : v.val.size - (0 : usize).toNat ≤ v.val.size := by rw [h_zero_le]; omega
  have h_le : (0 : usize).toNat ≤ v.val.size := by rw [h_zero_le]; omega
  -- v passed as slice: ⟨v.val, v.size_lt_usizeSize⟩
  exact insert_asc_at_all_odd_aux v.val.size ⟨v.val, v.size_lt_usizeSize⟩ x (0 : usize) false
    emptyVec r h_meas h_le hres h_v_odd h_x_odd emptyVec_all_odd

/-! ## Generic predicate preservation by insert_asc_at and insert_asc.

This factors out a generalization of `insert_asc_at_all_odd_aux` over an
arbitrary predicate `P : u64 → Prop`. The proof structure is identical;
only the predicate name changes. Used below for the reachability
postcondition. -/

private def all_pred (P : u64 → Prop) (arr : Array u64) : Prop :=
  ∀ (k : Nat) (h : k < arr.size), P (arr[k]'h)

private theorem all_pred_empty (P : u64 → Prop) : all_pred P (#[] : Array u64) := by
  intro k h
  exact absurd h (Nat.not_lt_zero _)

private theorem all_pred_append (P : u64 → Prop) (acc : Array u64) (y : u64)
    (h_acc : all_pred P acc) (h_y : P y) :
    all_pred P (acc ++ #[y]) := by
  intro k hk
  rw [Array.size_append] at hk
  have h_one : (#[y] : Array u64).size = 1 := rfl
  by_cases h_lt : k < acc.size
  · rw [Array.getElem_append_left h_lt]
    exact h_acc k h_lt
  · have h_ge : acc.size ≤ k := Nat.le_of_not_lt h_lt
    rw [Array.getElem_append_right h_ge]
    have h_idx : k - acc.size = 0 := by rw [h_one] at hk; omega
    have h_zero : (0 : Nat) < (#[y] : Array u64).size := by rw [h_one]; omega
    rw [show ((#[y] : Array u64)[k - acc.size]'(by rw [h_idx]; exact h_zero))
            = (#[y] : Array u64)[0]'h_zero from by simp [h_idx]]
    exact h_y

private theorem all_pred_push_one (P : u64 → Prop)
    (acc : alloc.vec.Vec u64 alloc.alloc.Global) (y : u64)
    (h : acc.val.size + 1 < USize64.size)
    (h_acc : all_pred P acc.val) (h_y : P y) :
    all_pred P (push_one acc y h).val :=
  all_pred_append P acc.val y h_acc h_y

/-- Generic predicate preservation by `insert_asc_at`. Structure mirrors
    `insert_asc_at_all_odd_aux`. -/
private theorem insert_asc_at_pred_aux (P : u64 → Prop) :
    ∀ (n : Nat) (v : RustSlice u64) (x : u64) (i : usize) (done : Bool)
      (acc r : alloc.vec.Vec u64 alloc.alloc.Global),
      v.val.size - i.toNat ≤ n →
      i.toNat ≤ v.val.size →
      clever_122_get_odd_collatz.insert_asc_at v x i done acc = RustM.ok r →
      all_pred P v.val →
      P x →
      all_pred P acc.val →
      all_pred P r.val := by
  intro n
  induction n with
  | zero =>
    intro v x i done acc r hm hi_le hres h_v h_x h_acc
    have hi_ge : v.val.size ≤ i.toNat := by omega
    cases done with
    | true =>
      rw [insert_asc_at_oob_done v x i acc hi_ge] at hres
      injection hres with h_eq
      injection h_eq with h_eq'
      subst h_eq'; exact h_acc
    | false =>
      by_cases h_size : acc.val.size + 1 < USize64.size
      · rw [insert_asc_at_oob_not_done v x i acc hi_ge h_size] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'
        exact all_pred_push_one P acc x h_size h_acc h_x
      · exfalso
        have h_big : USize64.size ≤ acc.val.size + 1 := by omega
        rw [insert_asc_at_oob_not_done_fail v x i acc hi_ge h_big] at hres
        cases hres
  | succ n ih =>
    intro v x i done acc r hm hi_le hres h_v h_x h_acc
    by_cases hi_ge : v.val.size ≤ i.toNat
    · cases done with
      | true =>
        rw [insert_asc_at_oob_done v x i acc hi_ge] at hres
        injection hres with h_eq
        injection h_eq with h_eq'
        subst h_eq'; exact h_acc
      | false =>
        by_cases h_size : acc.val.size + 1 < USize64.size
        · rw [insert_asc_at_oob_not_done v x i acc hi_ge h_size] at hres
          injection hres with h_eq
          injection h_eq with h_eq'
          subst h_eq'
          exact all_pred_push_one P acc x h_size h_acc h_x
        · exfalso
          have h_big : USize64.size ≤ acc.val.size + 1 := by omega
          rw [insert_asc_at_oob_not_done_fail v x i acc hi_ge h_big] at hres
          cases hres
    · have hi_lt : i.toNat < v.val.size := Nat.lt_of_not_le hi_ge
      have h_size_lt : v.val.size < USize64.size := v.size_lt_usizeSize
      have h_no_ov_i : i.toNat + 1 < 2^64 := by
        rw [usize_size_eq] at h_size_lt; omega
      have h_i1 : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov_i
      have h_i1_le : (i + 1).toNat ≤ v.val.size := by rw [h_i1]; omega
      have h_meas : v.val.size - (i + 1).toNat ≤ n := by rw [h_i1]; omega
      have h_vi_pred : P (v.val[i.toNat]'hi_lt) := h_v i.toNat hi_lt
      cases done with
      | true =>
        by_cases h_eq : v.val[i.toNat]'hi_lt = x
        · rw [insert_asc_at_step_skip_dup v x i acc hi_lt h_eq] at hres
          exact ih v x (i + 1) true acc r h_meas h_i1_le hres h_v h_x h_acc
        · by_cases h_sz : acc.val.size + 1 < USize64.size
          · rw [insert_asc_at_step_done_push v x i acc hi_lt h_eq h_sz] at hres
            have h_new_acc : all_pred P (push_one acc (v.val[i.toNat]'hi_lt) h_sz).val :=
              all_pred_push_one P acc _ h_sz h_acc h_vi_pred
            exact ih v x (i + 1) true _ r h_meas h_i1_le hres h_v h_x h_new_acc
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 1 := by omega
            rw [insert_asc_at_step_done_push_fail v x i acc hi_lt h_eq h_big] at hres
            cases hres
      | false =>
        by_cases h_vi_lt : (v.val[i.toNat]'hi_lt).toNat < x.toNat
        · by_cases h_sz : acc.val.size + 1 < USize64.size
          · rw [insert_asc_at_step_pass v x i acc hi_lt h_vi_lt h_sz] at hres
            have h_new_acc : all_pred P (push_one acc (v.val[i.toNat]'hi_lt) h_sz).val :=
              all_pred_push_one P acc _ h_sz h_acc h_vi_pred
            exact ih v x (i + 1) false _ r h_meas h_i1_le hres h_v h_x h_new_acc
          · exfalso
            have h_big : USize64.size ≤ acc.val.size + 1 := by omega
            rw [insert_asc_at_step_pass_fail v x i acc hi_lt h_vi_lt h_big] at hres
            cases hres
        · have h_vi_ge : x.toNat ≤ (v.val[i.toNat]'hi_lt).toNat := by omega
          by_cases h_eq : v.val[i.toNat]'hi_lt = x
          · by_cases h_sz : acc.val.size + 1 < USize64.size
            · rw [insert_asc_at_step_insert_dup v x i acc hi_lt h_eq h_sz] at hres
              have h_new_acc : all_pred P (push_one acc x h_sz).val :=
                all_pred_push_one P acc x h_sz h_acc h_x
              exact ih v x (i + 1) true _ r h_meas h_i1_le hres h_v h_x h_new_acc
            · exfalso
              have h_big : USize64.size ≤ acc.val.size + 1 := by omega
              rw [insert_asc_at_step_insert_dup_fail v x i acc hi_lt h_eq h_big] at hres
              cases hres
          · have h_vi_gt : x.toNat < (v.val[i.toNat]'hi_lt).toNat := by
              rcases Nat.eq_or_lt_of_le h_vi_ge with heq | hlt
              · exfalso; apply h_eq
                exact (UInt64.toNat_inj.mp heq.symm)
              · exact hlt
            by_cases h_sz : acc.val.size + 2 < USize64.size
            · rw [insert_asc_at_step_insert v x i acc hi_lt h_vi_gt h_sz] at hres
              have h_acc_x_size : acc.val.size + 1 < USize64.size := by omega
              have h_acc_vi_size : (push_one acc x h_acc_x_size).val.size + 1 < USize64.size := by
                rw [push_one_size]; omega
              have h_acc_x_pred : all_pred P (push_one acc x h_acc_x_size).val :=
                all_pred_push_one P acc x h_acc_x_size h_acc h_x
              have h_acc_xvi_pred :
                  all_pred P (push_one (push_one acc x h_acc_x_size)
                    (v.val[i.toNat]'hi_lt) h_acc_vi_size).val :=
                all_pred_push_one P _ _ h_acc_vi_size h_acc_x_pred h_vi_pred
              exact ih v x (i + 1) true _ r h_meas h_i1_le hres h_v h_x h_acc_xvi_pred
            · exfalso
              by_cases h_acc_x_size : acc.val.size + 1 < USize64.size
              · have h_big : USize64.size ≤ acc.val.size + 2 := by omega
                rw [insert_asc_at_step_insert_fail_vi v x i acc hi_lt h_vi_gt
                      h_acc_x_size h_big] at hres
                cases hres
              · have h_big : USize64.size ≤ acc.val.size + 1 := by omega
                rw [insert_asc_at_step_insert_fail_x v x i acc hi_lt h_vi_gt h_big] at hres
                cases hres

/-- Generic predicate preservation by `insert_asc`. -/
private theorem insert_asc_pred (P : u64 → Prop)
    (v : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (r : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_122_get_odd_collatz.insert_asc v x = RustM.ok r)
    (h_v_pred : all_pred P v.val) (h_x_pred : P x) :
    all_pred P r.val := by
  unfold clever_122_get_odd_collatz.insert_asc at hres
  have h_deref :
      (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u64 alloc.alloc.Global) v : RustM _) = RustM.ok v := rfl
  have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =
                RustM.ok emptyVec := rfl
  rw [h_deref, h_new] at hres
  simp only [RustM_ok_bind] at hres
  have h_zero_le : (0 : usize).toNat = 0 := rfl
  have h_meas : v.val.size - (0 : usize).toNat ≤ v.val.size := by rw [h_zero_le]; omega
  have h_le : (0 : usize).toNat ≤ v.val.size := by rw [h_zero_le]; omega
  exact insert_asc_at_pred_aux P v.val.size ⟨v.val, v.size_lt_usizeSize⟩ x (0 : usize) false
    emptyVec r h_meas h_le hres h_v_pred h_x_pred (all_pred_empty P)

/-! ## Collatz reachability helpers. -/

private theorem collatz_iter_succ (k n : Nat) :
    collatz_iter (k + 1) n = collatz_step (collatz_iter k n) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    show collatz_iter (k + 1) (collatz_step n) = collatz_step (collatz_iter k (collatz_step n))
    exact ih (collatz_step n)

private theorem collatz_reachable_refl (n : Nat) : collatz_reachable n n := ⟨0, rfl⟩

private theorem collatz_reachable_step_of (n x : Nat) (h : collatz_reachable n x) :
    collatz_reachable n (collatz_step x) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k + 1, ?_⟩
  rw [collatz_iter_succ, hk]

/-! ## u64 arithmetic helpers for step_at recursion targets. -/

private theorem u64_mul_three_toNat (x v : u64)
    (h : ((3 : u64) *? x : RustM u64) = RustM.ok v) :
    v.toNat = 3 * x.toNat := by
  have h_body :
      (if BitVec.umulOverflow ((3 : u64).toBitVec) x.toBitVec
       then (.fail .integerOverflow : RustM u64)
       else pure ((3 : u64) * x)) = RustM.ok v := h
  by_cases h_ov : BitVec.umulOverflow ((3 : u64).toBitVec) x.toBitVec
  · rw [if_pos h_ov] at h_body; cases h_body
  · rw [if_neg h_ov] at h_body
    have h_no_ov_iff : ¬ UInt64.mulOverflow 3 x := h_ov
    have h_no_ov : ¬ ((3 : u64).toNat * x.toNat ≥ 2 ^ 64) := by
      intro h_ge
      apply h_no_ov_iff
      exact UInt64.mulOverflow_iff.mpr h_ge
    have h_lt : (3 : u64).toNat * x.toNat < 2^64 := Nat.lt_of_not_le h_no_ov
    have h_pure : (pure ((3 : u64) * x) : RustM u64) = RustM.ok ((3 : u64) * x) := rfl
    rw [h_pure] at h_body
    injection h_body with h_eq
    injection h_eq with h_eq'
    have h_v_eq : v = (3 : u64) * x := h_eq'.symm
    rw [h_v_eq]
    have h3_toNat : (3 : u64).toNat = 3 := rfl
    rw [UInt64.toNat_mul_of_lt h_lt, h3_toNat]

private theorem u64_add_one_toNat (v vadd : u64)
    (h : (v +? (1 : u64) : RustM u64) = RustM.ok vadd) :
    vadd.toNat = v.toNat + 1 := by
  have h_body :
      (if BitVec.uaddOverflow v.toBitVec ((1 : u64).toBitVec)
       then (.fail .integerOverflow : RustM u64)
       else pure (v + (1 : u64))) = RustM.ok vadd := h
  by_cases h_ov : BitVec.uaddOverflow v.toBitVec ((1 : u64).toBitVec)
  · rw [if_pos h_ov] at h_body; cases h_body
  · rw [if_neg h_ov] at h_body
    have h_no_ov_iff : ¬ UInt64.addOverflow v 1 := h_ov
    have h_no_ov : ¬ (v.toNat + (1 : u64).toNat ≥ 2 ^ 64) := by
      intro h_ge
      apply h_no_ov_iff
      exact UInt64.addOverflow_iff.mpr h_ge
    have h_lt : v.toNat + (1 : u64).toNat < 2^64 := Nat.lt_of_not_le h_no_ov
    have h_pure : (pure (v + (1 : u64)) : RustM u64) = RustM.ok (v + (1 : u64)) := rfl
    rw [h_pure] at h_body
    injection h_body with h_eq
    injection h_eq with h_eq'
    have h_vadd_eq : vadd = v + (1 : u64) := h_eq'.symm
    rw [h_vadd_eq]
    have h1_toNat : (1 : u64).toNat = 1 := rfl
    rw [UInt64.toNat_add_of_lt h_lt, h1_toNat]

private theorem u64_div_two_toNat (x v : u64)
    (h : (x /? (2 : u64) : RustM u64) = RustM.ok v) :
    v.toNat = x.toNat / 2 := by
  have h_body :
      (if (2 : u64) = 0 then (.fail .divisionByZero : RustM u64)
       else pure (x / (2 : u64))) = RustM.ok v := h
  rw [if_neg (by decide)] at h_body
  have h_pure : (pure (x / (2 : u64)) : RustM u64) = RustM.ok (x / (2 : u64)) := rfl
  rw [h_pure] at h_body
  injection h_body with h_eq
  injection h_eq with h_eq'
  have h_v_eq : v = x / (2 : u64) := h_eq'.symm
  rw [h_v_eq]
  have h2_toNat : (2 : u64).toNat = 2 := rfl
  rw [show ((x / (2 : u64)).toNat = x.toNat / (2 : u64).toNat) from UInt64.toNat_div x 2,
      h2_toNat]

private theorem u64_mod_two_toNat (x : u64) :
    (x % (2 : u64)).toNat = x.toNat % 2 := by
  rw [UInt64.toNat_mod]; rfl

private theorem u64_x_mod_2_eq_one_iff_odd (x : u64) :
    (x % 2 : u64) = (1 : u64) ↔ x.toNat % 2 = 1 := by
  constructor
  · intro h
    have h2 : (x % 2 : u64).toNat = (1 : u64).toNat := by rw [h]
    rw [u64_mod_two_toNat] at h2
    exact h2
  · intro h
    have h2 : (x % 2 : u64).toNat = (1 : u64).toNat := by
      rw [u64_mod_two_toNat]; exact h
    have : x.toNat % 2 < 2 := by omega
    have h2' : (x % 2 : u64).toNat < 2 := by
      rw [u64_mod_two_toNat]; exact this
    exact UInt64.toNat_inj.mp h2

/-! ## step_at reachability invariant via fixpoint induction. -/

set_option maxHeartbeats 4000000 in
private theorem step_at_reach_motive (n : Nat) :
    ∀ (x : u64) (acc r : alloc.vec.Vec u64 alloc.alloc.Global),
      clever_122_get_odd_collatz.step_at x acc = RustM.ok r →
      collatz_reachable n x.toNat →
      all_pred (fun y => collatz_reachable n y.toNat) acc.val →
      all_pred (fun y => collatz_reachable n y.toNat) r.val := by
  -- We use admissible_ok_motive_2 with the property
  -- P x acc r := reachable n x → all_pred (reachable n) acc → all_pred (reachable n) r
  have h_adm := admissible_ok_motive_2
    (P := fun (x : u64) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
           (r : alloc.vec.Vec u64 alloc.alloc.Global) =>
        collatz_reachable n x.toNat →
        all_pred (fun y => collatz_reachable n y.toNat) acc.val →
        all_pred (fun y => collatz_reachable n y.toNat) r.val)
  apply clever_122_get_odd_collatz.step_at.fixpoint_induct
    (fun f => ∀ x acc r, f x acc = RustM.ok r →
        collatz_reachable n x.toNat →
        all_pred (fun y => collatz_reachable n y.toNat) acc.val →
        all_pred (fun y => collatz_reachable n y.toNat) r.val)
    h_adm
  intro step_at_f h_ih x acc r hres h_x_reach h_acc
  dsimp only at hres
  by_cases hx_eq_1 : x = 1
  · subst hx_eq_1
    have h_eq_test : ((1 : u64) ==? (1 : u64) : RustM Bool) = RustM.ok true := by
      show pure ((1 : u64) == (1 : u64) : Bool) = RustM.ok true; rfl
    rw [h_eq_test] at hres
    simp only [RustM_ok_bind, ↓reduceIte] at hres
    have h_deref :
        (core_models.ops.deref.Deref.deref
          (alloc.vec.Vec u64 alloc.alloc.Global) acc : RustM _) = RustM.ok acc := rfl
    rw [h_deref] at hres
    simp only [RustM_ok_bind] at hres
    generalize h_vc : clever_122_get_odd_collatz.vec_contains
      ⟨acc.val, acc.size_lt_usizeSize⟩ (1 : u64) (0 : usize) = vc_res at hres
    cases vc_res with
    | none => cases hres
    | some vc_inner =>
      cases vc_inner with
      | error _ => cases hres
      | ok vc_bool =>
        simp only [RustM_ok_bind] at hres
        cases vc_bool with
        | true =>
          simp only [rust_primitives.hax.logical_op.not, Bool.not_true,
                     RustM_ok_bind, Bool.false_eq_true, ↓reduceIte] at hres
          injection hres with h_eq
          injection h_eq with h_eq'
          subst h_eq'; exact h_acc
        | false =>
          simp only [rust_primitives.hax.logical_op.not, Bool.not_false,
                     RustM_ok_bind, ↓reduceIte] at hres
          exact insert_asc_pred _ acc 1 r hres h_acc h_x_reach
  · have h_eq_test : (x ==? (1 : u64) : RustM Bool) = RustM.ok false := by
      show pure (x == (1 : u64) : Bool) = RustM.ok false
      have : (x == (1 : u64)) = false := by
        rw [beq_eq_false_iff_ne]; exact hx_eq_1
      rw [this]; rfl
    rw [h_eq_test] at hres
    simp only [RustM_ok_bind, Bool.false_eq_true, ↓reduceIte] at hres
    have h_x_mod : (x %? (2 : u64) : RustM u64) = RustM.ok (x % 2) := by
      show (rust_primitives.ops.arith.Rem.rem x 2 : RustM u64) = _
      show (if (2 : u64) = 0 then (.fail .divisionByZero : RustM u64) else pure (x % 2)) = _
      rw [if_neg (by decide)]; rfl
    rw [h_x_mod] at hres
    simp only [RustM_ok_bind] at hres
    by_cases h_odd : (x % 2 : u64) = (1 : u64)
    · have h_eq_test_2 : ((x % 2 : u64) ==? (1 : u64) : RustM Bool) = RustM.ok true := by
        show pure ((x % 2 : u64) == (1 : u64) : Bool) = RustM.ok true
        have : ((x % 2 : u64) == (1 : u64)) = true := by
          rw [beq_iff_eq]; exact h_odd
        rw [this]; rfl
      rw [h_eq_test_2] at hres
      simp only [RustM_ok_bind, ↓reduceIte] at hres
      have h_deref :
          (core_models.ops.deref.Deref.deref
            (alloc.vec.Vec u64 alloc.alloc.Global) acc : RustM _) = RustM.ok acc := rfl
      rw [h_deref] at hres
      simp only [RustM_ok_bind] at hres
      -- x is odd at Nat level
      have h_x_odd_nat : x.toNat % 2 = 1 := (u64_x_mod_2_eq_one_iff_odd x).mp h_odd
      -- step from x: x is odd, so collatz_step x.toNat = 3*x.toNat + 1
      have h_step : collatz_step x.toNat = 3 * x.toNat + 1 := by
        show (if x.toNat % 2 = 0 then x.toNat / 2 else 3 * x.toNat + 1) = _
        rw [if_neg (by omega)]
      generalize h_vc : clever_122_get_odd_collatz.vec_contains
        ⟨acc.val, acc.size_lt_usizeSize⟩ x (0 : usize) = vc_res at hres
      cases vc_res with
      | none => cases hres
      | some vc_inner =>
        cases vc_inner with
        | error _ => cases hres
        | ok vc_bool =>
          simp only [RustM_ok_bind] at hres
          cases vc_bool with
          | true =>
            simp only [↓reduceIte, RustM_ok_bind] at hres
            generalize h_3x : ((3 : u64) *? x : RustM u64) = res3x at hres
            cases res3x with
            | none => cases hres
            | some inner3x =>
              cases inner3x with
              | error _ => cases hres
              | ok val3x =>
                have h_val3x : ((3 : u64) *? x : RustM u64) = RustM.ok val3x := h_3x
                have h_val3x_eq : val3x.toNat = 3 * x.toNat :=
                  u64_mul_three_toNat x val3x h_val3x
                simp only [RustM_ok_bind] at hres
                generalize h_add : (val3x +? (1 : u64) : RustM u64) = resadd at hres
                cases resadd with
                | none => cases hres
                | some inneradd =>
                  cases inneradd with
                  | error _ => cases hres
                  | ok valadd =>
                    have h_valadd : (val3x +? (1 : u64) : RustM u64) = RustM.ok valadd := h_add
                    have h_valadd_eq : valadd.toNat = val3x.toNat + 1 :=
                      u64_add_one_toNat val3x valadd h_valadd
                    simp only [RustM_ok_bind] at hres
                    have h_valadd_nat : valadd.toNat = 3 * x.toNat + 1 := by
                      rw [h_valadd_eq, h_val3x_eq]
                    have h_valadd_reach : collatz_reachable n valadd.toNat := by
                      rw [h_valadd_nat, ← h_step]
                      exact collatz_reachable_step_of n x.toNat h_x_reach
                    exact h_ih valadd acc r hres h_valadd_reach h_acc
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, RustM_ok_bind] at hres
            generalize h_ins : clever_122_get_odd_collatz.insert_asc acc x = ins_res at hres
            cases ins_res with
            | none => cases hres
            | some ins_inner =>
              cases ins_inner with
              | error _ => cases hres
              | ok next =>
                have h_ins_ok :
                    clever_122_get_odd_collatz.insert_asc acc x = RustM.ok next := h_ins
                simp only [RustM_ok_bind] at hres
                have h_next_reach :
                    all_pred (fun y => collatz_reachable n y.toNat) next.val :=
                  insert_asc_pred _ acc x next h_ins_ok h_acc h_x_reach
                generalize h_3x : ((3 : u64) *? x : RustM u64) = res3x at hres
                cases res3x with
                | none => cases hres
                | some inner3x =>
                  cases inner3x with
                  | error _ => cases hres
                  | ok val3x =>
                    have h_val3x : ((3 : u64) *? x : RustM u64) = RustM.ok val3x := h_3x
                    have h_val3x_eq : val3x.toNat = 3 * x.toNat :=
                      u64_mul_three_toNat x val3x h_val3x
                    simp only [RustM_ok_bind] at hres
                    generalize h_add : (val3x +? (1 : u64) : RustM u64) = resadd at hres
                    cases resadd with
                    | none => cases hres
                    | some inneradd =>
                      cases inneradd with
                      | error _ => cases hres
                      | ok valadd =>
                        have h_valadd : (val3x +? (1 : u64) : RustM u64) = RustM.ok valadd :=
                          h_add
                        have h_valadd_eq : valadd.toNat = val3x.toNat + 1 :=
                          u64_add_one_toNat val3x valadd h_valadd
                        simp only [RustM_ok_bind] at hres
                        have h_valadd_nat : valadd.toNat = 3 * x.toNat + 1 := by
                          rw [h_valadd_eq, h_val3x_eq]
                        have h_valadd_reach : collatz_reachable n valadd.toNat := by
                          rw [h_valadd_nat, ← h_step]
                          exact collatz_reachable_step_of n x.toNat h_x_reach
                        exact h_ih valadd next r hres h_valadd_reach h_next_reach
    · have h_eq_test_2 : ((x % 2 : u64) ==? (1 : u64) : RustM Bool) = RustM.ok false := by
        show pure ((x % 2 : u64) == (1 : u64) : Bool) = RustM.ok false
        have : ((x % 2 : u64) == (1 : u64)) = false := by
          rw [beq_eq_false_iff_ne]; exact h_odd
        rw [this]; rfl
      rw [h_eq_test_2] at hres
      simp only [RustM_ok_bind, Bool.false_eq_true, ↓reduceIte] at hres
      generalize h_xdiv : (x /? (2 : u64) : RustM u64) = res_div at hres
      cases res_div with
      | none => cases hres
      | some inner_div =>
        cases inner_div with
        | error _ => cases hres
        | ok val_div =>
          have h_val_div : (x /? (2 : u64) : RustM u64) = RustM.ok val_div := h_xdiv
          have h_val_div_eq : val_div.toNat = x.toNat / 2 :=
            u64_div_two_toNat x val_div h_val_div
          simp only [RustM_ok_bind] at hres
          -- x is even since x % 2 ≠ 1 and x % 2 < 2
          have h_x_even_nat : x.toNat % 2 = 0 := by
            have h_lt : x.toNat % 2 < 2 := Nat.mod_lt _ (by omega)
            have h_ne_one : x.toNat % 2 ≠ 1 := by
              intro h_eq1
              apply h_odd
              exact (u64_x_mod_2_eq_one_iff_odd x).mpr h_eq1
            omega
          have h_step : collatz_step x.toNat = x.toNat / 2 := by
            show (if x.toNat % 2 = 0 then x.toNat / 2 else 3 * x.toNat + 1) = _
            rw [if_pos h_x_even_nat]
          have h_val_div_reach : collatz_reachable n val_div.toNat := by
            rw [h_val_div_eq, ← h_step]
            exact collatz_reachable_step_of n x.toNat h_x_reach
          exact h_ih val_div acc r hres h_val_div_reach h_acc

/-! ## Universal contract clauses (proptests).

The three proptests phrase universal claims over `n in 1u64..=10_000`.
Because `step_at` is `partial_fixpoint`, total universal claims (over
all `u64`) cannot be proven without resolving Collatz: for any `n` whose
orbit fails to reach `1`, the function may not return `RustM.ok` at
all. We thread the implicit "the function returns ok" hypothesis
through every universal clause via `hres : ... = RustM.ok v`, which is
the natural and strongest honest postcondition shape.

(Note: for the proptest range `n.toNat ≤ 10_000`, the orbit is known
to terminate within `u64`; `hres` is then discharged. The proof stage
may add this bound where convenient.) -/

/-- Postcondition (from the proptest `prop_sorted_strictly_ascending`):
    whenever `get_odd_collatz n` succeeds, the result is strictly
    ascending. Captures both sortedness and uniqueness in one check —
    if either failed, the proptest would too.

    I, the proof generation agent with full access to the references,
    Hax prelude, local helper-lemma facility and Lean LSP, tried this
    proof and could not finish it within the available effort budget;
    the structural invariant required (acc remains strict_asc and
    bounded by `min(x, v[i])` through each step of `insert_asc_at`)
    needs a separate, similarly-sized strong-induction proof for
    insert_asc_at and another for step_at — a separately-verified
    `insert_asc_preserves_strict_asc` private theorem would unblock the
    step_at fixpoint induction. The remaining `sorry` is structural,
    not a missing piece of automation. -/
theorem get_odd_collatz_strict_asc (n : u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_122_get_odd_collatz.get_odd_collatz n = RustM.ok v) :
    strict_asc v.val := by
  sorry

/-! ## step_at all-odd invariant via fixpoint induction. -/

private theorem u64_eq_zero_test (n : u64) :
    (n ==? (0 : u64) : RustM Bool) = RustM.ok (decide (n = 0)) := by
  show (rust_primitives.cmp.eq n (0 : u64) : RustM Bool) = _
  show pure (n == (0 : u64) : Bool) = _
  rw [show (n == (0 : u64) : Bool) = decide (n = 0) from by
    by_cases h : n = 0
    · rw [h]; decide
    · simp [h]]
  rfl

set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 4000 in
private theorem step_at_all_odd_motive :
    ∀ (x : u64) (acc r : alloc.vec.Vec u64 alloc.alloc.Global),
      clever_122_get_odd_collatz.step_at x acc = RustM.ok r →
      all_odd_pred acc.val →
      all_odd_pred r.val := by
  have h_adm := admissible_ok_motive_2
    (P := fun (_ : u64) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
           (r : alloc.vec.Vec u64 alloc.alloc.Global) =>
        all_odd_pred acc.val → all_odd_pred r.val)
  apply clever_122_get_odd_collatz.step_at.fixpoint_induct
    (fun f => ∀ x acc r, f x acc = RustM.ok r → all_odd_pred acc.val → all_odd_pred r.val)
    h_adm
  intro step_at_f h_ih x acc r hres h_acc
  -- Beta-reduce the lambda body so subsequent rewrites can match.
  dsimp only at hres
  -- Cases on x.
  by_cases hx_eq_1 : x = 1
  · -- x = 1 branch.
    subst hx_eq_1
    have h_eq_test : ((1 : u64) ==? (1 : u64) : RustM Bool) = RustM.ok true := by
      show pure ((1 : u64) == (1 : u64) : Bool) = RustM.ok true; rfl
    rw [h_eq_test] at hres
    simp only [RustM_ok_bind, ↓reduceIte] at hres
    have h_deref :
        (core_models.ops.deref.Deref.deref
          (alloc.vec.Vec u64 alloc.alloc.Global) acc : RustM _) = RustM.ok acc := rfl
    rw [h_deref] at hres
    simp only [RustM_ok_bind] at hres
    generalize h_vc : clever_122_get_odd_collatz.vec_contains
      ⟨acc.val, acc.size_lt_usizeSize⟩ (1 : u64) (0 : usize) = vc_res at hres
    cases vc_res with
    | none => cases hres
    | some vc_inner =>
      cases vc_inner with
      | error _ => cases hres
      | ok vc_bool =>
        simp only [RustM_ok_bind] at hres
        cases vc_bool with
        | true =>
          simp only [rust_primitives.hax.logical_op.not, Bool.not_true,
                     RustM_ok_bind, Bool.false_eq_true, ↓reduceIte] at hres
          injection hres with h_eq
          injection h_eq with h_eq'
          subst h_eq'; exact h_acc
        | false =>
          simp only [rust_primitives.hax.logical_op.not, Bool.not_false,
                     RustM_ok_bind, ↓reduceIte] at hres
          have h_one_odd : (1 : u64).toNat % 2 = 1 := by decide
          exact insert_asc_all_odd acc 1 r hres h_acc h_one_odd
  · -- x ≠ 1 branch
    have h_eq_test : (x ==? (1 : u64) : RustM Bool) = RustM.ok false := by
      show pure (x == (1 : u64) : Bool) = RustM.ok false
      have : (x == (1 : u64)) = false := by
        rw [beq_eq_false_iff_ne]; exact hx_eq_1
      rw [this]; rfl
    rw [h_eq_test] at hres
    simp only [RustM_ok_bind, Bool.false_eq_true, ↓reduceIte] at hres
    have h_x_mod : (x %? (2 : u64) : RustM u64) = RustM.ok (x % 2) := by
      show (rust_primitives.ops.arith.Rem.rem x 2 : RustM u64) = _
      show (if (2 : u64) = 0 then (.fail .divisionByZero : RustM u64) else pure (x % 2)) = _
      rw [if_neg (by decide)]; rfl
    rw [h_x_mod] at hres
    simp only [RustM_ok_bind] at hres
    by_cases h_odd : (x % 2 : u64) = (1 : u64)
    · -- odd case
      have h_eq_test_2 : ((x % 2 : u64) ==? (1 : u64) : RustM Bool) = RustM.ok true := by
        show pure ((x % 2 : u64) == (1 : u64) : Bool) = RustM.ok true
        have : ((x % 2 : u64) == (1 : u64)) = true := by
          rw [beq_iff_eq]; exact h_odd
        rw [this]; rfl
      rw [h_eq_test_2] at hres
      simp only [RustM_ok_bind, ↓reduceIte] at hres
      have h_deref :
          (core_models.ops.deref.Deref.deref
            (alloc.vec.Vec u64 alloc.alloc.Global) acc : RustM _) = RustM.ok acc := rfl
      rw [h_deref] at hres
      simp only [RustM_ok_bind] at hres
      have h_x_odd : x.toNat % 2 = 1 := by
        have h2_toNat : (2 : u64).toNat = 2 := rfl
        have h1_toNat : (1 : u64).toNat = 1 := rfl
        have h_modN : (x % 2 : u64).toNat = x.toNat % 2 := by
          rw [UInt64.toNat_mod, h2_toNat]
        have : (x % 2 : u64).toNat = (1 : u64).toNat := by rw [h_odd]
        rw [h_modN, h1_toNat] at this; exact this
      generalize h_vc : clever_122_get_odd_collatz.vec_contains
        ⟨acc.val, acc.size_lt_usizeSize⟩ x (0 : usize) = vc_res at hres
      cases vc_res with
      | none => cases hres
      | some vc_inner =>
        cases vc_inner with
        | error _ => cases hres
        | ok vc_bool =>
          simp only [RustM_ok_bind] at hres
          cases vc_bool with
          | true =>
            simp only [↓reduceIte, RustM_ok_bind] at hres
            generalize h_3x : ((3 : u64) *? x : RustM u64) = res3x at hres
            cases res3x with
            | none => cases hres
            | some inner3x =>
              cases inner3x with
              | error _ => cases hres
              | ok val3x =>
                simp only [RustM_ok_bind] at hres
                generalize h_add : (val3x +? (1 : u64) : RustM u64) = resadd at hres
                cases resadd with
                | none => cases hres
                | some inneradd =>
                  cases inneradd with
                  | error _ => cases hres
                  | ok valadd =>
                    simp only [RustM_ok_bind] at hres
                    exact h_ih valadd acc r hres h_acc
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, RustM_ok_bind] at hres
            generalize h_ins : clever_122_get_odd_collatz.insert_asc acc x = ins_res at hres
            cases ins_res with
            | none => cases hres
            | some ins_inner =>
              cases ins_inner with
              | error _ => cases hres
              | ok next =>
                have h_ins_ok :
                    clever_122_get_odd_collatz.insert_asc acc x = RustM.ok next := h_ins
                simp only [RustM_ok_bind] at hres
                have h_next_all_odd : all_odd_pred next.val :=
                  insert_asc_all_odd acc x next h_ins_ok h_acc h_x_odd
                generalize h_3x : ((3 : u64) *? x : RustM u64) = res3x at hres
                cases res3x with
                | none => cases hres
                | some inner3x =>
                  cases inner3x with
                  | error _ => cases hres
                  | ok val3x =>
                    simp only [RustM_ok_bind] at hres
                    generalize h_add : (val3x +? (1 : u64) : RustM u64) = resadd at hres
                    cases resadd with
                    | none => cases hres
                    | some inneradd =>
                      cases inneradd with
                      | error _ => cases hres
                      | ok valadd =>
                        simp only [RustM_ok_bind] at hres
                        exact h_ih valadd next r hres h_next_all_odd
    · -- even case
      have h_eq_test_2 : ((x % 2 : u64) ==? (1 : u64) : RustM Bool) = RustM.ok false := by
        show pure ((x % 2 : u64) == (1 : u64) : Bool) = RustM.ok false
        have : ((x % 2 : u64) == (1 : u64)) = false := by
          rw [beq_eq_false_iff_ne]; exact h_odd
        rw [this]; rfl
      rw [h_eq_test_2] at hres
      simp only [RustM_ok_bind, Bool.false_eq_true, ↓reduceIte] at hres
      generalize h_xdiv : (x /? (2 : u64) : RustM u64) = res_div at hres
      cases res_div with
      | none => cases hres
      | some inner_div =>
        cases inner_div with
        | error _ => cases hres
        | ok val_div =>
          simp only [RustM_ok_bind] at hres
          exact h_ih val_div acc r hres h_acc

/-- Postcondition (from the proptest `prop_all_elements_odd`):
    whenever `get_odd_collatz n` succeeds, every element of the output
    is odd. -/
theorem get_odd_collatz_all_odd (n : u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_122_get_odd_collatz.get_odd_collatz n = RustM.ok v)
    (k : Nat) (hk : k < v.val.size) :
    (v.val[k]'hk).toNat % 2 = 1 := by
  unfold clever_122_get_odd_collatz.get_odd_collatz at hres
  rw [u64_eq_zero_test] at hres
  by_cases hn_zero : n = 0
  · rw [hn_zero] at hres
    have h_dec : decide ((0 : u64) = 0) = true := decide_eq_true rfl
    simp only [RustM_ok_bind, h_dec, ↓reduceIte] at hres
    have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                    RustM (alloc.vec.Vec u64 alloc.alloc.Global)) = RustM.ok emptyVec := rfl
    rw [h_new] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    have : k < 0 := hk
    exact absurd this (Nat.not_lt_zero _)
  · have h_dec : decide (n = 0) = false := decide_eq_false hn_zero
    simp only [RustM_ok_bind, h_dec, Bool.false_eq_true, ↓reduceIte] at hres
    have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                    RustM (alloc.vec.Vec u64 alloc.alloc.Global)) = RustM.ok emptyVec := rfl
    rw [h_new] at hres
    simp only [RustM_ok_bind] at hres
    have h_step := step_at_all_odd_motive n emptyVec v hres emptyVec_all_odd
    exact h_step k hk

/-- Postcondition (from the proptest `prop_matches_reference`, soundness
    half): every output element is Collatz-reachable from `n.toNat`.
    Combined with `get_odd_collatz_all_odd`, this means every output
    element is an odd value lying on the orbit of `n`. -/
theorem get_odd_collatz_output_reachable (n : u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_122_get_odd_collatz.get_odd_collatz n = RustM.ok v)
    (k : Nat) (hk : k < v.val.size) :
    collatz_reachable n.toNat (v.val[k]'hk).toNat := by
  unfold clever_122_get_odd_collatz.get_odd_collatz at hres
  rw [u64_eq_zero_test] at hres
  by_cases hn_zero : n = 0
  · rw [hn_zero] at hres
    have h_dec : decide ((0 : u64) = 0) = true := decide_eq_true rfl
    simp only [RustM_ok_bind, h_dec, ↓reduceIte] at hres
    have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                    RustM (alloc.vec.Vec u64 alloc.alloc.Global)) = RustM.ok emptyVec := rfl
    rw [h_new] at hres
    injection hres with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    have : k < 0 := hk
    exact absurd this (Nat.not_lt_zero _)
  · have h_dec : decide (n = 0) = false := decide_eq_false hn_zero
    simp only [RustM_ok_bind, h_dec, Bool.false_eq_true, ↓reduceIte] at hres
    have h_new : (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk :
                    RustM (alloc.vec.Vec u64 alloc.alloc.Global)) = RustM.ok emptyVec := rfl
    rw [h_new] at hres
    simp only [RustM_ok_bind] at hres
    have h_x_reach : collatz_reachable n.toNat n.toNat := collatz_reachable_refl _
    have h_empty_reach :
        all_pred (fun y => collatz_reachable n.toNat y.toNat) emptyVec.val := by
      intro k h
      have h_size : emptyVec.val.size = 0 := rfl
      rw [h_size] at h
      exact absurd h (Nat.not_lt_zero _)
    have h_step :=
      step_at_reach_motive n.toNat n emptyVec v hres h_x_reach h_empty_reach
    exact h_step k hk

/-- Postcondition (from the proptest `prop_matches_reference`,
    completeness half): every odd value `w < 2^64` that is
    Collatz-reachable from `n.toNat` appears as some output element.

    Bound `w < 2^64` is required so that `w` can be stored in a `u64`
    cell of the output. -/
theorem get_odd_collatz_reachable_odd_in_output (n : u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_122_get_odd_collatz.get_odd_collatz n = RustM.ok v)
    (w : Nat) (hreach : collatz_reachable n.toNat w)
    (hodd : w % 2 = 1) (hwlt : w < 2 ^ 64) :
    ∃ k : Nat, ∃ (hk : k < v.val.size), (v.val[k]'hk).toNat = w := by
  sorry

end Clever_122_get_odd_collatzObligations
