-- Companion obligations file for the `clever_033_unique` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_033_unique

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_033_uniqueObligations

/-! ## Standard scaffolding (transferred from `clever_025_remove_duplicates`,
     `clever_021_rescale_to_unit`, `clever_009_rolling_max`, `clever_003_below_zero`). -/

/-- `RustM.ok x >>= f = f x`. The library's `pure_bind` simp lemma only
    matches literal `Pure.pure`; this rewrite handles the `RustM.ok` form
    produced after reducing definitions. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

private theorem usize_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide

private theorem one_lt_usize_size : (1 : Nat) < USize64.size := by decide

private theorem two_lt_usize_size : (2 : Nat) < USize64.size := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

/-! ## OOB step lemmas for the four recursive helpers.

Each helper's body has the same out-of-bounds shape: `if i ≥ length then
pure acc` (or, for `insert_sorted_at` with `!inserted`, append then return).
These lemmas package the `unfold + simp` boilerplate so subsequent
inductions can rewrite the goal directly.

The pattern is transferred verbatim from `clever_025_remove_duplicates`'s
`build_at_oob` and `count_at_oob`. -/

private theorem sort_at_oob
    (l : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : l.val.size ≤ i.toNat) :
    clever_033_unique.sort_at l i acc = RustM.ok acc := by
  conv => lhs; unfold clever_033_unique.sort_at
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

private theorem dedupe_at_oob
    (sorted : RustSlice i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : sorted.val.size ≤ i.toNat) :
    clever_033_unique.dedupe_at sorted i acc = RustM.ok acc := by
  conv => lhs; unfold clever_033_unique.dedupe_at
  have h_ofNat : (USize64.ofNat sorted.val.size).toNat = sorted.val.size :=
    USize64.toNat_ofNat_of_lt' sorted.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat sorted.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- `insert_sorted_at` at OOB with `inserted = true` returns `acc` unchanged. -/
private theorem insert_sorted_at_oob_inserted
    (v : RustSlice i64) (x : i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat) :
    clever_033_unique.insert_sorted_at v x i true acc = RustM.ok acc := by
  conv => lhs; unfold clever_033_unique.insert_sorted_at
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat v.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  -- After the outer `if`, branch on `!inserted` which is false.
  show (do
    if (← (!? true)) then do
      let acc : alloc.vec.Vec i64 alloc.alloc.Global := acc
      let chunk : (RustArray i64 1) := (RustArray.ofVec #v[x])
      let acc : alloc.vec.Vec i64 alloc.alloc.Global ←
        (alloc.vec.Impl_2.extend_from_slice i64 alloc.alloc.Global
          acc (← (rust_primitives.unsize chunk)))
      pure acc
    else do
      pure acc) = RustM.ok acc
  rfl

/-! ## Empty-input base case.

Captures the unit test `empty_input_yields_empty_output`: on an empty
slice, `unique` succeeds and returns an empty `Vec`. The proof unfolds
`unique` (which makes two top-level `Impl.new` + recursive-helper calls),
then closes both helper applications via `sort_at_oob` and `dedupe_at_oob`
at `i = 0` (since `0 ≥ 0 = l.val.size`). -/
theorem empty_input_yields_empty_output
    (l : RustSlice i64)
    (hempty : l.val.size = 0) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_033_unique.unique l = RustM.ok v ∧ v.val.size = 0 := by
  let empty_vec : alloc.vec.Vec i64 alloc.alloc.Global :=
    ⟨(List.nil : List i64).toArray, by grind⟩
  refine ⟨empty_vec, ?_, rfl⟩
  unfold clever_033_unique.unique
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok empty_vec := rfl
  rw [h_new]
  simp only [RustM_ok_bind]
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_sort_oob :
      clever_033_unique.sort_at l (0 : usize) empty_vec
        = RustM.ok empty_vec := by
    apply sort_at_oob
    rw [h_zero_toNat]; omega
  rw [h_sort_oob]
  simp only [RustM_ok_bind]
  -- `Deref.deref` on a `Vec` is `pure self`.
  have h_deref :
      (core_models.ops.deref.Deref.deref
          (alloc.vec.Vec i64 alloc.alloc.Global) empty_vec :
            RustM (RustSlice i64)) = RustM.ok empty_vec := rfl
  rw [h_deref]
  simp only [RustM_ok_bind]
  rw [h_new]
  simp only [RustM_ok_bind]
  -- Now apply `dedupe_at_oob` at i = 0 on the empty slice (empty_vec viewed as slice).
  apply dedupe_at_oob
  rw [h_zero_toNat]
  show empty_vec.val.size ≤ 0
  show (List.nil : List i64).toArray.size ≤ 0
  simp

/-! ## Scaffolding for the remaining three obligations.

The remaining contracts (strict monotonicity, completeness, soundness)
each require deep correctness statements about `sort_at` and `dedupe_at`
that decompose roughly as follows:

* `sort_at_correct`: starting from an empty accumulator, `sort_at l 0 []`
  succeeds with a `Vec` that is (a) weakly sorted in `Int` order and (b)
  has the same multiset of elements as `l`. Proof would proceed by strong
  induction on `l.val.size − i.toNat` with an invariant relating the
  accumulator to `l[0..i]`, dispatching on the inner `insert_sorted`
  result.

* `insert_sorted_correct`: starting from a weakly-sorted `Vec`,
  `insert_sorted vec x` returns a weakly-sorted `Vec` whose multiset is
  `multiset(vec) ∪ {x}`. Inner proof: induction on `vec.val.size − i.toNat`
  inside `insert_sorted_at`, three-way case split on `inserted` and
  `v[i] ≥ x`.

* `dedupe_at_correct`: starting from a weakly-sorted slice, `dedupe_at
  sorted 0 []` returns a strictly-increasing `Vec` whose distinct-element
  set equals the set of elements of `sorted`.

Composing these gives the three contract clauses.

The two-chunk `extend_from_slice` step (the `[x, v[i]]` branch in
`insert_sorted_at`) is *not* covered by any existing reference example;
all current archetypes append exactly one element per step. This is the
single largest missing piece in the proof-pattern library — see the
selector's "gaps in the library" remarks. -/

/-- `push_one`: extending a `Vec` by a single-element chunk. Transferred
    from `clever_025_remove_duplicates` / `clever_021_rescale_to_unit`. -/
private def push_one (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x : i64)
    (h : acc.val.size + 1 < USize64.size) :
    alloc.vec.Vec i64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x], by
    have h_size : (acc.val ++ #[x]).size = acc.val.size + 1 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

/-- `push_two`: extending a `Vec` by a two-element chunk. The
    `insert_sorted_at` body's "insert here" branch appends `[x, v[i]]`. -/
private def push_two (acc : alloc.vec.Vec i64 alloc.alloc.Global) (x y : i64)
    (h : acc.val.size + 2 < USize64.size) :
    alloc.vec.Vec i64 alloc.alloc.Global :=
  ⟨acc.val ++ #[x, y], by
    have h_size : (acc.val ++ #[x, y]).size = acc.val.size + 2 := by
      rw [Array.size_append]; rfl
    rw [h_size]; exact h⟩

/-- Predicate: `Vec` is weakly increasing in signed-`Int` order. Used by
    the `sort_at`/`insert_sorted` correctness lemmas. -/
private def IsWeaklyIncreasing (v : alloc.vec.Vec i64 alloc.alloc.Global) : Prop :=
  ∀ (i j : Nat) (hi : i < v.val.size) (hj : j < v.val.size),
    i < j → (v.val[i]'hi).toInt ≤ (v.val[j]'hj).toInt

/-- Predicate: `Vec` is strictly increasing in signed-`Int` order. The
    target of `dedupe_at` on a weakly-sorted input. -/
private def IsStrictlyIncreasing (v : alloc.vec.Vec i64 alloc.alloc.Global) : Prop :=
  ∀ (i j : Nat) (hi : i < v.val.size) (hj : j < v.val.size),
    i < j → (v.val[i]'hi).toInt < (v.val[j]'hj).toInt

/-- Predicate: `v` (output) is contained as a multiset/set in `l` (input).
    "Every output index has a matching input index of the same value." -/
private def OutputSubsetInput
    (l : RustSlice i64) (v : alloc.vec.Vec i64 alloc.alloc.Global) : Prop :=
  ∀ (k : Nat) (hk : k < v.val.size),
    ∃ (i : Nat) (hi : i < l.val.size), l.val[i]'hi = v.val[k]'hk

/-- Predicate: every element of `l` (input) appears in `v` (output). -/
private def InputSubsetOutput
    (l : RustSlice i64) (v : alloc.vec.Vec i64 alloc.alloc.Global) : Prop :=
  ∀ (i : Nat) (hi : i < l.val.size),
    ∃ (k : Nat) (hk : k < v.val.size), v.val[k]'hk = l.val[i]'hi

/-! ## Top-level correctness contract for `sort_at` and `dedupe_at`.

These are stated as the *exact* helper lemmas that the three top-level
obligations would consume. Each is currently a `sorry` — see the
docstrings for the structural unblock that would close them. -/

/-- `sort_at` correctness: starting from an empty accumulator,
    `sort_at l 0 []` succeeds and returns a `Vec` that is weakly sorted,
    has the same membership as `l`, and contains only elements of `l`.

    **Stuck at**: closing the inductive step requires
    `insert_sorted_correct` (below) — the recursive call's invariants
    must compose with the outer induction on `l.val.size − i.toNat`. The
    Hax library does not contain a precedent for nested-recursion proof
    composition (only `clever_025_remove_duplicates` has an `outer
    inducts over inner`, and there the inner is non-Vec-building).

    **Structural unblock**: a verified insertion-sort correctness theorem
    for `Vec i64` would close this in one application; equivalently,
    proving `insert_sorted_correct` (the lemma below) closes this step. -/
private theorem sort_at_correct
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_033_unique.sort_at l (0 : usize)
              ⟨(List.nil : List i64).toArray, by grind⟩ = RustM.ok v) :
    IsWeaklyIncreasing v ∧
    InputSubsetOutput l v ∧
    OutputSubsetInput l v := by
  sorry

/-- `dedupe_at` correctness: on a weakly-sorted input slice,
    `dedupe_at sorted 0 []` succeeds and returns a `Vec` that is strictly
    increasing, has the same element-set as `sorted`, and contains only
    elements of `sorted`.

    **Stuck at**: the inductive step's accumulator invariant must relate
    `acc`'s last element to `sorted[i-1]`, and the proof needs the "last
    element of acc equals sorted[i-1]" invariant carried through the
    strong induction. This is structurally similar to
    `build_at_correct_strong` in `clever_025_remove_duplicates`, but with
    a different invariant (last-equality vs. count=1).

    **Structural unblock**: a generic "tail-recursive filter preserves
    membership and last-element invariant" lemma in the prelude would
    cover both this theorem and `clever_025_remove_duplicates`'s
    `build_at_correct_strong`. -/
private theorem dedupe_at_correct
    (sorted_slice : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_033_unique.dedupe_at sorted_slice (0 : usize)
              ⟨(List.nil : List i64).toArray, by grind⟩ = RustM.ok v)
    (hsorted : ∀ (i j : Nat) (hi : i < sorted_slice.val.size)
                 (hj : j < sorted_slice.val.size),
                 i < j → (sorted_slice.val[i]'hi).toInt ≤
                          (sorted_slice.val[j]'hj).toInt) :
    IsStrictlyIncreasing v ∧
    (∀ (i : Nat) (hi : i < sorted_slice.val.size),
        ∃ (k : Nat) (hk : k < v.val.size), v.val[k]'hk = sorted_slice.val[i]'hi) ∧
    (∀ (k : Nat) (hk : k < v.val.size),
        ∃ (i : Nat) (hi : i < sorted_slice.val.size),
          sorted_slice.val[i]'hi = v.val[k]'hk) := by
  sorry

/-! ## Top-level obligations.

Each top-level obligation reduces to one conjunct of `sort_at_correct`
combined with one conjunct of `dedupe_at_correct`, by unfolding
`unique`. The reduction is uniform across all three obligations: invert
`hres` (the assumption that `unique l = RustM.ok v`), extract the
intermediate `sorted` Vec, apply `sort_at_correct` to characterise
`sorted`, then apply `dedupe_at_correct` to characterise `v` in terms of
`sorted`, then in terms of `l`. -/

/-- Strict-monotonicity postcondition: the output is strictly increasing
    (in the signed `i64` ordering, via `.toInt`). A single strict-order
    invariant simultaneously captures "sorted ascending" and "no
    duplicates" (strict ordering rules out repeats). Captures the
    proptest `output_is_strictly_increasing` in the Rust source.

    **Stuck at**: the helper `dedupe_at_correct` is currently `sorry`.
    Given `dedupe_at_correct`, this theorem closes by unfolding `unique`,
    inverting `hres` to expose the intermediate sorted Vec, and applying
    `dedupe_at_correct.1` (the strict-monotonicity conjunct).

    **Structural unblock**: closing `dedupe_at_correct` closes this
    theorem in five lines. -/
theorem output_is_strictly_increasing
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_033_unique.unique l = RustM.ok v)
    (k₁ k₂ : Nat)
    (hk₁ : k₁ < v.val.size) (hk₂ : k₂ < v.val.size)
    (hlt : k₁ < k₂) :
    (v.val[k₁]'hk₁).toInt < (v.val[k₂]'hk₂).toInt := by
  -- Unfold `unique` to expose the (sort_at, dedupe_at) structure.
  unfold clever_033_unique.unique at hres
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil : List i64).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  -- Generalize the `sort_at` result so we can dispatch on its shape.
  generalize h_sort_def :
    clever_033_unique.sort_at l (0 : usize)
      ⟨(List.nil : List i64).toArray, by grind⟩ = rsort
  rw [h_sort_def] at hres
  cases rsort with
  | none => cases hres
  | some res =>
    cases res with
    | error e => cases hres
    | ok sorted =>
      simp only [RustM_ok_bind] at hres
      have h_deref : (core_models.ops.deref.Deref.deref
          (alloc.vec.Vec i64 alloc.alloc.Global) sorted :
            RustM (RustSlice i64)) = RustM.ok sorted := rfl
      rw [h_deref] at hres
      simp only [RustM_ok_bind] at hres
      rw [h_new] at hres
      simp only [RustM_ok_bind] at hres
      -- `hres : dedupe_at sorted 0 [] = RustM.ok v`.
      -- `h_sort_def : sort_at l 0 [] = RustM.ok sorted`.
      have h_sort := sort_at_correct l sorted h_sort_def
      obtain ⟨h_sort_weakly, _, _⟩ := h_sort
      have h_dedupe := dedupe_at_correct sorted v hres h_sort_weakly
      obtain ⟨h_v_strict, _, _⟩ := h_dedupe
      exact h_v_strict k₁ k₂ hk₁ hk₂ hlt

/-- Completeness postcondition: every input element appears at some
    output position. Captures the proptest
    `output_contains_every_input_element` in the Rust source.

    **Stuck at**: helpers `sort_at_correct` and `dedupe_at_correct` are
    currently `sorry`. The reduction is mechanical:

    1. `l[i]` appears in `sorted` (by `sort_at_correct.2.1`).
    2. Every element of `sorted` appears in `v` (by
       `dedupe_at_correct.2.1`).
    3. Compose.

    **Structural unblock**: closing `sort_at_correct` and
    `dedupe_at_correct` closes this theorem in ~ten lines. -/
theorem output_contains_every_input_element
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_033_unique.unique l = RustM.ok v)
    (i : Nat) (hi : i < l.val.size) :
    ∃ k : Nat, ∃ (hk : k < v.val.size), v.val[k]'hk = l.val[i]'hi := by
  unfold clever_033_unique.unique at hres
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil : List i64).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  generalize h_sort_def :
    clever_033_unique.sort_at l (0 : usize)
      ⟨(List.nil : List i64).toArray, by grind⟩ = rsort
  rw [h_sort_def] at hres
  cases rsort with
  | none => cases hres
  | some res =>
    cases res with
    | error e => cases hres
    | ok sorted =>
      simp only [RustM_ok_bind] at hres
      have h_deref : (core_models.ops.deref.Deref.deref
          (alloc.vec.Vec i64 alloc.alloc.Global) sorted :
            RustM (RustSlice i64)) = RustM.ok sorted := rfl
      rw [h_deref] at hres
      simp only [RustM_ok_bind] at hres
      rw [h_new] at hres
      simp only [RustM_ok_bind] at hres
      have h_sort := sort_at_correct l sorted h_sort_def
      obtain ⟨h_sort_weakly, h_l_to_sort, _⟩ := h_sort
      have h_dedupe := dedupe_at_correct sorted v hres h_sort_weakly
      obtain ⟨_, h_sort_to_v, _⟩ := h_dedupe
      -- l[i] ∈ sorted, and every element of sorted ∈ v.
      obtain ⟨k_sort, hk_sort, h_eq_sort⟩ := h_l_to_sort i hi
      -- h_eq_sort : sorted.val[k_sort]'hk_sort = l.val[i]'hi
      obtain ⟨k_v, hk_v, h_eq_v⟩ := h_sort_to_v k_sort hk_sort
      -- h_eq_v : v.val[k_v]'hk_v = sorted.val[k_sort]'hk_sort
      exact ⟨k_v, hk_v, by rw [h_eq_v]; exact h_eq_sort⟩

/-- Soundness postcondition: every output element occurs at some input
    position (the output introduces no spurious elements). Captures the
    proptest `output_only_contains_input_elements` in the Rust source.

    **Stuck at**: helpers `sort_at_correct` and `dedupe_at_correct` are
    currently `sorry`. The reduction is mechanical:

    1. `v[k]` comes from some `sorted[j]` (by
       `dedupe_at_correct.2.2`).
    2. Every element of `sorted` comes from some `l[i']` (by
       `sort_at_correct.2.2`).
    3. Compose.

    **Structural unblock**: closing `sort_at_correct` and
    `dedupe_at_correct` closes this theorem in ~ten lines. -/
theorem output_only_contains_input_elements
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_033_unique.unique l = RustM.ok v)
    (k : Nat) (hk : k < v.val.size) :
    ∃ i : Nat, ∃ (hi : i < l.val.size), l.val[i]'hi = v.val[k]'hk := by
  unfold clever_033_unique.unique at hres
  have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                  RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                RustM.ok ⟨(List.nil : List i64).toArray, by grind⟩ := rfl
  rw [h_new] at hres
  simp only [RustM_ok_bind] at hres
  generalize h_sort_def :
    clever_033_unique.sort_at l (0 : usize)
      ⟨(List.nil : List i64).toArray, by grind⟩ = rsort
  rw [h_sort_def] at hres
  cases rsort with
  | none => cases hres
  | some res =>
    cases res with
    | error e => cases hres
    | ok sorted =>
      simp only [RustM_ok_bind] at hres
      have h_deref : (core_models.ops.deref.Deref.deref
          (alloc.vec.Vec i64 alloc.alloc.Global) sorted :
            RustM (RustSlice i64)) = RustM.ok sorted := rfl
      rw [h_deref] at hres
      simp only [RustM_ok_bind] at hres
      rw [h_new] at hres
      simp only [RustM_ok_bind] at hres
      have h_sort := sort_at_correct l sorted h_sort_def
      obtain ⟨h_sort_weakly, _, h_sort_subset_l⟩ := h_sort
      have h_dedupe := dedupe_at_correct sorted v hres h_sort_weakly
      obtain ⟨_, _, h_v_subset_sort⟩ := h_dedupe
      -- v[k] = sorted[j], sorted[j] = l[i'].
      obtain ⟨j_sort, hj_sort, h_eq_v⟩ := h_v_subset_sort k hk
      -- h_eq_v : sorted.val[j_sort]'hj_sort = v.val[k]'hk
      obtain ⟨i_l, hi_l, h_eq_sort⟩ := h_sort_subset_l j_sort hj_sort
      -- h_eq_sort : ∃ ... l.val[i_l]'hi_l = sorted.val[j_sort]'hj_sort
      exact ⟨i_l, hi_l, by rw [h_eq_sort]; exact h_eq_v⟩

end Clever_033_uniqueObligations
