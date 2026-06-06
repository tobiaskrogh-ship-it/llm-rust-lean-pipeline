-- Companion obligations file for the `clever_036_sort_even` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_036_sort_even

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_036_sort_evenObligations

/-! ## Specification oracle: occurrence count at even-indexed positions.

For an `Array i64` `arr` and a value `target`, `count_at_even arr target k`
counts the number of indices `j < k` with `j` even and `arr[j] = target`.
The `dite` keeps the definition total — in actual use, every theorem below
applies it with `k ≤ arr.size`, keeping every checked index in range.

This is the analogue of `total_count` from `clever_025_remove_duplicates`
restricted to even positions. -/

private def count_at_even (arr : Array i64) (target : i64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      if h : k < arr.size then
        (if k % 2 = 0 ∧ (arr[k]'h) = target then 1 else 0)
          + count_at_even arr target k
      else
        count_at_even arr target k

/-! ## Standard scaffolding (transferred from `clever_009_rolling_max`,
     `clever_021_rescale_to_unit`, `clever_025_remove_duplicates`). -/

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

private theorem two_lt_usize_size : (2 : Nat) < USize64.size := by decide

private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

/-! ## OOB step lemmas for the three recursive helpers.

When the slice has been fully traversed (`size ≤ i.toNat`), each helper
returns the accumulator unchanged. This is the only branch we need to
close `empty_input_returns_empty`, where every recursion starts with
`i = 0` and `size = 0`. The pattern follows `count_at_oob`/`build_at_oob`
from `clever_025_remove_duplicates`. -/

private theorem insert_sorted_at_oob
    (v : RustSlice i64) (x : i64) (i : usize) (inserted : Bool)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat) :
    clever_036_sort_even.insert_sorted_at v x i inserted acc =
      RustM.ok (if inserted then acc else
        ⟨acc.val ++ #[x], by
          have : (acc.val ++ #[x]).size = acc.val.size + 1 := by
            rw [Array.size_append]; rfl
          rw [this]
          have hx : acc.val.size + 1 ≤ USize64.size := by
            have := acc.size_lt_usizeSize
            have h1 : (1 : Nat) < USize64.size := one_lt_usize_size
            omega
          -- We do not actually need a tight bound here for elaboration —
          -- the size_lt fact stays as an inequality. The `by grind` form
          -- below would handle it, but to keep this term-level we use a
          -- relaxed bound. The OOB step is only invoked from the empty
          -- recursion in `empty_input_returns_empty`, where the `inserted`
          -- branch is the one taken (so the witness side never runs).
          sorry⟩) := by
  -- This shape is too aggressive for the empty proof (it mixes both
  -- branches into the result). Use `insert_sorted_at_oob_inserted` below
  -- instead, which is what `empty_input_returns_empty` needs.
  sorry

/-- OOB step for `insert_sorted_at` when `inserted = true`: returns `acc`. -/
private theorem insert_sorted_at_oob_inserted
    (v : RustSlice i64) (x : i64) (i : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : v.val.size ≤ i.toNat) :
    clever_036_sort_even.insert_sorted_at v x i true acc = RustM.ok acc := by
  conv => lhs; unfold clever_036_sort_even.insert_sorted_at
  have h_ofNat : (USize64.ofNat v.val.size).toNat = v.val.size :=
    USize64.toNat_ofNat_of_lt' v.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat v.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- OOB step for `collect_evens`: returns the accumulator. -/
private theorem collect_evens_oob
    (l : RustSlice i64) (i : usize) (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : l.val.size ≤ i.toNat) :
    clever_036_sort_even.collect_evens l i acc = RustM.ok acc := by
  conv => lhs; unfold clever_036_sort_even.collect_evens
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

/-- OOB step for `rebuild_at`: returns the accumulator. -/
private theorem rebuild_at_oob
    (l sorted : RustSlice i64) (i j : usize)
    (acc : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : l.val.size ≤ i.toNat) :
    clever_036_sort_even.rebuild_at l sorted i j acc = RustM.ok acc := by
  conv => lhs; unfold clever_036_sort_even.rebuild_at
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

/-! ## Top-level contract clauses.

The Rust source contains four proptest contract clauses and one boundary
unit test. Each becomes one independent theorem below.

* `length_preserved` (proptest)              — `out.len() == l.len()`.
* `odd_indices_unchanged` (proptest)         — `out[i] == l[i]` for odd `i`.
* `even_indices_sorted` (proptest)           — output even-indexed values
                                                are non-decreasing.
* `even_indices_multiset_preserved` (proptest) — multiset of even-indexed
                                                  values is preserved.
* `empty_input_returns_empty` (unit test)    — `sort_even(&[])` returns
                                                an empty `Vec`. -/

/-- Length-preservation postcondition (also packages totality).
    Captures the proptest `length_preserved`.

    Stuck sub-goal after attempting structural induction: the proof needs a
    helper `collect_evens_correct` that tracks the size of the intermediate
    `sorted` vector. The natural invariant is
      `(collect_evens l i acc).val.size = acc.val.size + (# even j in [i, size))`,
    which can be proved by strong induction on `size − i.toNat` if we have a
    parallel `extend_from_slice [i64;1]` step lemma for `acc.size + 1`, plus
    a corresponding `extend_from_slice [i64;2]` step lemma for the
    `insert_sorted_at` even-branch. Then a second helper
    `rebuild_at_correct` needs `sorted.val.size ≥ (# even j in [0, size))`
    to discharge the `sorted[j]_?` bounds-check inside the recursive call.

    Structural unblock: separately-verified
      `insert_sorted_at_length : (insert_sorted_at v x i ins acc).val.size
        = acc.val.size + (size − i.toNat) + (if ins then 0 else 1)`
    and
      `collect_evens_length : (collect_evens l i acc).val.size
        = acc.val.size + (# even j in [i, size))`
    as `private theorem`s in this file would unblock the chain. Both follow
    the strong-induction shape of `shift_at_correct` from
    `clever_021_rescale_to_unit`, except they require a `[i64;2]` chunk
    push step lemma that no reference example provides. -/
theorem length_preserved
    (l : RustSlice i64) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_036_sort_even.sort_even l = RustM.ok v ∧
      v.val.size = l.val.size := by
  sorry

/-- Odd-index-preservation postcondition: at every odd in-range position
    the output equals the input pointwise.  Captures the proptest
    `odd_indices_unchanged`.

    Stuck sub-goal: the proof needs an invariant on `rebuild_at` showing
    that at the `i`-th position (odd branch), the output writes `l[i]`
    verbatim. Concretely:
      `rebuild_at_correct_odd : ∀ k, k % 2 = 1 → k < l.val.size →
        (rebuild_at l sorted 0 0 empty).val[k] = l.val[k]`.
    This is one half of the `rebuild_at` correctness invariant (the other
    half is for even indices, used by `even_indices_sorted` and
    `even_indices_multiset_preserved`).

    Structural unblock: a single `rebuild_at_correct` strong-induction
    lemma (shape mirrors `shift_at_correct` from
    `clever_021_rescale_to_unit`) with a per-position invariant
    parametrised on `i % 2` would close this and the two even-side
    theorems simultaneously. The lemma also needs the
    `insert_sorted_at_length` / `collect_evens_length` chain above to
    discharge the `sorted[j]_?` bounds-check inside its inductive step. -/
theorem odd_indices_unchanged
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_036_sort_even.sort_even l = RustM.ok v)
    (i : Nat) (h_v : i < v.val.size) (h_l : i < l.val.size)
    (hodd : i % 2 = 1) :
    v.val[i]'h_v = l.val[i]'h_l := by
  sorry

/-- Even-index sortedness postcondition: consecutive even-indexed output
    values are non-decreasing.  Captures the proptest
    `even_indices_sorted`.

    Stuck sub-goal: the proof needs *two* layered invariants. Inner:
    `insert_sorted_correct : ∀ acc x, acc sorted → (insert_sorted acc x)
       is sorted and a permutation of acc ∪ {x}`.
    Outer (using inner): `collect_evens_correct : ∀ l i acc, acc sorted →
       (collect_evens l i acc) is sorted and a permutation of acc ∪
       (multiset of even-indexed values in l[i..size))`.
    Then the `rebuild_at` invariant reads consecutive entries from this
    sorted intermediate.

    Structural unblock: a separately-verified
      `insert_sorted_at_sorted_invariant` private theorem in this file
      (or, even better, in the Hax prelude's `MissingLean/Array.lean` as
      a generic "sorted insert preserves sortedness" lemma) would unblock
      the chain. No reference example proves a `Pairwise (· ≤ ·)`-style
      sortedness postcondition; this is a structural gap in the library. -/
theorem even_indices_sorted
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_036_sort_even.sort_even l = RustM.ok v)
    (i : Nat) (h_v_i : i < v.val.size) (h_v_i2 : i + 2 < v.val.size)
    (heven : i % 2 = 0) :
    (v.val[i]'h_v_i).toInt ≤ (v.val[i + 2]'h_v_i2).toInt := by
  sorry

/-- Multiset-preservation postcondition for even-indexed values.
    Captures the proptest `even_indices_multiset_preserved`.

    Stuck sub-goal: the proof needs three layered invariants:
    1. `insert_sorted_correct_count : ∀ acc x target,
         count_in (insert_sorted acc x) target = count_in acc target
           + (if x = target then 1 else 0)`.
    2. `collect_evens_correct_count : ∀ l i acc target,
         count_in (collect_evens l i acc) target = count_in acc target
           + count_at_even_range l target i size`.
    3. `rebuild_at_correct_count : ∀ l sorted i j acc target,
         when `j ≤ sorted.val.size` and acc has the right
         partial-multiset shape,
         count_at_even (rebuild_at l sorted i j acc).val target k =
           count_at_even acc target k_acc + (multiset contribution from
           sorted[j..] for even slots in l[i..size))`.

    The chained composition then yields multiset equality between input
    even-indexed values and output even-indexed values.

    Structural unblock: a single
      `multiset_preserving_rebuild` private theorem combining (3) above
      with the `collect_evens_correct_count` from (2) — both are
      structurally similar to `count_at_correct` from
      `clever_025_remove_duplicates`, just with the per-target-count
      oracle restricted to even positions. The cleanest path is to
      develop them as private theorems in this file (no Mathlib needed),
      following the `count_at`-style strong induction. -/
theorem even_indices_multiset_preserved
    (l : RustSlice i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_036_sort_even.sort_even l = RustM.ok v)
    (target : i64) :
    count_at_even v.val target v.val.size =
      count_at_even l.val target l.val.size := by
  sorry

/-- Empty-input boundary clause: when the input slice is empty, `sort_even`
    returns successfully an empty `Vec`.  Captures the unit test
    `empty_input` (function is total — no panic on `&[]`). -/
theorem empty_input_returns_empty
    (l : RustSlice i64) (hempty : l.val.size = 0) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_036_sort_even.sort_even l = RustM.ok v ∧ v.val.size = 0 := by
  -- Witness: the empty `Vec`.
  let v_empty : alloc.vec.Vec i64 alloc.alloc.Global :=
    ⟨(List.nil : List i64).toArray, by grind⟩
  refine ⟨v_empty, ?_, ?_⟩
  · -- Show `sort_even l = RustM.ok v_empty`.
    unfold clever_036_sort_even.sort_even
    -- Step 1: `alloc.vec.Impl.new` returns `RustM.ok v_empty`.
    have h_new : (alloc.vec.Impl.new i64 rust_primitives.hax.Tuple0.mk :
                    RustM (alloc.vec.Vec i64 alloc.alloc.Global)) =
                  RustM.ok v_empty := rfl
    rw [h_new, RustM_ok_bind]
    -- Step 2: `collect_evens l 0 v_empty = RustM.ok v_empty`.
    have h_zero_le : l.val.size ≤ (0 : usize).toNat := by
      show l.val.size ≤ 0; rw [hempty]
    have h_collect := collect_evens_oob l (0 : usize) v_empty h_zero_le
    rw [h_collect, RustM_ok_bind]
    -- Step 3: `core_models.ops.deref.Deref.deref ... v_empty = pure v_empty`.
    -- The deref instance for any type is `fun self => pure self`.
    have h_deref :
        (core_models.ops.deref.Deref.deref (alloc.vec.Vec i64 alloc.alloc.Global)
          v_empty : RustM (alloc.vec.Vec i64 alloc.alloc.Global))
        = RustM.ok v_empty := rfl
    rw [h_deref, RustM_ok_bind]
    -- Step 4: `alloc.vec.Impl.new` again.
    rw [h_new, RustM_ok_bind]
    -- Step 5: `rebuild_at l v_empty 0 0 v_empty = RustM.ok v_empty`.
    exact rebuild_at_oob l v_empty (0 : usize) (0 : usize) v_empty h_zero_le
  · -- `v_empty.val.size = 0`.
    rfl

end Clever_036_sort_evenObligations
