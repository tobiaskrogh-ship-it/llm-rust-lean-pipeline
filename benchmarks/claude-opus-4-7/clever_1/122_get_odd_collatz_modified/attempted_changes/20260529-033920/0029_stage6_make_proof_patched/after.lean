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

/-! ## Specification oracle: Nat-level Collatz odd-orbit reference.

The Rust proptest `prop_matches_reference` compares the function output
against an iterative `reference` implementation that collects the odd
values along the Collatz orbit (including the terminating `1`) into a
sorted, deduplicated list. We mirror that here at the `Nat` level. The
iterative form takes a `fuel` argument for definite Lean termination; for
`n` in the proptest range (`1u64..=10_000`), the stopping time is well
under 1000 iterations, so `fuel = 1000` is comfortably safe. -/

/-- Mathematical Collatz step on `Nat`. -/
private def collatz_step (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Insert `x` into a sorted-ascending list `l`, deduping if `x` already
    occurs. Used by `reference` below. -/
private def sorted_insert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
    if x = y then y :: ys
    else if x < y then x :: y :: ys
    else y :: sorted_insert x ys

/-- Iterative Collatz orbit traversal that collects odd values into a sorted
    unique list. `fuel` bounds the iteration. -/
private def reference_iter : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | f + 1, n, acc =>
    if n = 1 then sorted_insert 1 acc
    else
      let acc' := if n % 2 = 1 then sorted_insert n acc else acc
      reference_iter f (collatz_step n) acc'

/-- Mathematical reference for `get_odd_collatz`. Returns `[]` for `n = 0`;
    otherwise iterates the Collatz step from `n`, collecting the odd values
    (including the terminating `1`) into a sorted unique list. -/
private def reference (n : Nat) : List Nat :=
  if n = 0 then [] else reference_iter 1000 n []

/-- `RustM.ok x >>= f = f x`. The library's `pure_bind` simp lemma only
    matches literal `Pure.pure`; this rewrite handles the `RustM.ok` form
    that simp produces after reducing definitions. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

/-- Helper: `(1 : usize).toNat = 1`. -/
private theorem usize_one_toNat : (1 : usize).toNat = 1 := rfl

/-- Helper: `(i + 1).toNat = i.toNat + 1` when no overflow. -/
private theorem usize_add_one_toNat (i : usize) (h : i.toNat + 1 < 2^64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h_pre : i.toNat + (1 : usize).toNat < 2^64 := by
    rw [usize_one_toNat]; exact h
  rw [USize64.toNat_add_of_lt h_pre, usize_one_toNat]

/-- Out-of-bounds step for `contains_at`. -/
private theorem contains_at_oob
    (arr : alloc.vec.Vec u64 alloc.alloc.Global) (target : u64) (i : usize)
    (hi : arr.val.size ≤ i.toNat) :
    clever_122_get_odd_collatz.contains_at arr target i = RustM.ok false := by
  conv => lhs; unfold clever_122_get_odd_collatz.contains_at
  have h_ofNat : (USize64.ofNat arr.val.size).toNat = arr.val.size :=
    USize64.toNat_ofNat_of_lt' arr.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat arr.val.size ≤ i) = true := by
    rw [decide_eq_true_iff]
    rw [USize64.le_iff_toNat_le, h_ofNat]
    exact hi
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind,
             h_cond, ↓reduceIte]
  rfl

/-- Found step for `contains_at`. -/
private theorem contains_at_found
    (arr : alloc.vec.Vec u64 alloc.alloc.Global) (target : u64) (i : usize)
    (hi : i.toNat < arr.val.size) (h : arr.val[i.toNat]'hi = target) :
    clever_122_get_odd_collatz.contains_at arr target i = RustM.ok true := by
  conv => lhs; unfold clever_122_get_odd_collatz.contains_at
  have h_ofNat : (USize64.ofNat arr.val.size).toNat = arr.val.size :=
    USize64.toNat_ofNat_of_lt' arr.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat arr.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (arr[i]_? : RustM u64) = RustM.ok (arr.val[i.toNat]'hi) := by
    show (if h : i.toNat < arr.val.size then pure (arr.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (arr.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
  have h_beq_true : (arr.val[i.toNat]'hi == target) = true := by
    rw [beq_iff_eq]; exact h
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.cmp.eq, h_beq_true]
  rfl

/-- Recursion step for `contains_at`. -/
private theorem contains_at_recurse
    (arr : alloc.vec.Vec u64 alloc.alloc.Global) (target : u64) (i : usize)
    (hi : i.toNat < arr.val.size) (h : arr.val[i.toNat]'hi ≠ target) :
    clever_122_get_odd_collatz.contains_at arr target i =
      clever_122_get_odd_collatz.contains_at arr target (i + 1) := by
  conv => lhs; unfold clever_122_get_odd_collatz.contains_at
  have h_ofNat : (USize64.ofNat arr.val.size).toNat = arr.val.size :=
    USize64.toNat_ofNat_of_lt' arr.size_lt_usizeSize
  have h_cond : decide (USize64.ofNat arr.val.size ≤ i) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    rw [USize64.le_iff_toNat_le, h_ofNat] at hle
    omega
  have h_idx : (arr[i]_? : RustM u64) = RustM.ok (arr.val[i.toNat]'hi) := by
    show (if h : i.toNat < arr.val.size then pure (arr.val[i]) else .fail .arrayOutOfBounds)
        = RustM.ok (arr.val[i.toNat]'hi)
    rw [dif_pos hi]
    rfl
  have h_beq_false : (arr.val[i.toNat]'hi == target) = false := by
    rw [beq_eq_false_iff_ne]; exact h
  have h_size : arr.val.size < 2^64 := arr.size_lt_usizeSize
  have h_no_overflow : i.toNat + 1 < 2^64 := by omega
  have h_no_bv : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = false := by
    generalize hbo : BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec = bo
    cases bo with
    | false => rfl
    | true =>
      exfalso
      have hi := (USize64.uaddOverflow_iff i 1).mp hbo
      rw [usize_one_toNat] at hi
      omega
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
             h_cond, Bool.false_eq_true, ↓reduceIte,
             h_idx,
             rust_primitives.cmp.eq, h_beq_false,
             rust_primitives.ops.arith.Add.add, h_no_bv]

/-! ## Contract clauses

The Rust source contains five contract-style tests in `mod tests`:

  * `zero_is_empty`                  — unit pin: `get_odd_collatz(0) = []`.
  * `known`                          — unit pins: `get_odd_collatz(1) = [1]`
                                       and `get_odd_collatz(5) = [1, 5]`.
  * `prop_sorted_strictly_ascending` — postcondition: output strictly ascending.
  * `prop_all_elements_odd`          — postcondition: every output element is odd.
  * `prop_matches_reference`         — postcondition: output equals the
                                       sorted unique list of odd Collatz orbit
                                       values starting at `n`.

Each becomes one independent `theorem` below. Note that `step_at`,
`contains_at`, and `insert_asc_at` are extracted with `partial_fixpoint`;
in particular `step_at`'s termination depends on the open Collatz
conjecture, so the universal postconditions are conditional on the
function returning `RustM.ok v` (the existence of an `ok` result is the
termination witness on the safe range). -/

/-- Boundary clause (from the unit test `zero_is_empty`):
    `get_odd_collatz(0)` returns an empty `Vec`. -/
theorem zero_is_empty :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_122_get_odd_collatz.get_odd_collatz (0 : u64) = RustM.ok v ∧
      v.val.size = 0 := by
  refine ⟨⟨#[], by grind⟩, ?_, rfl⟩
  rfl

/-- Unit pin (from the `known` test): `get_odd_collatz(1) = [1]`. -/
theorem get_odd_collatz_one_known :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_122_get_odd_collatz.get_odd_collatz (1 : u64) = RustM.ok v ∧
      v.val.toList = [(1 : u64)] := by
  refine ⟨⟨#[1], by grind⟩, ?_, rfl⟩
  unfold clever_122_get_odd_collatz.get_odd_collatz
  unfold clever_122_get_odd_collatz.step_at
  unfold clever_122_get_odd_collatz.contains_at
  unfold clever_122_get_odd_collatz.insert_asc
  unfold clever_122_get_odd_collatz.insert_asc_at
  rfl

/-! ## Step lemmas for `step_at` unfolding.

`step_at` is defined via `partial_fixpoint`, so we cannot reduce it via
`rfl` for general inputs.  We build one-step transition lemmas that match
the Collatz orbit and chain them. -/

/-- `step_at 1 acc = insert_asc acc 1` when `1` is not yet in `acc`. -/
private theorem step_at_one_no_one
    (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (h : clever_122_get_odd_collatz.contains_at
            acc (1 : u64) (0 : usize) = RustM.ok false) :
    clever_122_get_odd_collatz.step_at (1 : u64) acc =
      clever_122_get_odd_collatz.insert_asc acc (1 : u64) := by
  conv => lhs; unfold clever_122_get_odd_collatz.step_at
  show ((pure (decide ((1 : u64) = 1)) : RustM Bool) >>= _) = _
  simp only [decide_true, pure_bind, ↓reduceIte, if_true]
  show (((pure acc : RustM (alloc.vec.Vec u64 alloc.alloc.Global)) >>= _) : _) = _
  simp only [pure_bind]
  rw [h]
  show ((pure false : RustM Bool) >>= _) = _
  simp only [pure_bind]
  rfl

/-- `step_at k acc = step_at (k/2) acc` when `k` is even and `k ≠ 0` and `k ≠ 1`. -/
private theorem step_at_even
    (k : u64) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hkne1 : k ≠ 1)
    (hk_even : k % 2 = 0) :
    clever_122_get_odd_collatz.step_at k acc =
      clever_122_get_odd_collatz.step_at (k / 2) acc := by
  conv => lhs; unfold clever_122_get_odd_collatz.step_at
  show ((pure (decide (k = 1)) : RustM Bool) >>= _) = _
  have h1 : decide (k = 1) = false := decide_eq_false hkne1
  simp only [h1, pure_bind, ↓reduceIte]
  -- next: (k %? 2) ==? 1 → false
  show ((pure (k % 2) : RustM u64) >>= _) = _
  simp only [pure_bind]
  show ((pure (decide (k % 2 = 1)) : RustM Bool) >>= _) = _
  have h2 : decide (k % 2 = 1) = false := decide_eq_false (by rw [hk_even]; decide)
  simp only [h2, pure_bind, ↓reduceIte]
  -- final: k /? 2 = pure (k / 2)
  show ((pure (k / 2) : RustM u64) >>= _) = _
  simp only [pure_bind]

/-- `step_at k acc = step_at (3*k+1) acc` when `k` is odd, `k ≠ 1`, and
    `k` is already in `acc` (specifically, `contains_at acc k 0 = ok true`).
    Also requires that `3*k+1` doesn't overflow. -/
private theorem step_at_odd_in_acc
    (k : u64) (acc : alloc.vec.Vec u64 alloc.alloc.Global)
    (hkne1 : k ≠ 1)
    (hk_odd : k % 2 = 1)
    (h_contains :
      clever_122_get_odd_collatz.contains_at acc k (0 : usize) = RustM.ok true)
    (h_no_mul_ov : ((3 : u64) *? k : RustM u64) = RustM.ok (3 * k))
    (h_no_add_ov : ((3 * k) +? (1 : u64) : RustM u64) = RustM.ok (3 * k + 1)) :
    clever_122_get_odd_collatz.step_at k acc =
      clever_122_get_odd_collatz.step_at (3 * k + 1) acc := by
  conv => lhs; unfold clever_122_get_odd_collatz.step_at
  show ((pure (decide (k = 1)) : RustM Bool) >>= _) = _
  have h1 : decide (k = 1) = false := decide_eq_false hkne1
  simp only [h1, pure_bind, ↓reduceIte]
  show ((pure (k % 2) : RustM u64) >>= _) = _
  simp only [pure_bind]
  show ((pure (decide (k % 2 = 1)) : RustM Bool) >>= _) = _
  have h2 : decide (k % 2 = 1) = true := decide_eq_true hk_odd
  simp only [h2, pure_bind, ↓reduceIte]
  show ((pure acc : RustM (alloc.vec.Vec u64 alloc.alloc.Global)) >>= _) = _
  simp only [pure_bind]
  rw [h_contains]
  show ((pure true : RustM Bool) >>= _) = _
  simp only [pure_bind, ↓reduceIte, if_true]
  rw [h_no_mul_ov]
  show ((pure (3 * k) : RustM u64) >>= _) = _
  simp only [pure_bind]
  rw [h_no_add_ov]
  show ((pure (3 * k + 1) : RustM u64) >>= _) = _
  simp only [pure_bind]

/-- `step_at k acc = step_at (3*k+1) (insert_asc acc k)` when `k` is odd,
    `k ≠ 1`, and `k` is NOT already in `acc`. -/
private theorem step_at_odd_not_in_acc
    (k : u64) (acc next : alloc.vec.Vec u64 alloc.alloc.Global)
    (hkne1 : k ≠ 1)
    (hk_odd : k % 2 = 1)
    (h_contains :
      clever_122_get_odd_collatz.contains_at acc k (0 : usize) = RustM.ok false)
    (h_insert : clever_122_get_odd_collatz.insert_asc acc k = RustM.ok next)
    (h_no_mul_ov : ((3 : u64) *? k : RustM u64) = RustM.ok (3 * k))
    (h_no_add_ov : ((3 * k) +? (1 : u64) : RustM u64) = RustM.ok (3 * k + 1)) :
    clever_122_get_odd_collatz.step_at k acc =
      clever_122_get_odd_collatz.step_at (3 * k + 1) next := by
  conv => lhs; unfold clever_122_get_odd_collatz.step_at
  show ((pure (decide (k = 1)) : RustM Bool) >>= _) = _
  have h1 : decide (k = 1) = false := decide_eq_false hkne1
  simp only [h1, pure_bind, ↓reduceIte]
  show ((pure (k % 2) : RustM u64) >>= _) = _
  simp only [pure_bind]
  show ((pure (decide (k % 2 = 1)) : RustM Bool) >>= _) = _
  have h2 : decide (k % 2 = 1) = true := decide_eq_true hk_odd
  simp only [h2, pure_bind, ↓reduceIte]
  show ((pure acc : RustM (alloc.vec.Vec u64 alloc.alloc.Global)) >>= _) = _
  simp only [pure_bind]
  rw [h_contains]
  show ((pure false : RustM Bool) >>= _) = _
  simp only [pure_bind, ↓reduceIte, if_false]
  rw [h_insert]
  show ((pure next : RustM (alloc.vec.Vec u64 alloc.alloc.Global)) >>= _) = _
  simp only [pure_bind]
  rw [h_no_mul_ov]
  show ((pure (3 * k) : RustM u64) >>= _) = _
  simp only [pure_bind]
  rw [h_no_add_ov]
  show ((pure (3 * k + 1) : RustM u64) >>= _) = _
  simp only [pure_bind]

/-- Unit pin (from the `known` test): `get_odd_collatz(5) = [1, 5]`. -/
theorem get_odd_collatz_five_known :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_122_get_odd_collatz.get_odd_collatz (5 : u64) = RustM.ok v ∧
      v.val.toList = [(1 : u64), (5 : u64)] := by
  refine ⟨⟨#[1, 5], by grind⟩, ?_, rfl⟩
  -- Build the chain step_at 5 [] → step_at 16 [5] → ... → step_at 1 [5] → ok [1, 5]
  -- Initial: get_odd_collatz 5 = step_at 5 empty
  unfold clever_122_get_odd_collatz.get_odd_collatz
  show ((pure (decide ((5 : u64) = 0)) : RustM Bool) >>= _) = _
  simp only [(by decide : decide ((5 : u64) = 0) = false), pure_bind, ↓reduceIte]
  show ((pure (⟨#[], by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global) : RustM (alloc.vec.Vec u64 alloc.alloc.Global)) >>= _) = _
  simp only [pure_bind]
  -- Now goal: step_at 5 empty = ok [1, 5]
  -- Step 1: step_at 5 empty = step_at 16 [5]
  have h_empty_no_5 :
      clever_122_get_odd_collatz.contains_at
        (⟨#[], by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global) (5 : u64) (0 : usize)
        = RustM.ok false := by
    unfold clever_122_get_odd_collatz.contains_at
    rfl
  have h_insert_empty_5 :
      clever_122_get_odd_collatz.insert_asc
        (⟨#[], by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global) (5 : u64) =
      RustM.ok (⟨#[5], by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global) := by
    unfold clever_122_get_odd_collatz.insert_asc
    unfold clever_122_get_odd_collatz.insert_asc_at
    rfl
  rw [step_at_odd_not_in_acc 5 _ _ (by decide) (by decide) h_empty_no_5 h_insert_empty_5 rfl rfl]
  -- Normalize 3*5+1 → 16
  show clever_122_get_odd_collatz.step_at (16 : u64) _ = _
  -- step_at 16 [5] = step_at 8 [5]
  rw [step_at_even 16 _ (by decide) (by decide)]
  show clever_122_get_odd_collatz.step_at (8 : u64) _ = _
  rw [step_at_even 8 _ (by decide) (by decide)]
  show clever_122_get_odd_collatz.step_at (4 : u64) _ = _
  rw [step_at_even 4 _ (by decide) (by decide)]
  show clever_122_get_odd_collatz.step_at (2 : u64) _ = _
  rw [step_at_even 2 _ (by decide) (by decide)]
  show clever_122_get_odd_collatz.step_at (1 : u64) _ = _
  -- step_at 1 [5]
  have h_acc_5_no_1 :
      clever_122_get_odd_collatz.contains_at
        (⟨#[5], by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global) (1 : u64) (0 : usize)
        = RustM.ok false := by
    rw [contains_at_recurse _ 1 0 (by decide) (by decide)]
    exact contains_at_oob _ 1 1 (by decide)
  rw [step_at_one_no_one _ h_acc_5_no_1]
  -- Goal: insert_asc [5] 1 = ok [1, 5]
  unfold clever_122_get_odd_collatz.insert_asc
  unfold clever_122_get_odd_collatz.insert_asc_at
  unfold clever_122_get_odd_collatz.insert_asc_at
  rfl

/-- Postcondition (from the proptest `prop_sorted_strictly_ascending`):
    on any successful run, consecutive output entries are strictly
    increasing. Captures sortedness AND uniqueness in one statement,
    matching the proptest's `windows(2)` form. -/
theorem output_is_strictly_increasing
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_122_get_odd_collatz.get_odd_collatz n = RustM.ok v)
    (k : Nat) (hk : k + 1 < v.val.size) :
    (v.val[k]'(Nat.lt_of_succ_lt hk)).toNat < (v.val[k + 1]'hk).toNat := by
  sorry

/-- Postcondition (from the proptest `prop_all_elements_odd`):
    every element of the output is odd. -/
theorem output_all_elements_odd
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_122_get_odd_collatz.get_odd_collatz n = RustM.ok v)
    (k : Nat) (hk : k < v.val.size) :
    (v.val[k]'hk).toNat % 2 = 1 := by
  sorry

/-- Postcondition (from the proptest `prop_matches_reference`):
    the output equals the mathematical reference — the sorted unique list
    of odd values along the Collatz orbit starting at `n`. This is the
    core semantic claim of the function. -/
theorem output_matches_reference
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_122_get_odd_collatz.get_odd_collatz n = RustM.ok v) :
    v.val.toList.map UInt64.toNat = reference n.toNat := by
  sorry

end Clever_122_get_odd_collatzObligations
