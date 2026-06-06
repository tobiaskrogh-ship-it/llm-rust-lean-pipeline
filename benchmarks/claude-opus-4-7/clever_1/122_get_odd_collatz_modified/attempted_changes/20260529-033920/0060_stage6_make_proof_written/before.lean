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
  simp only [decide_true, pure_bind, ↓reduceIte]
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
  simp only [h1, pure_bind]
  -- next: (k %? 2) ==? 1 → false
  show ((pure (k % 2) : RustM u64) >>= _) = _
  simp only [pure_bind]
  show ((pure (decide (k % 2 = 1)) : RustM Bool) >>= _) = _
  have h2 : decide (k % 2 = 1) = false := decide_eq_false (by rw [hk_even]; decide)
  simp only [h2, pure_bind]
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
  simp only [h1, pure_bind]
  show ((pure (k % 2) : RustM u64) >>= _) = _
  simp only [pure_bind]
  show ((pure (decide (k % 2 = 1)) : RustM Bool) >>= _) = _
  have h2 : decide (k % 2 = 1) = true := decide_eq_true hk_odd
  simp only [h2, pure_bind]
  show ((pure acc : RustM (alloc.vec.Vec u64 alloc.alloc.Global)) >>= _) = _
  simp only [pure_bind]
  rw [h_contains]
  show ((pure true : RustM Bool) >>= _) = _
  simp only [pure_bind]
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
  simp only [h1, pure_bind]
  show ((pure (k % 2) : RustM u64) >>= _) = _
  simp only [pure_bind]
  show ((pure (decide (k % 2 = 1)) : RustM Bool) >>= _) = _
  have h2 : decide (k % 2 = 1) = true := decide_eq_true hk_odd
  simp only [h2, pure_bind]
  show ((pure acc : RustM (alloc.vec.Vec u64 alloc.alloc.Global)) >>= _) = _
  simp only [pure_bind]
  rw [h_contains]
  show ((pure false : RustM Bool) >>= _) = _
  simp only [pure_bind]
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
  simp only [(by decide : decide ((5 : u64) = 0) = false), pure_bind]
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
    increasing.

    AGENT ADMISSION: I attempted this proof via `step_at.fixpoint_induct`
    with a `strictly_increasing acc → strictly_increasing v` motive and
    could not complete it. Discharging the invariant for `insert_asc_at`
    requires a multi-state carried bundle (strictly-increasing accumulator
    PLUS a current upper-bound predicate keyed on the `done : Bool` flag),
    and the six-arm body of `insert_asc_at` requires multiple step lemmas
    that proved fragile under `simp only` reduction of the `RustM` do-block
    binds (the `rust_primitives.unsize`, `extend_from_slice`, and
    `i +? 1` chains all need precise rewriting). I am incapable of
    completing this proof and no future iteration of this pipeline with
    the same model and references could complete it either.

    Stuck sub-goal: at the recursive step of `insert_asc_at_preserves_sorted`
    in the in-bounds vi ≥ x branch, the carried `(¬done → ∀ k, acc[k] < x)`
    upper-bound invariant must be re-established for the extended `acc'`
    after a 2-element chunk extend; the `simp only` reduction of the
    `RustM` bind chain stripped the structure I needed for the case analysis.

    Structural unblock: a separately verified
    `insert_asc_at_preserves_strictly_ascending_no_duplicates` lemma in the
    Hax prelude (parametric in the slice and the inserted value), plus an
    `insert_asc_preserves_strictly_ascending` corollary, would discharge
    the invariant cleanly. With those in place, the step-at fixpoint
    induction follows the same shape as the `output_all_elements_odd`
    attempt below. -/
theorem output_is_strictly_increasing
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_122_get_odd_collatz.get_odd_collatz n = RustM.ok v)
    (k : Nat) (hk : k + 1 < v.val.size) :
    (v.val[k]'(Nat.lt_of_succ_lt hk)).toNat < (v.val[k + 1]'hk).toNat := by
  sorry

/-! ## Scaffolding for the universal postconditions.

The three universal contracts are conditional on
`get_odd_collatz n = RustM.ok v`. Their proofs go via `step_at`'s
`fixpoint_induct` principle, choosing an admissible motive of the form
`∀ x acc v', f x acc = RustM.ok v' → InvAcc acc → InvOut acc v'`. -/

/-- The unary "all elements odd" predicate on a `Vec u64`. -/
private def all_odd (a : alloc.vec.Vec u64 alloc.alloc.Global) : Prop :=
  ∀ k : Nat, ∀ (hk : k < a.val.size), (a.val[k]'hk).toNat % 2 = 1

private theorem all_odd_empty :
    all_odd (⟨#[], by grind⟩ : alloc.vec.Vec u64 alloc.alloc.Global) := by
  intro k hk
  -- size = 0, no k < 0
  exact absurd hk (by simp)

/-! ## Insert_asc invariant: preserves `all_odd` when inserting an odd value.

The strategy: prove `insert_asc_at` preserves `all_odd` via strong induction
on the measure `arr.val.size - i.toNat`. -/

/-- Step lemma for `extend_from_slice`: appending preserves all_odd
    when the appended chunk has only odd values. -/
private theorem extend_from_slice_one_odd
    (acc : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64)
    (h_acc : all_odd acc) (h_x : x.toNat % 2 = 1) :
    ∀ (acc' : alloc.vec.Vec u64 alloc.alloc.Global),
      alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[x], by grind⟩ = RustM.ok acc' → all_odd acc' := by
  intro acc' h
  unfold alloc.vec.Impl_2.extend_from_slice at h
  by_cases h_size : acc.val.size + (⟨#[x], by grind⟩ : RustSlice u64).val.size < USize64.size
  · rw [dif_pos h_size] at h
    -- pure x = RustM.ok x, so h : RustM.ok ... = RustM.ok acc'
    injection h with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    intro k hk
    -- acc'.val = acc.val.append #[x]
    show ((acc.val.append (⟨#[x], by grind⟩ : RustSlice u64).val)[k]'_).toNat % 2 = 1
    by_cases hk_lt : k < acc.val.size
    · show ((acc.val ++ (⟨#[x], by grind⟩ : RustSlice u64).val)[k]'_).toNat % 2 = 1
      rw [Array.getElem_append_left hk_lt]
      exact h_acc k hk_lt
    · -- k = acc.val.size
      have h_size_app : (acc.val.append (⟨#[x], by grind⟩ : RustSlice u64).val).size
                          = acc.val.size + 1 := by
        show (acc.val ++ (⟨#[x], by grind⟩ : RustSlice u64).val).size = acc.val.size + 1
        rw [Array.size_append]
        rfl
      have hk_eq : k = acc.val.size := by
        rw [h_size_app] at hk; omega
      subst hk_eq
      show ((acc.val ++ (⟨#[x], by grind⟩ : RustSlice u64).val)[acc.val.size]'_).toNat % 2 = 1
      rw [Array.getElem_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self]
      show ((#[x])[0]).toNat % 2 = 1
      exact h_x
  · rw [dif_neg h_size] at h
    exact absurd h (by intro hh; cases hh)

/-- Step lemma for `extend_from_slice` with a 2-element chunk [x, vi]. -/
private theorem extend_from_slice_two_odd
    (acc : alloc.vec.Vec u64 alloc.alloc.Global) (x vi : u64)
    (h_acc : all_odd acc) (h_x : x.toNat % 2 = 1) (h_vi : vi.toNat % 2 = 1) :
    ∀ (acc' : alloc.vec.Vec u64 alloc.alloc.Global),
      alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
        ⟨#[x, vi], by grind⟩ = RustM.ok acc' → all_odd acc' := by
  intro acc' h
  unfold alloc.vec.Impl_2.extend_from_slice at h
  by_cases h_size : acc.val.size + (⟨#[x, vi], by grind⟩ : RustSlice u64).val.size < USize64.size
  · rw [dif_pos h_size] at h
    injection h with h_eq
    injection h_eq with h_eq'
    subst h_eq'
    intro k hk
    show ((acc.val.append (⟨#[x, vi], by grind⟩ : RustSlice u64).val)[k]'_).toNat % 2 = 1
    by_cases hk_lt : k < acc.val.size
    · show ((acc.val ++ (⟨#[x, vi], by grind⟩ : RustSlice u64).val)[k]'_).toNat % 2 = 1
      rw [Array.getElem_append_left hk_lt]
      exact h_acc k hk_lt
    · have h_size_app : (acc.val.append (⟨#[x, vi], by grind⟩ : RustSlice u64).val).size
                          = acc.val.size + 2 := by
        show (acc.val ++ (⟨#[x, vi], by grind⟩ : RustSlice u64).val).size = _
        rw [Array.size_append]
        rfl
      have hk_range : k = acc.val.size ∨ k = acc.val.size + 1 := by
        rw [h_size_app] at hk; omega
      rcases hk_range with heq | heq
      · subst heq
        show ((acc.val ++ (⟨#[x, vi], by grind⟩ : RustSlice u64).val)[acc.val.size]'_).toNat % 2 = 1
        rw [Array.getElem_append_right (Nat.le_refl _)]
        simp only [Nat.sub_self]
        show ((#[x, vi])[0]).toNat % 2 = 1
        exact h_x
      · subst heq
        have h_le : acc.val.size ≤ acc.val.size + 1 := Nat.le_succ _
        show ((acc.val ++ (⟨#[x, vi], by grind⟩ : RustSlice u64).val)[acc.val.size + 1]'_).toNat % 2 = 1
        rw [Array.getElem_append_right h_le]
        simp only [Nat.add_sub_cancel_left]
        show ((#[x, vi])[1]).toNat % 2 = 1
        exact h_vi
  · rw [dif_neg h_size] at h
    exact absurd h (by intro hh; cases hh)

/-! ## `slice_all_odd` companion predicate (Vec-deref'd-to-slice case). -/

private def slice_all_odd (s : RustSlice u64) : Prop :=
  ∀ k : Nat, ∀ (hk : k < s.val.size), (s.val[k]'hk).toNat % 2 = 1

private theorem slice_all_odd_of_all_odd (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (h : all_odd v) : slice_all_odd ⟨v.val, v.size_lt_usizeSize⟩ := h

/-! ## Preservation of `all_odd` through `insert_asc_at`.

Strong induction on the measure `src.val.size - i.toNat`. At each step,
unfold one layer of `insert_asc_at` and dispatch the six arms (oob_extend,
oob_done, in_eq, in_neq, skip, copy). Each arm either terminates (oob
arms) or recurses with `i + 1` (smaller measure) on an extended `acc'`
that we show is still `all_odd` via `extend_from_slice_one_odd` /
`extend_from_slice_two_odd`. -/

private theorem insert_asc_at_preserves_all_odd
    (src : RustSlice u64) (x : u64)
    (h_src : slice_all_odd src) (h_x : x.toNat % 2 = 1) :
    ∀ (m : Nat) (i : usize) (done : Bool) (acc next : alloc.vec.Vec u64 alloc.alloc.Global),
      src.val.size - i.toNat ≤ m →
      all_odd acc →
      clever_122_get_odd_collatz.insert_asc_at src x i done acc = RustM.ok next →
      all_odd next := by
  have h_src_size : src.val.size < 2 ^ 64 := src.size_lt_usizeSize
  have h_size_eq : (USize64.size : Nat) = 2 ^ 64 := by decide
  -- Common unfolding facts.
  have h_len_eq (i : usize) :
      (core_models.slice.Impl.len u64 src : RustM usize)
        = RustM.ok (USize64.ofNat src.val.size) := rfl
  have h_ofNat : (USize64.ofNat src.val.size).toNat = src.val.size :=
    USize64.toNat_ofNat_of_lt' src.size_lt_usizeSize
  intro m
  induction m with
  | zero =>
    intro i done acc next hm h_acc h_eq
    have hi_ge : src.val.size ≤ i.toNat := by omega
    -- OOB arm
    rw [clever_122_get_odd_collatz.insert_asc_at.eq_def] at h_eq
    have h_cond_ge : decide (USize64.ofNat src.val.size ≤ i) = true := by
      rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat]; exact hi_ge
    simp only [h_len_eq, RustM_ok_bind, rust_primitives.cmp.ge,
               pure_bind, h_cond_ge, ↓reduceIte] at h_eq
    cases hd : done with
    | true =>
      rw [hd] at h_eq
      simp only [rust_primitives.hax.logical_op.not, pure_bind,
                 Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h_eq
      injection h_eq with h_eq2
      injection h_eq2 with h_eq3
      subst h_eq3
      exact h_acc
    | false =>
      rw [hd] at h_eq
      simp only [rust_primitives.hax.logical_op.not, pure_bind,
                 Bool.not_false, ↓reduceIte] at h_eq
      -- Now h_eq says: do { let __do_lift ← unsize ⟨#v[x]⟩; let acc ← extend ...; pure acc } = ok next
      have h_unsize :
          (rust_primitives.unsize (RustArray.ofVec #v[x] : RustArray u64 1)
              : RustM (rust_primitives.sequence.Seq u64))
            = RustM.ok ⟨#[x], by decide⟩ := rfl
      rw [h_unsize] at h_eq
      simp only [RustM_ok_bind] at h_eq
      -- h_eq : (extend acc ⟨#[x], _⟩ >>= pure) = ok next
      -- This says: ∃ acc', extend = ok acc' ∧ pure acc' = ok next, so extend = ok next.
      have h_extend : alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
                        ⟨#[x], by decide⟩ = RustM.ok next := by
        generalize hext : alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
                            (⟨#[x], by decide⟩ : RustSlice u64) = r at h_eq
        cases r with
        | ok a =>
          simp only [RustM_ok_bind] at h_eq
          -- h_eq : pure a = ok next, so a = next
          have : a = next := by
            change (RustM.ok a : RustM _) = RustM.ok next at h_eq
            injection h_eq with h_eq2
            injection h_eq2
            assumption
          subst this; rfl
        | fail e =>
          exfalso
          show False
          change (RustM.fail e >>= _ : RustM _) = RustM.ok next at h_eq
          rfl_at_h_eq:
          rfl
      exact extend_from_slice_one_odd acc x h_acc h_x next h_extend
  | succ m ih =>
    intro i done acc next hm h_acc h_eq
    by_cases hi_ge : src.val.size ≤ i.toNat
    · -- OOB arm — same as base case
      rw [clever_122_get_odd_collatz.insert_asc_at.eq_def] at h_eq
      have h_cond_ge : decide (USize64.ofNat src.val.size ≤ i) = true := by
        rw [decide_eq_true_iff, USize64.le_iff_toNat_le, h_ofNat]; exact hi_ge
      simp only [h_len_eq, RustM_ok_bind, rust_primitives.cmp.ge,
                 pure_bind, h_cond_ge, ↓reduceIte] at h_eq
      cases hd : done with
      | true =>
        rw [hd] at h_eq
        simp only [rust_primitives.hax.logical_op.not, pure_bind,
                   Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h_eq
        injection h_eq with h_eq2
        injection h_eq2 with h_eq3
        subst h_eq3
        exact h_acc
      | false =>
        rw [hd] at h_eq
        simp only [rust_primitives.hax.logical_op.not, pure_bind,
                   Bool.not_false, ↓reduceIte] at h_eq
        have h_unsize :
            (rust_primitives.unsize (RustArray.ofVec #v[x] : RustArray u64 1)
                : RustM (rust_primitives.sequence.Seq u64))
              = RustM.ok ⟨#[x], by decide⟩ := rfl
        rw [h_unsize] at h_eq
        simp only [RustM_ok_bind] at h_eq
        have h_extend : alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
                          ⟨#[x], by decide⟩ = RustM.ok next := by
          generalize hext : alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
                              (⟨#[x], by decide⟩ : RustSlice u64) = r at h_eq
          cases r with
          | ok a =>
            simp only [RustM_ok_bind] at h_eq
            have : a = next := by
              change (RustM.ok a : RustM _) = RustM.ok next at h_eq
              injection h_eq with h_eq2
              injection h_eq2
              assumption
            subst this; rfl
          | fail e =>
            exfalso
            change (RustM.fail e >>= _ : RustM _) = RustM.ok next at h_eq
            cases h_eq
        exact extend_from_slice_one_odd acc x h_acc h_x next h_extend
    · -- In-bounds arm
      have hi_lt : i.toNat < src.val.size := Nat.lt_of_not_le hi_ge
      have h_no_ov : i.toNat + 1 < 2 ^ 64 := by omega
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 := usize_add_one_toNat i h_no_ov
      have h_meas : src.val.size - (i + 1).toNat ≤ m := by rw [h_i1_toNat]; omega
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
      have h_add :
          (i +? (1 : usize) : RustM usize) = RustM.ok (i + 1) := by
        show (rust_primitives.ops.arith.Add.add i 1 : RustM usize) = RustM.ok (i + 1)
        show (if BitVec.uaddOverflow i.toBitVec (1 : usize).toBitVec
              then (.fail .integerOverflow : RustM usize)
              else pure (i + 1)) = _
        rw [h_no_bv]; rfl
      rw [clever_122_get_odd_collatz.insert_asc_at.eq_def] at h_eq
      have h_cond_ge : decide (USize64.ofNat src.val.size ≤ i) = false := by
        rw [decide_eq_false_iff_not, USize64.le_iff_toNat_le, h_ofNat]
        omega
      simp only [h_len_eq, RustM_ok_bind, rust_primitives.cmp.ge,
                 pure_bind, h_cond_ge, Bool.false_eq_true, ↓reduceIte] at h_eq
      -- Now reduce v[i]_? = ok (v.val[i.toNat]).
      have h_idx : (src[i]_? : RustM u64) = RustM.ok (src.val[i.toNat]'hi_lt) := by
        show (if h : i.toNat < src.val.size then pure (src.val[i]) else .fail .arrayOutOfBounds)
            = RustM.ok (src.val[i.toNat]'hi_lt)
        rw [dif_pos hi_lt]; rfl
      rw [h_idx] at h_eq
      simp only [RustM_ok_bind] at h_eq
      set vi := src.val[i.toNat]'hi_lt with hvi_def
      have h_vi_odd : vi.toNat % 2 = 1 := h_src i.toNat hi_lt
      cases hd : done with
      | false =>
        rw [hd] at h_eq
        simp only [rust_primitives.hax.logical_op.not, pure_bind,
                   Bool.not_false] at h_eq
        -- Conjunction: true && (vi >= x)
        by_cases h_vi_ge : x ≤ vi
        · -- (true) && (true) = true ⇒ insert x here, recurse
          have h_ge : (vi >=? x : RustM Bool) = RustM.ok true := by
            show pure (decide (x ≤ vi)) = RustM.ok true
            rw [decide_eq_true h_vi_ge]
          rw [h_ge] at h_eq
          simp only [RustM_ok_bind, rust_primitives.hax.logical_op.and,
                     Bool.and_self, Bool.true_and, pure_bind, ↓reduceIte] at h_eq
          by_cases h_vi_eq : vi = x
          · -- vi == x: extend [x] and recurse with done=true
            have h_eq_b : (vi ==? x : RustM Bool) = RustM.ok true := by
              show pure (decide (vi = x)) = RustM.ok true
              rw [decide_eq_true h_vi_eq]
            rw [h_eq_b] at h_eq
            simp only [RustM_ok_bind, pure_bind, ↓reduceIte] at h_eq
            have h_unsize :
                (rust_primitives.unsize (RustArray.ofVec #v[x] : RustArray u64 1)
                    : RustM (rust_primitives.sequence.Seq u64))
                  = RustM.ok ⟨#[x], by decide⟩ := rfl
            rw [h_unsize] at h_eq
            simp only [RustM_ok_bind] at h_eq
            -- h_eq : (extend acc [x]) >>= (fun acc' => insert_asc_at src x (i+1) true acc') = ok next
            generalize hext : alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
                                (⟨#[x], by decide⟩ : RustSlice u64) = r at h_eq
            cases r with
            | ok acc' =>
              simp only [RustM_ok_bind] at h_eq
              rw [h_add] at h_eq
              simp only [RustM_ok_bind] at h_eq
              have h_acc' : all_odd acc' :=
                extend_from_slice_one_odd acc x h_acc h_x acc' hext
              exact ih (i + 1) true acc' next h_meas h_acc' h_eq
            | fail e =>
              exfalso
              change (RustM.fail e >>= _ : RustM _) = RustM.ok next at h_eq
              cases h_eq
          · -- vi ≠ x: extend [x, vi] and recurse with done=true
            have h_eq_b : (vi ==? x : RustM Bool) = RustM.ok false := by
              show pure (decide (vi = x)) = RustM.ok false
              rw [decide_eq_false h_vi_eq]
            rw [h_eq_b] at h_eq
            simp only [RustM_ok_bind, pure_bind, Bool.false_eq_true, ↓reduceIte] at h_eq
            have h_unsize :
                (rust_primitives.unsize (RustArray.ofVec #v[x, vi] : RustArray u64 2)
                    : RustM (rust_primitives.sequence.Seq u64))
                  = RustM.ok ⟨#[x, vi], by decide⟩ := rfl
            rw [h_unsize] at h_eq
            simp only [RustM_ok_bind] at h_eq
            generalize hext : alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
                                (⟨#[x, vi], by decide⟩ : RustSlice u64) = r at h_eq
            cases r with
            | ok acc' =>
              simp only [RustM_ok_bind] at h_eq
              rw [h_add] at h_eq
              simp only [RustM_ok_bind] at h_eq
              have h_acc' : all_odd acc' :=
                extend_from_slice_two_odd acc x vi h_acc h_x h_vi_odd acc' hext
              exact ih (i + 1) true acc' next h_meas h_acc' h_eq
            | fail e =>
              exfalso
              change (RustM.fail e >>= _ : RustM _) = RustM.ok next at h_eq
              cases h_eq
        · -- x > vi: condition is false. Fall through to "copy vi" branch.
          have h_ge : (vi >=? x : RustM Bool) = RustM.ok false := by
            show pure (decide (x ≤ vi)) = RustM.ok false
            rw [decide_eq_false h_vi_ge]
          rw [h_ge] at h_eq
          simp only [RustM_ok_bind, rust_primitives.hax.logical_op.and,
                     Bool.and_false, pure_bind, Bool.false_eq_true,
                     ↓reduceIte] at h_eq
          -- Then: done && (vi == x). done = false here, so this is false.
          -- Conjunction `false && anything = false`. Need to handle vi == x query first.
          -- But the body has `let __do_lift ← vi ==? x; let __do_lift ← done &&? __do_lift; if ...`
          have h_done_and (b : Bool) :
              (rust_primitives.hax.logical_op.and false b : RustM Bool) = RustM.ok false := by
            show pure (false && b) = RustM.ok false
            simp
          -- Need to reduce: vi ==? x; then done(=false) &&? __; then if = false then "copy" branch
          by_cases h_vi_eq : vi = x
          · have h_eq_b : (vi ==? x : RustM Bool) = RustM.ok true := by
              show pure (decide (vi = x)) = RustM.ok true
              rw [decide_eq_true h_vi_eq]
            rw [h_eq_b] at h_eq
            simp only [RustM_ok_bind, h_done_and, pure_bind, Bool.false_eq_true,
                       ↓reduceIte] at h_eq
            -- Now copy [vi] then recurse
            have h_unsize :
                (rust_primitives.unsize (RustArray.ofVec #v[vi] : RustArray u64 1)
                    : RustM (rust_primitives.sequence.Seq u64))
                  = RustM.ok ⟨#[vi], by decide⟩ := rfl
            rw [h_unsize] at h_eq
            simp only [RustM_ok_bind] at h_eq
            generalize hext : alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
                                (⟨#[vi], by decide⟩ : RustSlice u64) = r at h_eq
            cases r with
            | ok acc' =>
              simp only [RustM_ok_bind] at h_eq
              rw [h_add] at h_eq
              simp only [RustM_ok_bind] at h_eq
              have h_acc' : all_odd acc' :=
                extend_from_slice_one_odd acc vi h_acc h_vi_odd acc' hext
              exact ih (i + 1) false acc' next h_meas h_acc' h_eq
            | fail e =>
              exfalso
              change (RustM.fail e >>= _ : RustM _) = RustM.ok next at h_eq
              cases h_eq
          · have h_eq_b : (vi ==? x : RustM Bool) = RustM.ok false := by
              show pure (decide (vi = x)) = RustM.ok false
              rw [decide_eq_false h_vi_eq]
            rw [h_eq_b] at h_eq
            simp only [RustM_ok_bind, h_done_and, pure_bind, Bool.false_eq_true,
                       ↓reduceIte] at h_eq
            have h_unsize :
                (rust_primitives.unsize (RustArray.ofVec #v[vi] : RustArray u64 1)
                    : RustM (rust_primitives.sequence.Seq u64))
                  = RustM.ok ⟨#[vi], by decide⟩ := rfl
            rw [h_unsize] at h_eq
            simp only [RustM_ok_bind] at h_eq
            generalize hext : alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
                                (⟨#[vi], by decide⟩ : RustSlice u64) = r at h_eq
            cases r with
            | ok acc' =>
              simp only [RustM_ok_bind] at h_eq
              rw [h_add] at h_eq
              simp only [RustM_ok_bind] at h_eq
              have h_acc' : all_odd acc' :=
                extend_from_slice_one_odd acc vi h_acc h_vi_odd acc' hext
              exact ih (i + 1) false acc' next h_meas h_acc' h_eq
            | fail e =>
              exfalso
              change (RustM.fail e >>= _ : RustM _) = RustM.ok next at h_eq
              cases h_eq
      | true =>
        rw [hd] at h_eq
        simp only [rust_primitives.hax.logical_op.not, pure_bind,
                   Bool.not_true] at h_eq
        -- false && _ = false
        have h_and_false (b : Bool) :
            (rust_primitives.hax.logical_op.and false b : RustM Bool) = RustM.ok false := by
          show pure (false && b) = RustM.ok false
          simp
        -- Need: vi >=? x bound, then (false &&? __), then if false → fall through.
        -- The expression: let __dlift ← !?done(=false); let __dlift1 ← vi >=? x; let __dlift ← __dlift &&? __dlift1; if false then ... else (let __dlift ← vi ==? x; ...).
        -- So: vi >=? x is queried first (binding __dlift1), but the result is "false && x".
        by_cases h_vi_ge : x ≤ vi
        · have h_ge : (vi >=? x : RustM Bool) = RustM.ok true := by
            show pure (decide (x ≤ vi)) = RustM.ok true
            rw [decide_eq_true h_vi_ge]
          rw [h_ge] at h_eq
          simp only [RustM_ok_bind, h_and_false, pure_bind, Bool.false_eq_true,
                     ↓reduceIte] at h_eq
          -- Now: vi ==? x then done(=true) &&? __ then if ... else (extend [vi] then recurse)
          by_cases h_vi_eq : vi = x
          · -- vi == x ∧ done ⇒ skip branch
            have h_eq_b : (vi ==? x : RustM Bool) = RustM.ok true := by
              show pure (decide (vi = x)) = RustM.ok true
              rw [decide_eq_true h_vi_eq]
            rw [h_eq_b] at h_eq
            simp only [RustM_ok_bind,
                       rust_primitives.hax.logical_op.and, Bool.true_and,
                       pure_bind, ↓reduceIte] at h_eq
            rw [h_add] at h_eq
            simp only [RustM_ok_bind] at h_eq
            exact ih (i + 1) true acc next h_meas h_acc h_eq
          · -- vi != x: extend [vi] and recurse with done=true
            have h_eq_b : (vi ==? x : RustM Bool) = RustM.ok false := by
              show pure (decide (vi = x)) = RustM.ok false
              rw [decide_eq_false h_vi_eq]
            rw [h_eq_b] at h_eq
            simp only [RustM_ok_bind,
                       rust_primitives.hax.logical_op.and, Bool.and_false,
                       pure_bind, Bool.false_eq_true, ↓reduceIte] at h_eq
            have h_unsize :
                (rust_primitives.unsize (RustArray.ofVec #v[vi] : RustArray u64 1)
                    : RustM (rust_primitives.sequence.Seq u64))
                  = RustM.ok ⟨#[vi], by decide⟩ := rfl
            rw [h_unsize] at h_eq
            simp only [RustM_ok_bind] at h_eq
            generalize hext : alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
                                (⟨#[vi], by decide⟩ : RustSlice u64) = r at h_eq
            cases r with
            | ok acc' =>
              simp only [RustM_ok_bind] at h_eq
              rw [h_add] at h_eq
              simp only [RustM_ok_bind] at h_eq
              have h_acc' : all_odd acc' :=
                extend_from_slice_one_odd acc vi h_acc h_vi_odd acc' hext
              exact ih (i + 1) true acc' next h_meas h_acc' h_eq
            | fail e =>
              exfalso
              change (RustM.fail e >>= _ : RustM _) = RustM.ok next at h_eq
              cases h_eq
        · have h_ge : (vi >=? x : RustM Bool) = RustM.ok false := by
            show pure (decide (x ≤ vi)) = RustM.ok false
            rw [decide_eq_false h_vi_ge]
          rw [h_ge] at h_eq
          simp only [RustM_ok_bind, h_and_false, pure_bind, Bool.false_eq_true,
                     ↓reduceIte] at h_eq
          -- vi < x. done = true. Check vi ==? x = false (since vi < x ≠ x).
          have h_vi_ne_x : vi ≠ x := by
            intro h_eq2
            subst h_eq2; exact h_vi_ge (le_refl _)
          have h_eq_b : (vi ==? x : RustM Bool) = RustM.ok false := by
            show pure (decide (vi = x)) = RustM.ok false
            rw [decide_eq_false h_vi_ne_x]
          rw [h_eq_b] at h_eq
          simp only [RustM_ok_bind,
                     rust_primitives.hax.logical_op.and, Bool.and_false,
                     pure_bind, Bool.false_eq_true, ↓reduceIte] at h_eq
          have h_unsize :
              (rust_primitives.unsize (RustArray.ofVec #v[vi] : RustArray u64 1)
                  : RustM (rust_primitives.sequence.Seq u64))
                = RustM.ok ⟨#[vi], by decide⟩ := rfl
          rw [h_unsize] at h_eq
          simp only [RustM_ok_bind] at h_eq
          generalize hext : alloc.vec.Impl_2.extend_from_slice u64 alloc.alloc.Global acc
                              (⟨#[vi], by decide⟩ : RustSlice u64) = r at h_eq
          cases r with
          | ok acc' =>
            simp only [RustM_ok_bind] at h_eq
            rw [h_add] at h_eq
            simp only [RustM_ok_bind] at h_eq
            have h_acc' : all_odd acc' :=
              extend_from_slice_one_odd acc vi h_acc h_vi_odd acc' hext
            exact ih (i + 1) true acc' next h_meas h_acc' h_eq
          | fail e =>
            exfalso
            change (RustM.fail e >>= _ : RustM _) = RustM.ok next at h_eq
            cases h_eq

/-- `insert_asc` preserves `all_odd` when inserting an odd value. -/
private theorem insert_asc_preserves_all_odd
    (acc : alloc.vec.Vec u64 alloc.alloc.Global) (x : u64) (next : alloc.vec.Vec u64 alloc.alloc.Global)
    (h_acc : all_odd acc) (h_x : x.toNat % 2 = 1)
    (h_eq : clever_122_get_odd_collatz.insert_asc acc x = RustM.ok next) :
    all_odd next := by
  unfold clever_122_get_odd_collatz.insert_asc at h_eq
  -- Deref evaluates to ok ⟨acc.val, _⟩.
  have h_deref :
      (core_models.ops.deref.Deref.deref (alloc.vec.Vec u64 alloc.alloc.Global) acc
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global)) = RustM.ok acc := rfl
  -- New empty Vec.
  have h_new :
      (alloc.vec.Impl.new u64 rust_primitives.hax.Tuple0.mk
        : RustM (alloc.vec.Vec u64 alloc.alloc.Global))
      = RustM.ok ⟨#[], by decide⟩ := rfl
  rw [h_deref, h_new] at h_eq
  simp only [RustM_ok_bind] at h_eq
  -- Now h_eq : insert_asc_at ⟨acc.val, _⟩ x 0 false ⟨#[], _⟩ = ok next
  apply insert_asc_at_preserves_all_odd ⟨acc.val, acc.size_lt_usizeSize⟩ x
    (slice_all_odd_of_all_odd acc h_acc) h_x acc.val.size 0 false ⟨#[], by decide⟩ next
  · -- measure
    show acc.val.size - (0 : usize).toNat ≤ acc.val.size
    rw [show (0 : usize).toNat = 0 from rfl]; omega
  · exact all_odd_empty
  · exact h_eq

/-! ## Preservation of `all_odd` through `step_at` via fixpoint induction. -/

private theorem step_at_preserves_all_odd_motive
    (f : u64 → alloc.vec.Vec u64 alloc.alloc.Global →
        RustM (alloc.vec.Vec u64 alloc.alloc.Global)) : Prop :=
  ∀ (x : u64) (acc next : alloc.vec.Vec u64 alloc.alloc.Global),
    all_odd acc → f x acc = RustM.ok next → all_odd next

private theorem admissible_step_at_motive :
    Lean.Order.admissible step_at_preserves_all_odd_motive := by
  unfold step_at_preserves_all_odd_motive
  refine Lean.Order.admissible_pi_apply _ ?_
  intro x
  refine Lean.Order.admissible_pi_apply _ ?_
  intro acc
  refine Lean.Order.admissible_pi (P := fun (rm : RustM (alloc.vec.Vec u64 alloc.alloc.Global)) (next : alloc.vec.Vec u64 alloc.alloc.Global) =>
      all_odd acc → rm = RustM.ok next → all_odd next) ?_
  intro next
  -- need admissible (fun rm => all_odd acc → rm = ok next → all_odd next)
  intro c hc h
  intro h_acc h_eq
  -- `Option.admissible_eq_some` gives admissible (fun rm => rm = ok next → all_odd next)
  have hadm0 : Lean.Order.admissible (fun (rm : RustM (alloc.vec.Vec u64 alloc.alloc.Global)) =>
      rm = RustM.ok next → all_odd next) :=
    Option.admissible_eq_some (all_odd next) (.ok next)
  apply hadm0 c hc
  · intro rm hrm; exact h rm hrm h_acc
  · exact h_eq

private theorem step_at_preserves_all_odd
    (x : u64) (acc next : alloc.vec.Vec u64 alloc.alloc.Global)
    (h_acc : all_odd acc)
    (h_eq : clever_122_get_odd_collatz.step_at x acc = RustM.ok next) :
    all_odd next := by
  revert x acc next h_acc h_eq
  change step_at_preserves_all_odd_motive clever_122_get_odd_collatz.step_at
  apply clever_122_get_odd_collatz.step_at.fixpoint_induct
    (motive := step_at_preserves_all_odd_motive)
    admissible_step_at_motive
  intro f IH
  -- IH : step_at_preserves_all_odd_motive f
  -- Goal: motive (body f)
  -- Body: λ x acc, do { let __do_lift ← x ==? 1; if then ... else if (x % 2 == 1) then ... else ...}
  unfold step_at_preserves_all_odd_motive at IH ⊢
  intro x acc next h_acc h_eq
  -- Reduce the body step by step.
  -- x ==? 1 = pure (decide (x = 1))
  by_cases hx1 : x = 1
  · subst hx1
    -- decide ((1 : u64) = 1) = true
    have h1 : (((1 : u64) ==? (1 : u64)) : RustM Bool) = RustM.ok true := by
      show pure (decide ((1 : u64) = 1)) = RustM.ok true
      simp
    simp only [h1, RustM_ok_bind, pure_bind, ↓reduceIte] at h_eq
    have h_deref :
        (core_models.ops.deref.Deref.deref (alloc.vec.Vec u64 alloc.alloc.Global) acc
          : RustM (alloc.vec.Vec u64 alloc.alloc.Global)) = RustM.ok acc := rfl
    rw [h_deref] at h_eq
    simp only [RustM_ok_bind] at h_eq
    -- now: let __do_lift ← contains_at ⟨acc.val, _⟩ 1 0; ...
    -- contains_at returns ok b for some bool b. Case on b.
    generalize hc : clever_122_get_odd_collatz.contains_at acc 1 0 = r at h_eq
    cases r with
    | ok b =>
      simp only [RustM_ok_bind] at h_eq
      cases b with
      | true =>
        simp only [rust_primitives.hax.logical_op.not, pure_bind,
                   Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h_eq
        -- h_eq : pure acc = ok next, so next = acc
        injection h_eq with h_eq2
        injection h_eq2 with h_eq3
        subst h_eq3
        exact h_acc
      | false =>
        simp only [rust_primitives.hax.logical_op.not, pure_bind,
                   Bool.not_false, ↓reduceIte] at h_eq
        -- h_eq : insert_asc acc 1 = ok next
        exact insert_asc_preserves_all_odd acc 1 next h_acc (by decide) h_eq
    | fail e =>
      exfalso
      change (RustM.fail e >>= _ : RustM _) = RustM.ok next at h_eq
      cases h_eq
  · have h1 : ((x ==? (1 : u64)) : RustM Bool) = RustM.ok false := by
      show pure (decide (x = 1)) = RustM.ok false
      rw [decide_eq_false hx1]
    simp only [h1, RustM_ok_bind, pure_bind, Bool.false_eq_true, ↓reduceIte] at h_eq
    -- now: let __do_lift ← x %? 2; let __do_lift ← __do_lift ==? 1; ...
    have h_mod : ((x %? (2 : u64)) : RustM u64) = RustM.ok (x % 2) := by
      show (rust_primitives.ops.arith.Rem.rem x 2 : RustM u64) = _
      show (if (2 : u64) = 0 then (.fail _ : RustM u64) else pure (x % 2)) = _
      rfl
    rw [h_mod] at h_eq
    simp only [RustM_ok_bind] at h_eq
    -- Now case on x % 2 = 1 vs x % 2 = 0.
    by_cases hx_odd : x % 2 = 1
    · -- odd branch
      have h_eq_b : ((x % 2) ==? (1 : u64) : RustM Bool) = RustM.ok true := by
        show pure (decide (x % 2 = 1)) = RustM.ok true
        rw [decide_eq_true hx_odd]
      rw [h_eq_b] at h_eq
      simp only [RustM_ok_bind, pure_bind, ↓reduceIte] at h_eq
      -- x is odd; x.toNat % 2 = 1
      have h_x_toNat_odd : x.toNat % 2 = 1 := by
        have : (x % 2).toNat = 1 := by
          rw [hx_odd]; rfl
        have h_x_mod_eq : (x.toNat % 2) = 1 := by
          have := UInt64.toNat_mod (a := x) (b := 2)
          simp at this
          rw [this]; exact this ▸ (this.symm.trans (by rw [hx_odd]; rfl))
        exact h_x_mod_eq
      sorry
    · -- even branch: recurse on x/2
      have h_x_mod0 : x % 2 = 0 := by
        have : x % 2 < 2 := by
          have := UInt64.toNat_mod (a := x) (b := 2)
          -- Need bound; alternative: case on `x % 2`.
          sorry
        sorry
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
