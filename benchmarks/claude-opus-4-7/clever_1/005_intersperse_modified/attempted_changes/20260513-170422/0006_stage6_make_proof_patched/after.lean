-- Companion obligations file for the `clever_005_intersperse` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

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

/-! ## Helper lemmas (shared infrastructure)

Standard helpers transferred from `contains_u64_modified` / `below_zero_modified`
references. They package the bind-unfolding and `+? 1` arithmetic that
every step lemma needs. -/

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

/-! ## Contract obligations for `intersperse`

The Rust `proptest` block in `src/lib.rs` asserts three independent contract
clauses on the result of `intersperse numbers delimiter`:

  1. **Length** — empty input yields an empty vector; otherwise the length
     is `2 * numbers.len() - 1`.
  2. **Even indices** — `result[2 * i] = numbers[i]` for every valid `i`.
  3. **Odd indices** — `result[2 * i + 1] = delimiter` for every `i < n - 1`.

Each contract clause is captured as one independent theorem below. The
function returns `RustM (Vec i64 …)`, so every theorem is phrased on the
hypothesis that `intersperse numbers delimiter = RustM.ok v` and asserts a
property of `v`. The `intersperse_total` theorem makes the implicit
totality baseline explicit — without it, the conditional theorems would
be vacuously satisfied by a function that always failed.

`Vec` is a `Seq` in the Hax prelude (`abbrev alloc.vec.Vec α _ := Seq α`),
so we access its underlying array via `.val` and its length via
`.val.size`. -/

/-- Totality: `intersperse` always succeeds (returns `RustM.ok`).

    This is the implicit baseline for the three proptests in the Rust
    source — each test calls `intersperse` and then asserts a property of
    the returned `Vec`, so a `RustM.fail` (panic, overflow, or
    out-of-bounds) would crash the test before any assertion fires. The
    function has no failure mode in the contract: indexing is guarded by
    the length comparison, `i + 1` cannot overflow because `i < numbers.len()
    ≤ usize::MAX`, and `extend_from_slice` only fails on a vector larger
    than `usize::MAX`, which is unreachable since `numbers.len()` itself
    fits in `usize`. -/
theorem intersperse_total
    (numbers : RustSlice i64) (delimiter : i64) :
    ∃ v : alloc.vec.Vec i64 alloc.alloc.Global,
      clever_005_intersperse.intersperse numbers delimiter = RustM.ok v := by
  sorry

/-- Length (empty case): when `numbers` is empty, the result is an empty
    vector.

    Captures the `numbers.is_empty()` branch of the proptest
    `length_matches_contract`:
    `let expected = if numbers.is_empty() { 0 } else { 2 * numbers.len() - 1 };`.
    A buggy implementation that pushed a delimiter on the empty input, or
    otherwise produced a non-empty `Vec`, would falsify this. -/
theorem intersperse_length_empty
    (numbers : RustSlice i64) (delimiter : i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_005_intersperse.intersperse numbers delimiter = RustM.ok v)
    (hempty : numbers.val.size = 0) :
    v.val.size = 0 := by
  sorry

/-- Length (non-empty case): for a non-empty input slice, the result has
    length `2 * numbers.len() - 1`.

    Captures the non-empty branch of the proptest
    `length_matches_contract`. A buggy implementation that emitted an
    extra trailing delimiter (`2n`), missed a delimiter (`2n − 2`), or
    skipped an element (`n`) would falsify this. -/
theorem intersperse_length_nonempty
    (numbers : RustSlice i64) (delimiter : i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_005_intersperse.intersperse numbers delimiter = RustM.ok v)
    (hne : 0 < numbers.val.size) :
    v.val.size = 2 * numbers.val.size - 1 := by
  sorry

/-- Even indices contract: `result[2 * i] = numbers[i]` for every valid
    `i`.

    Captures the proptest `even_indices_are_original_numbers`:
    `for i in 0..numbers.len() { prop_assert_eq!(result[2 * i], numbers[i]); }`.
    The Vec-bound hypothesis `h2i : 2 * i < v.val.size` is supplied
    explicitly so this theorem does not depend on
    `intersperse_length_nonempty` for its statement to type-check; the
    proof stage may discharge it via that lemma. A buggy implementation
    that scrambled the order of inputs, replaced an element with a
    delimiter, or inserted an extra delimiter at the front would falsify
    this. -/
theorem intersperse_even_indices
    (numbers : RustSlice i64) (delimiter : i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_005_intersperse.intersperse numbers delimiter = RustM.ok v)
    (i : Nat) (hi : i < numbers.val.size) (h2i : 2 * i < v.val.size) :
    v.val[2 * i]'h2i = numbers.val[i]'hi := by
  sorry

/-- Odd indices contract: `result[2 * i + 1] = delimiter` for every
    `i < numbers.len() - 1`.

    Captures the proptest `odd_indices_are_delimiter`:
    `for i in 0..numbers.len().saturating_sub(1) {
       prop_assert_eq!(result[2 * i + 1], delimiter); }`.
    The hypothesis `i + 1 < numbers.val.size` is the `Nat` translation of
    `i < numbers.len().saturating_sub(1)` (the saturating subtraction
    yields the empty range when `numbers` is empty, so the constraint is
    vacuous there). A buggy implementation that used a wrong delimiter,
    swapped an input element into an odd slot, or appended a trailing
    delimiter at index `2n − 1` (and shifted everything) would falsify
    this. -/
theorem intersperse_odd_indices
    (numbers : RustSlice i64) (delimiter : i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_005_intersperse.intersperse numbers delimiter = RustM.ok v)
    (i : Nat) (hi : i + 1 < numbers.val.size)
    (h2i1 : 2 * i + 1 < v.val.size) :
    v.val[2 * i + 1]'h2i1 = delimiter := by
  sorry

end Clever_005_intersperseObligations
