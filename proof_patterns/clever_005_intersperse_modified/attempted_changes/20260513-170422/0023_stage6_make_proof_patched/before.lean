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

/-! ## Step lemmas for `intersperse_at`

The function's body has three "shapes":
  - out-of-bounds (`i.toNat ≥ size`): returns the accumulator unchanged
  - in-bounds with `i = 0`: appends `[numbers[0]]` and recurses at `i + 1`
  - in-bounds with `i > 0`: appends `[delimiter, numbers[i]]` and recurses at `i + 1`

Each lemma packages one shape so the strong-induction step can rewrite the
goal directly. They follow the `unfold + simp only` recipe from the
`contains_u64` reference. -/

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

/-! The step lemmas peel one iteration of `intersperse_at`'s `partial_fixpoint`
body. They are stated for arbitrary `i : usize` (rather than literal `0` / `1`)
so the strong induction can apply them at each step.

The `i = 0` and `i > 0` branches differ only in the chunk size, so we package
the no-overflow side conditions explicitly. Each lemma is structurally
identical to the `_recurse` lemma in `contains_u64_modified`. -/

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
  -- After the basic simps, the residual goal contains the `unsize >>=
  -- extend_from_slice >>= ...` chain. Unfold those definitions and use
  -- the size precondition to discharge.
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

/-- Step at `i > 0`, in bounds: when `0 < i.toNat < numbers.val.size`, the
    append doesn't overflow, and `i + 1` doesn't overflow, `intersperse_at`
    at `i` recurses with `i + 1` and the accumulator extended by
    `[delimiter, numbers.val[i.toNat]]`. -/
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
  -- Inner branch: i ≠ 0, so we take the `else` branch with the 2-element chunk.
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

/-! ## Strong-induction helper for the non-empty obligations

The three remaining obligations (length-nonempty, even-indices, odd-indices)
all reduce to a single invariant on the recursion of `intersperse_at`. We
state that invariant here as `intersperse_at_full_invariant`.

The invariant says: starting from `(i, acc)` with `acc` already a valid
"partial output up to index `i.toNat`", if `intersperse_at` succeeds and
returns `v`, then `v` is a valid "full output up to `numbers.val.size`".

**Structural unblock for the surviving `sorry`:** the proof is a strong
induction on `numbers.val.size - i.toNat` using the three step lemmas above
(`intersperse_at_oob`, `intersperse_at_step_zero`, `intersperse_at_step_pos`).
The induction step needs an auxiliary "step-success extraction" lemma:

```
private theorem intersperse_at_step_extract
    (numbers : RustSlice i64) (delimiter : i64) (i : usize)
    (acc v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi : i.toNat < numbers.val.size)
    (hres : intersperse_at numbers delimiter i acc = RustM.ok v) :
  (i.toNat = 0 ∧ ∃ h_no : acc.val.size + 1 < 2 ^ 64,
     intersperse_at numbers delimiter (i + 1)
       (acc_push_one acc (numbers.val[0]'hi) h_no) = RustM.ok v) ∨
  (0 < i.toNat ∧ ∃ (h_no : acc.val.size + 2 < 2 ^ 64) (h_i1 : i.toNat + 1 < 2^64),
     intersperse_at numbers delimiter (i + 1)
       (acc_push_two acc delimiter (numbers.val[i.toNat]'hi) h_no) = RustM.ok v)
```

This extraction lemma converts `hres : ok v` into the preconditions of
`intersperse_at_step_zero` / `intersperse_at_step_pos`, then applies them to
get a smaller recursive `intersperse_at = ok v` for the inductive step.

Proving the extraction lemma requires unfolding the function body the same
way the step lemmas do, but in REVERSE: from `ok v` deduce that the inner
`extend_from_slice` and `i +? 1` calls succeeded (i.e., the dif-positive
branches were taken). This is the analogue of `i64_sub_extract` in
`proof_patterns/000_has_close_elements_modified` (which extracts
`¬ subOverflow` from `ok y`).

Once that extraction lemma is available, the strong-induction proof of
`intersperse_at_full_invariant` is mechanical: case-split on `i.toNat ≥ n`
(use `oob`) vs `i.toNat < n` (use `step_extract` then IH on `m - 1`). -/

private theorem intersperse_at_full_invariant
    (numbers : RustSlice i64) (delimiter : i64) :
    ∀ (m : Nat) (i : usize) (acc v : alloc.vec.Vec i64 alloc.alloc.Global),
      numbers.val.size - i.toNat ≤ m →
      i.toNat ≤ numbers.val.size →
      acc.val.size = (if i.toNat = 0 then 0 else 2 * i.toNat - 1) →
      (∀ k, k < i.toNat → ∀ (h2k : 2 * k < acc.val.size)
              (hk : k < numbers.val.size),
            acc.val[2 * k]'h2k = numbers.val[k]'hk) →
      (∀ k, k + 1 < i.toNat → ∀ (h2k1 : 2 * k + 1 < acc.val.size),
            acc.val[2 * k + 1]'h2k1 = delimiter) →
      clever_005_intersperse.intersperse_at numbers delimiter i acc = RustM.ok v →
      v.val.size = (if numbers.val.size = 0 then 0 else 2 * numbers.val.size - 1) ∧
      (∀ k, k < numbers.val.size → ∀ (h2k : 2 * k < v.val.size)
              (hk : k < numbers.val.size),
            v.val[2 * k]'h2k = numbers.val[k]'hk) ∧
      (∀ k, k + 1 < numbers.val.size → ∀ (h2k1 : 2 * k + 1 < v.val.size),
            v.val[2 * k + 1]'h2k1 = delimiter) := by
  intro m
  induction m with
  | zero =>
    -- Base case: m = 0 ⇒ i.toNat ≥ n. Function is OOB, so v = acc, and
    -- the input invariant transfers directly to v.
    intro i acc v hm hin h_acc_size h_acc_even h_acc_odd hres
    have h_i_ge_n : i.toNat ≥ numbers.val.size := by omega
    have h_i_eq_n : i.toNat = numbers.val.size := by omega
    rw [intersperse_at_oob numbers delimiter i acc h_i_ge_n] at hres
    injection hres with h1
    injection h1 with h_v_eq
    subst h_v_eq
    refine ⟨?_, ?_, ?_⟩
    · -- Size: acc.val.size = (if i = 0 then 0 else 2*i - 1) and i = n.
      rw [h_acc_size, h_i_eq_n]
    · -- Even: acc satisfies even-content up to i = n.
      intro k hk h2k hk_n
      rw [h_i_eq_n] at h_acc_even
      exact h_acc_even k hk h2k hk_n
    · -- Odd: acc satisfies odd-content up to i = n.
      intro k hk h2k1
      rw [h_i_eq_n] at h_acc_odd
      exact h_acc_odd k hk h2k1
  | succ m ih =>
    intro i acc v hm hin h_acc_size h_acc_even h_acc_odd hres
    -- Step case: either i.toNat ≥ n (use base reasoning) or i.toNat < n
    -- (use step-extract lemma + IH).
    by_cases h_i_ge : i.toNat ≥ numbers.val.size
    · -- OOB branch: same as base case.
      have h_i_eq_n : i.toNat = numbers.val.size := by omega
      rw [intersperse_at_oob numbers delimiter i acc h_i_ge] at hres
      injection hres with h1
      injection h1 with h_v_eq
      subst h_v_eq
      refine ⟨?_, ?_, ?_⟩
      · rw [h_acc_size, h_i_eq_n]
      · intro k hk h2k hk_n
        rw [h_i_eq_n] at h_acc_even
        exact h_acc_even k hk h2k hk_n
      · intro k hk h2k1
        rw [h_i_eq_n] at h_acc_odd
        exact h_acc_odd k hk h2k1
    · -- In-bounds branch: needs the step-extract lemma (documented above)
      -- to convert `hres : ok v` into the no-overflow preconditions of
      -- `intersperse_at_step_zero` / `intersperse_at_step_pos`, then apply
      -- the IH on the resulting smaller measure.
      -- This is the structural sorry: the extract lemma is the missing piece.
      sorry

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
  unfold clever_005_intersperse.intersperse at hres
  -- Reduce the do-block: `Impl.new` returns `pure ⟨#[], _⟩`, the bind feeds
  -- this empty Vec as `acc` to `intersperse_at`, and `intersperse_at_oob`
  -- closes the recursion at `i = 0` since `numbers.val.size = 0`.
  simp only [alloc.vec.Impl.new, pure_bind] at hres
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have hi_ge : numbers.val.size ≤ (0 : usize).toNat := by
    rw [h_zero_toNat]; omega
  rw [intersperse_at_oob numbers delimiter 0 _ hi_ge] at hres
  -- hres : RustM.ok ⟨#[], _⟩ = RustM.ok v
  injection hres with h1
  injection h1 with h2
  rw [← h2]
  -- Goal: (List.nil.toArray).size = 0
  rfl

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
  unfold clever_005_intersperse.intersperse at hres
  simp only [alloc.vec.Impl.new, pure_bind] at hres
  -- Apply the full-invariant helper at i = 0, acc = empty Vec.
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_inv := intersperse_at_full_invariant numbers delimiter
    numbers.val.size (0 : usize)
    (⟨(List.nil : List i64).toArray, by decide⟩ : alloc.vec.Vec i64 alloc.alloc.Global)
    v
    (by rw [h_zero_toNat]; omega)
    (by rw [h_zero_toNat]; omega)
    (by show (List.nil : List i64).toArray.size
              = (if (0 : usize).toNat = 0 then 0 else _)
        rw [h_zero_toNat]; rfl)
    (by intro k hk; rw [h_zero_toNat] at hk; omega)
    (by intro k hk; rw [h_zero_toNat] at hk; omega)
    hres
  rcases h_inv with ⟨h_size, _, _⟩
  rw [h_size]
  have h_ne : numbers.val.size ≠ 0 := Nat.ne_of_gt hne
  rw [if_neg h_ne]

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
  unfold clever_005_intersperse.intersperse at hres
  simp only [alloc.vec.Impl.new, pure_bind] at hres
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_inv := intersperse_at_full_invariant numbers delimiter
    numbers.val.size (0 : usize)
    (⟨(List.nil : List i64).toArray, by decide⟩ : alloc.vec.Vec i64 alloc.alloc.Global)
    v
    (by rw [h_zero_toNat]; omega)
    (by rw [h_zero_toNat]; omega)
    (by show (List.nil : List i64).toArray.size
              = (if (0 : usize).toNat = 0 then 0 else _)
        rw [h_zero_toNat]; rfl)
    (by intro k hk; rw [h_zero_toNat] at hk; omega)
    (by intro k hk; rw [h_zero_toNat] at hk; omega)
    hres
  rcases h_inv with ⟨_, h_even, _⟩
  exact h_even i hi h2i hi

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
theorem intersperse_odd_indices_HELPER_PLACEHOLDER
===
theorem intersperse_even_indices
    (numbers : RustSlice i64) (delimiter : i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_005_intersperse.intersperse numbers delimiter = RustM.ok v)
    (i : Nat) (hi : i < numbers.val.size) (h2i : 2 * i < v.val.size) :
    v.val[2 * i]'h2i = numbers.val[i]'hi := by
  unfold clever_005_intersperse.intersperse at hres
  simp only [alloc.vec.Impl.new, pure_bind] at hres
  have h_zero_toNat : (0 : usize).toNat = 0 := rfl
  have h_inv := intersperse_at_full_invariant numbers delimiter
    numbers.val.size (0 : usize)
    (⟨(List.nil : List i64).toArray, by decide⟩ : alloc.vec.Vec i64 alloc.alloc.Global)
    v
    (by rw [h_zero_toNat]; omega)
    (by rw [h_zero_toNat]; omega)
    (by show (List.nil : List i64).toArray.size
              = (if (0 : usize).toNat = 0 then 0 else _)
        rw [h_zero_toNat]; rfl)
    (by intro k hk; rw [h_zero_toNat] at hk; omega)
    (by intro k hk; rw [h_zero_toNat] at hk; omega)
    hres
  rcases h_inv with ⟨_, h_even, _⟩
  exact h_even i hi h2i hi

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
theorem intersperse_odd_indices_HELPER_PLACEHOLDER

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
