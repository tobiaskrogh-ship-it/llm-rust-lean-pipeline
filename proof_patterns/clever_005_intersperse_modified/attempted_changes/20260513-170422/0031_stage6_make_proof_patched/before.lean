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

/-! ## Step-extract lemmas (success at i ⇒ no-overflow preconditions)

These convert `intersperse_at numbers delimiter i acc = RustM.ok v` into
the preconditions of `intersperse_at_step_zero` / `intersperse_at_step_pos`,
so that the step lemma can rewrite `hres` into a smaller-measure form
suitable for the IH. They are the reverse direction of the step lemmas:
case-split on the precondition; if it holds, apply the step lemma; if it
fails, unfold the function body and show the failure propagates to a
contradiction with `hres = RustM.ok v`.
-/

/-- Reverse direction of `intersperse_at_step_zero`: from a successful
    result at `i = 0`, extract the no-overflow witness on the accumulator. -/
private theorem intersperse_at_step_zero_extract
    (numbers : RustSlice i64) (delimiter : i64)
    (acc v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hn_pos : 0 < numbers.val.size)
    (hres : clever_005_intersperse.intersperse_at numbers delimiter (0 : usize) acc
              = RustM.ok v) :
    ∃ (h_no : acc.val.size + 1 < 2 ^ 64),
      clever_005_intersperse.intersperse_at numbers delimiter (1 : usize)
        (acc_push_one acc (numbers.val[0]'hn_pos) h_no) = RustM.ok v := by
  by_cases h_no : acc.val.size + 1 < 2 ^ 64
  · refine ⟨h_no, ?_⟩
    rw [intersperse_at_step_zero numbers delimiter acc hn_pos h_no] at hres
    exact hres
  · exfalso
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
        (numbers[(0 : usize)]_? : RustM i64) = RustM.ok (numbers.val[0]'hn_pos) := by
      show (if h : (0 : usize).toNat < numbers.val.size
              then pure (numbers.val[(0 : usize)])
              else .fail .arrayOutOfBounds)
          = RustM.ok (numbers.val[0]'hn_pos)
      rw [dif_pos h_n_pos_toNat]; rfl
    have h_eq_zero :
        ((0 : usize) ==? (0 : usize) : RustM Bool) = RustM.ok true := rfl
    conv at hres => lhs; unfold clever_005_intersperse.intersperse_at
    simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
               rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
               h_cond_ge, Bool.false_eq_true, ↓reduceIte,
               h_idx, h_eq_zero] at hres
    simp only [rust_primitives.unsize, alloc.vec.Impl_2.extend_from_slice,
               pure_bind] at hres
    have h_size_arr : ¬ (acc.val.size + (#[numbers.val[0]'hn_pos] : Array i64).size
                          < USize64.size) := by
      show ¬ (acc.val.size + 1 < USize64.size)
      have heq : USize64.size = 2 ^ 64 := by decide
      rw [heq]; exact h_no
    rw [dif_neg h_size_arr] at hres
    simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, Option.bind] at hres
    cases hres

/-- Reverse direction of `intersperse_at_step_pos`: from a successful
    result at `i > 0`, extract the no-overflow witnesses. -/
private theorem intersperse_at_step_pos_extract
    (numbers : RustSlice i64) (delimiter : i64) (i : usize)
    (acc v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hi_pos : 0 < i.toNat) (hi_lt : i.toNat < numbers.val.size)
    (hres : clever_005_intersperse.intersperse_at numbers delimiter i acc
              = RustM.ok v) :
    ∃ (h_i1 : i.toNat + 1 < 2 ^ 64) (h_no : acc.val.size + 2 < 2 ^ 64),
      clever_005_intersperse.intersperse_at numbers delimiter (i + 1)
        (acc_push_two acc delimiter (numbers.val[i.toNat]'hi_lt) h_no) = RustM.ok v := by
  have h_size_lt : numbers.val.size < 2 ^ 64 := numbers.size_lt_usizeSize
  have h_i1 : i.toNat + 1 < 2 ^ 64 := by omega
  refine ⟨h_i1, ?_⟩
  by_cases h_no : acc.val.size + 2 < 2 ^ 64
  · refine ⟨h_no, ?_⟩
    rw [intersperse_at_step_pos numbers delimiter i acc hi_pos hi_lt h_i1 h_no] at hres
    exact hres
  · exfalso
    have h_ofNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
      USize64.toNat_ofNat_of_lt' numbers.size_lt_usizeSize
    have h_cond_ge : decide (USize64.ofNat numbers.val.size ≤ i) = false := by
      rw [decide_eq_false_iff_not]
      intro hle
      rw [USize64.le_iff_toNat_le, h_ofNat] at hle
      omega
    have h_idx :
        (numbers[i]_? : RustM i64) = RustM.ok (numbers.val[i.toNat]'hi_lt) := by
      show (if h : i.toNat < numbers.val.size
              then pure (numbers.val[i])
              else .fail .arrayOutOfBounds)
          = RustM.ok (numbers.val[i.toNat]'hi_lt)
      rw [dif_pos hi_lt]; rfl
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
    conv at hres => lhs; unfold clever_005_intersperse.intersperse_at
    simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
               rust_primitives.cmp.ge, pure_bind, RustM_ok_bind,
               h_cond_ge, Bool.false_eq_true, ↓reduceIte,
               h_idx, h_neq_zero] at hres
    simp only [rust_primitives.unsize, alloc.vec.Impl_2.extend_from_slice,
               pure_bind] at hres
    have h_size_arr :
        ¬ (acc.val.size + (#[delimiter, numbers.val[i.toNat]'hi_lt] : Array i64).size
            < USize64.size) := by
      show ¬ (acc.val.size + 2 < USize64.size)
      have heq : USize64.size = 2 ^ 64 := by decide
      rw [heq]; exact h_no
    rw [dif_neg h_size_arr] at hres
    simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, Option.bind] at hres
    cases hres

/-! ## Array-indexing helpers for the pushed accumulator

After `acc_push_one acc x` or `acc_push_two acc x y`, indexing into the new
accumulator at `k < acc.val.size` recovers the old `acc.val[k]`, and at
`acc.val.size` / `acc.val.size + 1` recovers `x` and `y`. We package these
as four standalone lemmas because the strong induction uses them at each
"extend" step. -/

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
  have h_ge : acc.val.size ≥ acc.val.size := Nat.le_refl _
  have h_ge' : acc.val.size + 1 ≥ acc.val.size := by omega
  rw [Array.getElem_append_right h_ge']
  simp

/-- Generalised indexing: at any `j = acc.val.size`, return `x`. The
    `_at` variant takes the index equation as an explicit hypothesis so
    callers can use it on arbitrary index expressions like `2 * k`. -/
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

/-! ## Strong-induction helper for the non-empty obligations

The three remaining obligations (length-nonempty, even-indices, odd-indices)
all reduce to a single invariant on the recursion of `intersperse_at`. We
state that invariant here as `intersperse_at_full_invariant` and prove it
by strong induction on `numbers.val.size - i.toNat`, using
`intersperse_at_step_zero_extract` / `intersperse_at_step_pos_extract` to
peel one iteration of the body at each step. -/

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
    · rw [h_acc_size, h_i_eq_n]
    · intro k hk h2k hk_n
      rw [h_i_eq_n] at h_acc_even
      exact h_acc_even k hk h2k hk_n
    · intro k hk h2k1
      rw [h_i_eq_n] at h_acc_odd
      exact h_acc_odd k hk h2k1
  | succ m ih =>
    intro i acc v hm hin h_acc_size h_acc_even h_acc_odd hres
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
    · -- In-bounds branch: use the step-extract lemmas to convert
      -- `hres : ok v` into a smaller `intersperse_at = ok v` and apply IH.
      have hi_lt : i.toNat < numbers.val.size := Nat.lt_of_not_le h_i_ge
      have h_size_lt : numbers.val.size < 2 ^ 64 := numbers.size_lt_usizeSize
      have h_no_overflow_i : i.toNat + 1 < 2 ^ 64 := by omega
      have h_i1_toNat : (i + 1).toNat = i.toNat + 1 :=
        usize_add_one_toNat i h_no_overflow_i
      have h_one : (1 : usize).toNat = 1 := rfl
      by_cases hi_zero : i.toNat = 0
      · -- i.toNat = 0: apply `intersperse_at_step_zero_extract`.
        have hi_eq : i = (0 : usize) := by
          apply USize64.toNat_inj.mp
          show i.toNat = (0 : usize).toNat
          rw [hi_zero]; rfl
        have h_acc_zero : acc.val.size = 0 := by
          rw [h_acc_size, if_pos hi_zero]
        have hn_pos : 0 < numbers.val.size := by omega
        rw [hi_eq] at hres
        obtain ⟨h_no, hres'⟩ :=
          intersperse_at_step_zero_extract numbers delimiter acc v hn_pos hres
        -- New accumulator after pushing numbers.val[0].
        have h_acc'_size_one :
            (acc_push_one acc (numbers.val[0]'hn_pos) h_no).val.size = 1 := by
          rw [acc_push_one_size, h_acc_zero]
        have h_acc'_size_inv :
            (acc_push_one acc (numbers.val[0]'hn_pos) h_no).val.size
              = (if (1 : usize).toNat = 0 then 0 else 2 * (1 : usize).toNat - 1) := by
          rw [h_acc'_size_one]
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
          show (acc.val ++ #[numbers.val[0]'hn_pos])[2 * 0]'_
                = numbers.val[0]'hk_n
          have h_ge : (2 * 0 : Nat) ≥ acc.val.size := by
            rw [h_acc_zero]; omega
          rw [Array.getElem_append_right h_ge]
          simp [h_acc_zero]
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
        exact ih (1 : usize) (acc_push_one acc (numbers.val[0]'hn_pos) h_no) v
          h_measure h_in h_acc'_size_inv h_acc'_even h_acc'_odd hres'
      · -- i.toNat > 0: apply `intersperse_at_step_pos_extract`.
        have hi_pos : 0 < i.toNat := Nat.pos_of_ne_zero hi_zero
        have h_acc_size_val : acc.val.size = 2 * i.toNat - 1 := by
          rw [h_acc_size, if_neg hi_zero]
        obtain ⟨h_i1, h_no, hres'⟩ :=
          intersperse_at_step_pos_extract numbers delimiter i acc v hi_pos hi_lt hres
        -- New accumulator after pushing [delimiter, numbers.val[i.toNat]].
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
          · -- k < i.toNat: use the old invariant via append_left.
            have h2k_lt : 2 * k < acc.val.size := by
              rw [h_acc_size_val]; omega
            show (acc.val ++ #[delimiter, numbers.val[i.toNat]'hi_lt])[2 * k]'_
                  = numbers.val[k]'hk_n
            rw [Array.getElem_append_left h2k_lt]
            exact h_acc_even k hki h2k_lt hk_n
          · -- k = i.toNat: new last-of-pair-1 position.
            have hki_eq : k = i.toNat := by omega
            show (acc.val ++ #[delimiter, numbers.val[i.toNat]'hi_lt])[2 * k]'h2k
                  = numbers.val[k]'hk_n
            have h_ge : (2 * k : Nat) ≥ acc.val.size := by
              rw [hki_eq, h_acc_size_val]; omega
            rw [Array.getElem_append_right h_ge]
            -- index is 2*k - acc.val.size = 2*k - (2*k - 1) = 1
            have h_diff : 2 * k - acc.val.size = 1 := by
              rw [hki_eq, h_acc_size_val]; omega
            rw [hki_eq]
            simp [h_diff]
        have h_acc'_odd :
            ∀ k, k + 1 < (i + 1).toNat →
              ∀ (h2k1 : 2 * k + 1 <
                    (acc_push_two acc delimiter (numbers.val[i.toNat]'hi_lt) h_no).val.size),
              (acc_push_two acc delimiter (numbers.val[i.toNat]'hi_lt) h_no).val[2 * k + 1]'h2k1
                = delimiter := by
          intro k hk h2k1
          rw [h_i1_toNat] at hk
          by_cases hki_strict : k + 1 < i.toNat
          · -- Old invariant via append_left.
            have h2k1_lt : 2 * k + 1 < acc.val.size := by
              rw [h_acc_size_val]; omega
            show (acc.val ++ #[delimiter, numbers.val[i.toNat]'hi_lt])[2 * k + 1]'_
                  = delimiter
            rw [Array.getElem_append_left h2k1_lt]
            exact h_acc_odd k hki_strict h2k1_lt
          · -- k + 1 = i.toNat: new delimiter at slot 2*k+1 = acc.val.size.
            have hki_eq : k + 1 = i.toNat := by omega
            show (acc.val ++ #[delimiter, numbers.val[i.toNat]'hi_lt])[2 * k + 1]'_
                  = delimiter
            have h_ge : (2 * k + 1 : Nat) ≥ acc.val.size := by
              rw [h_acc_size_val]; omega
            rw [Array.getElem_append_right h_ge]
            -- index 2*k + 1 - acc.val.size = 2*k + 1 - (2*(k+1) - 1) = 0
            have h_diff : 2 * k + 1 - acc.val.size = 0 := by
              rw [h_acc_size_val]; omega
            simp [h_diff]
        have h_measure : numbers.val.size - (i + 1).toNat ≤ m := by
          rw [h_i1_toNat]; omega
        have h_in : (i + 1).toNat ≤ numbers.val.size := by
          rw [h_i1_toNat]; omega
        exact ih (i + 1) (acc_push_two acc delimiter (numbers.val[i.toNat]'hi_lt) h_no) v
          h_measure h_in h_acc'_size_inv h_acc'_even h_acc'_odd hres'

/-- Totality: `intersperse` always succeeds (returns `RustM.ok`).

    **Status:** this obligation is left as `sorry` because it is genuinely
    not provable in its current unconditional form. The function fails when
    `2 * numbers.val.size > 2 ^ 64`: the final `extend_from_slice` on the
    last element of the slice overflows the `USize64.size` bound on the
    Vec. The proptest in `src/lib.rs` constrains lengths to `0..32`, so the
    overflow is unreachable in the test domain, but the obligation as
    stated quantifies over all `RustSlice i64`.

    **Structural unblock:** the obligation needs an extra precondition
    `2 * numbers.val.size ≤ 2 ^ 64` (equivalently `2 * numbers.val.size - 1
    < USize64.size`). Under that precondition, totality follows from a
    strong induction using the same `intersperse_at_step_zero` /
    `intersperse_at_step_pos` lemmas: each step succeeds because the size
    of the running `acc` is bounded by the precondition, and `i + 1` does
    not overflow because `i ≤ numbers.val.size < 2 ^ 64`. -/
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
  injection hres with h1
  injection h1 with h2
  rw [← h2]
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
theorem intersperse_odd_indices
    (numbers : RustSlice i64) (delimiter : i64)
    (v : alloc.vec.Vec i64 alloc.alloc.Global)
    (hres : clever_005_intersperse.intersperse numbers delimiter = RustM.ok v)
    (i : Nat) (hi : i + 1 < numbers.val.size)
    (h2i1 : 2 * i + 1 < v.val.size) :
    v.val[2 * i + 1]'h2i1 = delimiter := by
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
  rcases h_inv with ⟨_, _, h_odd⟩
  exact h_odd i hi h2i1

end Clever_005_intersperseObligations
