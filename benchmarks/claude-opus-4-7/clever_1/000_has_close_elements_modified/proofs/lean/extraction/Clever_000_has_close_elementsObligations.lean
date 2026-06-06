-- Companion obligations file for the `clever_000_has_close_elements` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_000_has_close_elements

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_000_has_close_elementsObligations

/-- Oracle: a "close pair" exists when some pair of distinct indices `i, j`
    has `|numbers[i] - numbers[j]| < threshold`. We compute the difference
    and absolute value in `Int`, sidestepping `i64` subtraction overflow at
    the spec level — this matches the brute-force `close_pair_exists`
    reference function in the Rust source's `tests` module. -/
private def close_pair_exists
    (numbers : RustSlice i64) (threshold : i64) : Prop :=
  ∃ i j : Nat, ∃ (hi : i < numbers.val.size) (hj : j < numbers.val.size),
    i ≠ j ∧
    (((numbers.val[i]'hi).toInt - (numbers.val[j]'hj).toInt).natAbs : Int)
      < threshold.toInt

/-- Edge case at the recursion base (`n = 0`): an empty slice contains no
    pair, so the result is `false` for every threshold. Pins down the
    `k >= n * n` base case at `n = 0`, matching the `empty_slice_is_false`
    proptest.

    Proof: direct computation. With `numbers.val.size = 0`, `Impl.len`
    returns `pure (USize64.ofNat 0)`, `cast_op` lifts this to `pure (0 :
    u64)`, `0 *? 0 = pure 0` (no overflow), `0 >=? 0 = pure true`, so the
    body's first if-branch reduces and yields `pure false = RustM.ok false`.
    All these reductions are definitional once `hempty` is substituted. -/
theorem empty_slice_is_false
    (numbers : RustSlice i64) (threshold : i64)
    (hempty : numbers.val.size = 0) :
    clever_000_has_close_elements.has_close_elements numbers threshold
      = RustM.ok false := by
  unfold clever_000_has_close_elements.has_close_elements
  unfold clever_000_has_close_elements.has_close_elements_at
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             hempty]
  rfl

/-! ## Auxiliary lemmas for the recursive obligations

Both `sound_no_false_positive` and `complete_no_false_negative` reason
about `has_close_elements_at` over arbitrary `k`. The natural induction
measure is `n*n - k.toNat` where `n = numbers.val.size`, decreasing by 1
on each recursive call (which increments `k`). The inductive step
requires a "step-decomposition" lemma — provided by `step_analyze`
below — that peels one iteration of the `partial_fixpoint` body under
the success hypothesis.

### Geometry of the index space

`has_close_elements_at` linearises pairs `(i, j) ∈ [0, n) × [0, n)` into
counters `k = i * n + j`. We need the basic fact that the inverse of this
encoding stays in bounds, packaged as `index_bound` below.
-/

/-- Index decomposition: when `k < n * n` with `n > 0`, both
    `k / n` and `k % n` are valid indices into a length-`n` slice. -/
private theorem index_bound (n k : Nat) (hn : 0 < n) (hk : k < n * n) :
    k / n < n ∧ k % n < n := by
  refine ⟨?_, Nat.mod_lt _ hn⟩
  exact (Nat.div_lt_iff_lt_mul hn).mpr (by rw [Nat.mul_comm]; exact hk)

/-- Geometric bound: for `i, j < n` we have `i * n + j < n * n`. Used in
    the base-case branch of the induction to derive a contradiction when
    `k.toNat ≥ n * n` but we're given some `(i, j)` with `k.toNat ≤ i*n+j`. -/
private theorem ij_lt_nn (n i j : Nat) (hi : i < n) (hj : j < n) :
    i * n + j < n * n := by
  have h_mul : (i + 1) * n ≤ n * n := Nat.mul_le_mul_right n hi
  have h_succ : (i + 1) * n = i * n + n := Nat.succ_mul i n
  omega

/-- Step unfold: at any `k` with `k < n*n` and `n*n` fitting in `u64`,
    `has_close_elements_at numbers threshold k` equals the body's else-branch
    — i.e., the inner do-block that examines `numbers[k/n]` and `numbers[k%n]`,
    optionally returns `true`, or recurses at `k+1`. -/
private theorem step_unfold
    (numbers : RustSlice i64) (threshold : i64) (k : u64)
    (hnn_fits : numbers.val.size * numbers.val.size < 2 ^ 64)
    (hk_lt : k.toNat < numbers.val.size * numbers.val.size) :
    clever_000_has_close_elements.has_close_elements_at numbers threshold k =
      (do
        let i ← (rust_primitives.hax.cast_op
                  (← (k /? (USize64.ofNat numbers.val.size).toUInt64 : RustM u64))
                  : RustM usize)
        let j ← (rust_primitives.hax.cast_op
                  (← (k %? (USize64.ofNat numbers.val.size).toUInt64 : RustM u64))
                  : RustM usize)
        let diff : i64 ←
          if (← ((← (numbers[i]_? : RustM i64)) >? (← (numbers[j]_? : RustM i64)))) then
            ((← (numbers[i]_? : RustM i64)) -? (← (numbers[j]_? : RustM i64)))
          else
            ((← (numbers[j]_? : RustM i64)) -? (← (numbers[i]_? : RustM i64)))
        if (← ((← (i !=? j : RustM Bool)) &&? (← (diff <? threshold : RustM Bool)))) then
          pure true
        else
          clever_000_has_close_elements.has_close_elements_at numbers threshold
            (← (k +? (1 : u64) : RustM u64))) := by
  have h_n_fit : numbers.val.size < 2 ^ 64 := by
    have h_lt := numbers.size_lt_usizeSize
    have heq : (USize64.size : Nat) = 2 ^ 64 := by decide
    rw [← heq]; exact h_lt
  have h_n_toNat : (USize64.ofNat numbers.val.size).toUInt64.toNat = numbers.val.size := by
    show (USize64.ofNat numbers.val.size).toNat.toUInt64.toNat = numbers.val.size
    rw [USize64.toNat_ofNat_of_lt' h_n_fit]
    exact UInt64.toNat_ofNat_of_lt' h_n_fit
  have h_no_mul_overflow :
      BitVec.umulOverflow (USize64.ofNat numbers.val.size).toUInt64.toBitVec
                          (USize64.ofNat numbers.val.size).toUInt64.toBitVec = false := by
    have : ¬ UInt64.mulOverflow (USize64.ofNat numbers.val.size).toUInt64
                                (USize64.ofNat numbers.val.size).toUInt64 := by
      rw [UInt64.mulOverflow_iff, h_n_toNat]; omega
    simpa [UInt64.mulOverflow] using this
  have h_mul_eq :
      ((USize64.ofNat numbers.val.size).toUInt64 *? (USize64.ofNat numbers.val.size).toUInt64
        : RustM u64) =
      pure ((USize64.ofNat numbers.val.size).toUInt64 * (USize64.ofNat numbers.val.size).toUInt64) := by
    show (rust_primitives.ops.arith.Mul.mul _ _ : RustM u64) = _
    show (if BitVec.umulOverflow _ _ then (.fail .integerOverflow : RustM u64)
          else pure _) = _
    rw [h_no_mul_overflow]; rfl
  have h_prod_toNat :
      ((USize64.ofNat numbers.val.size).toUInt64
       * (USize64.ofNat numbers.val.size).toUInt64).toNat
        = numbers.val.size * numbers.val.size := by
    rw [UInt64.toNat_mul, h_n_toNat]
    exact Nat.mod_eq_of_lt hnn_fits
  have h_ge_eq :
      (k >=? ((USize64.ofNat numbers.val.size).toUInt64
              * (USize64.ofNat numbers.val.size).toUInt64) : RustM Bool) = pure false := by
    show (rust_primitives.cmp.ge k _ : RustM Bool) = pure false
    show (pure (decide _) : RustM Bool) = pure false
    have h_lt_uint : k < ((USize64.ofNat numbers.val.size).toUInt64
                          * (USize64.ofNat numbers.val.size).toUInt64) := by
      rw [UInt64.lt_iff_toNat_lt, h_prod_toNat]
      exact hk_lt
    have hnge : ¬ (k ≥ ((USize64.ofNat numbers.val.size).toUInt64
                        * (USize64.ofNat numbers.val.size).toUInt64)) := by
      intro hge; exact absurd h_lt_uint (Nat.not_lt.mpr (UInt64.le_iff_toNat_le.mp hge))
    rw [decide_eq_false hnge]
  conv => lhs; unfold clever_000_has_close_elements.has_close_elements_at
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.hax.cast_op, Cast.cast, pure_bind]
  rw [h_mul_eq]
  simp only [pure_bind]
  rw [h_ge_eq]
  simp only [pure_bind, if_false, Bool.false_eq_true]

/-! ## Bind-success extraction

We need a workhorse lemma that, given `(x >>= f) = RustM.ok b`, extracts a
witness `a` such that `x = RustM.ok a` and `f a = RustM.ok b`. -/

/-- Symmetry of `Int.natAbs` under signed subtraction. -/
private theorem int_natAbs_sub_comm (a b : Int) :
    (a - b).natAbs = (b - a).natAbs := by
  have h : a - b = -(b - a) := by omega
  rw [h, Int.natAbs_neg]

/-- From `(a -? b : RustM i64) = ok y`, extract that the signed subtraction
    did not overflow, and that the witness is `a - b`. -/
private theorem i64_sub_extract (a b y : i64)
    (hsub : (a -? b : RustM i64) = RustM.ok y) :
    BitVec.ssubOverflow a.toBitVec b.toBitVec = false ∧ y = a - b := by
  have h_unfold : (a -? b : RustM i64) =
      (if BitVec.ssubOverflow a.toBitVec b.toBitVec then
        (.fail .integerOverflow : RustM i64)
       else pure (a - b)) := rfl
  cases hbv : BitVec.ssubOverflow a.toBitVec b.toBitVec with
  | true =>
    exfalso
    have h_fail : (a -? b : RustM i64) = .fail .integerOverflow := by
      rw [h_unfold, hbv]; rfl
    rw [h_fail] at hsub
    cases hsub
  | false =>
    refine ⟨rfl, ?_⟩
    have h_pure : (a -? b : RustM i64) = pure (a - b) := by
      rw [h_unfold, hbv]; rfl
    rw [h_pure] at hsub
    have h_ok : (pure (a - b) : RustM i64) = RustM.ok (a - b) := rfl
    rw [h_ok] at hsub
    injection hsub with h1
    injection h1 with h2
    exact h2.symm

/-- Bridge from boolean `bne` to propositional inequality on `USize64`. -/
private theorem USize64_bne_iff_ne (a b : USize64) :
    (a != b) = true ↔ a ≠ b := by
  simp [bne_iff_ne]

private theorem RustM_bind_ok_iff {α β : Type} (x : RustM α) (f : α → RustM β) (b : β) :
    (x >>= f) = RustM.ok b ↔ ∃ a, x = RustM.ok a ∧ f a = RustM.ok b := by
  constructor
  · intro h
    cases hx : x with
    | none =>
      exfalso
      rw [hx] at h
      cases h
    | some r =>
      cases r with
      | error e =>
        exfalso
        rw [hx] at h
        cases h
      | ok v =>
        refine ⟨v, rfl, ?_⟩
        rw [hx] at h
        exact h
  · rintro ⟨a, hx, hfa⟩
    rw [hx]
    show f a = RustM.ok b
    exact hfa

/-- Base-case lemma: when the counter `k` has reached `n * n`, the function
    returns `RustM.ok false`. -/
private theorem base_case
    (numbers : RustSlice i64) (threshold : i64) (k : u64)
    (hnn_fits : numbers.val.size * numbers.val.size < 2 ^ 64)
    (hk_ge : k.toNat ≥ numbers.val.size * numbers.val.size) :
    clever_000_has_close_elements.has_close_elements_at numbers threshold k
      = RustM.ok false := by
  have h_n_fit : numbers.val.size < 2 ^ 64 := by
    have h_lt := numbers.size_lt_usizeSize
    have heq : (USize64.size : Nat) = 2 ^ 64 := by decide
    rw [← heq]; exact h_lt
  have h_us_toNat : (USize64.ofNat numbers.val.size).toNat = numbers.val.size :=
    USize64.toNat_ofNat_of_lt' h_n_fit
  have h_n_toNat : (USize64.ofNat numbers.val.size).toUInt64.toNat = numbers.val.size := by
    show (USize64.ofNat numbers.val.size).toNat.toUInt64.toNat = numbers.val.size
    rw [h_us_toNat]
    exact UInt64.toNat_ofNat_of_lt' h_n_fit
  have h_no_mul_overflow :
      BitVec.umulOverflow (USize64.ofNat numbers.val.size).toUInt64.toBitVec
                          (USize64.ofNat numbers.val.size).toUInt64.toBitVec = false := by
    have : ¬ UInt64.mulOverflow (USize64.ofNat numbers.val.size).toUInt64
                                (USize64.ofNat numbers.val.size).toUInt64 := by
      rw [UInt64.mulOverflow_iff, h_n_toNat]; omega
    simpa [UInt64.mulOverflow] using this
  have h_mul_eq :
      ((USize64.ofNat numbers.val.size).toUInt64 *? (USize64.ofNat numbers.val.size).toUInt64
        : RustM u64) =
      pure ((USize64.ofNat numbers.val.size).toUInt64 * (USize64.ofNat numbers.val.size).toUInt64)
      := by
    show (rust_primitives.ops.arith.Mul.mul (USize64.ofNat numbers.val.size).toUInt64
                                            (USize64.ofNat numbers.val.size).toUInt64
          : RustM u64) = _
    show (if BitVec.umulOverflow (USize64.ofNat numbers.val.size).toUInt64.toBitVec
                                  (USize64.ofNat numbers.val.size).toUInt64.toBitVec then
            (.fail .integerOverflow : RustM u64)
          else pure ((USize64.ofNat numbers.val.size).toUInt64
                     * (USize64.ofNat numbers.val.size).toUInt64)) = _
    rw [h_no_mul_overflow]; rfl
  have h_prod_toNat :
      ((USize64.ofNat numbers.val.size).toUInt64 * (USize64.ofNat numbers.val.size).toUInt64).toNat
        = numbers.val.size * numbers.val.size := by
    rw [UInt64.toNat_mul, h_n_toNat]
    exact Nat.mod_eq_of_lt hnn_fits
  have h_ge_eq :
      (k >=? ((USize64.ofNat numbers.val.size).toUInt64
              * (USize64.ofNat numbers.val.size).toUInt64) : RustM Bool) = pure true := by
    show (rust_primitives.cmp.ge k _ : RustM Bool) = pure true
    show (pure (decide _) : RustM Bool) = pure true
    have h_le_uint : ((USize64.ofNat numbers.val.size).toUInt64
                       * (USize64.ofNat numbers.val.size).toUInt64) ≤ k := by
      rw [UInt64.le_iff_toNat_le, h_prod_toNat]
      exact hk_ge
    have hge : k ≥ ((USize64.ofNat numbers.val.size).toUInt64
                     * (USize64.ofNat numbers.val.size).toUInt64) := h_le_uint
    rw [decide_eq_true hge]
  unfold clever_000_has_close_elements.has_close_elements_at
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.hax.cast_op, Cast.cast, pure_bind]
  rw [h_mul_eq]
  simp only [pure_bind]
  rw [h_ge_eq]
  simp only [pure_bind, if_true]
  rfl

/-- Step analysis (the workhorse of both auxiliary lemmas).

    Given the function returns `ok b` at counter `k` with `k < n*n` and
    `n*n < 2^64`, peeling one iteration via `step_unfold` and chasing the
    bind chain via `RustM_bind_ok_iff` yields:
      - either the current pair `(k/n, k%n)` is "close" (distinct indices
        whose absolute integer difference is < threshold) AND `b = true`;
      - or the pair is NOT close AND the recursive call at `k+1` returns
        `ok b` (with `(k+1).toNat = k.toNat + 1`). -/
private theorem step_analyze
    (numbers : RustSlice i64) (threshold : i64) (k : u64) (b : Bool)
    (hnn_fits : numbers.val.size * numbers.val.size < 2 ^ 64)
    (hk_lt : k.toNat < numbers.val.size * numbers.val.size)
    (hat : clever_000_has_close_elements.has_close_elements_at numbers threshold k
            = RustM.ok b) :
    ∃ (hi : k.toNat / numbers.val.size < numbers.val.size)
      (hj : k.toNat % numbers.val.size < numbers.val.size),
    (((k.toNat / numbers.val.size ≠ k.toNat % numbers.val.size) ∧
      ((((numbers.val[k.toNat / numbers.val.size]'hi).toInt -
         (numbers.val[k.toNat % numbers.val.size]'hj).toInt).natAbs : Int)
            < threshold.toInt) ∧
       b = true) ∨
     (((k.toNat / numbers.val.size = k.toNat % numbers.val.size) ∨
       ¬ ((((numbers.val[k.toNat / numbers.val.size]'hi).toInt -
            (numbers.val[k.toNat % numbers.val.size]'hj).toInt).natAbs : Int)
              < threshold.toInt)) ∧
      ∃ k' : u64, k'.toNat = k.toNat + 1 ∧
        clever_000_has_close_elements.has_close_elements_at numbers threshold k'
          = RustM.ok b)) := by
  have h_n_fit : numbers.val.size < 2 ^ 64 := by
    have h_lt := numbers.size_lt_usizeSize
    have heq : (USize64.size : Nat) = 2 ^ 64 := by decide
    rw [← heq]; exact h_lt
  have h_n_pos : 0 < numbers.val.size := by
    rcases Nat.eq_zero_or_pos numbers.val.size with hzero | hpos
    · exfalso; rw [hzero] at hk_lt; omega
    · exact hpos
  obtain ⟨h_i_lt_n, h_j_lt_n⟩ :=
    index_bound numbers.val.size k.toNat h_n_pos hk_lt
  refine ⟨h_i_lt_n, h_j_lt_n, ?_⟩
  have h_n_u64_toNat :
      (USize64.ofNat numbers.val.size).toUInt64.toNat = numbers.val.size := by
    show (USize64.ofNat numbers.val.size).toNat.toUInt64.toNat = numbers.val.size
    rw [USize64.toNat_ofNat_of_lt' h_n_fit]
    exact UInt64.toNat_ofNat_of_lt' h_n_fit
  have h_n_u64_ne_zero : (USize64.ofNat numbers.val.size).toUInt64 ≠ 0 := by
    intro h
    have h0 : (USize64.ofNat numbers.val.size).toUInt64.toNat = 0 := by
      rw [h]; rfl
    rw [h_n_u64_toNat] at h0
    omega
  have h_div_eq :
      (k /? (USize64.ofNat numbers.val.size).toUInt64 : RustM u64)
        = pure (k / (USize64.ofNat numbers.val.size).toUInt64) := by
    show (rust_primitives.ops.arith.Div.div k (USize64.ofNat numbers.val.size).toUInt64
          : RustM u64) = pure _
    show (if (USize64.ofNat numbers.val.size).toUInt64 = 0
          then (.fail .divisionByZero : RustM u64)
          else pure _) = _
    rw [if_neg h_n_u64_ne_zero]
  have h_mod_eq :
      (k %? (USize64.ofNat numbers.val.size).toUInt64 : RustM u64)
        = pure (k % (USize64.ofNat numbers.val.size).toUInt64) := by
    show (rust_primitives.ops.arith.Rem.rem k (USize64.ofNat numbers.val.size).toUInt64
          : RustM u64) = pure _
    show (if (USize64.ofNat numbers.val.size).toUInt64 = 0
          then (.fail .divisionByZero : RustM u64)
          else pure _) = _
    rw [if_neg h_n_u64_ne_zero]
  have h_kp1_no_overflow : k.toNat + 1 < 2 ^ 64 := by omega
  have h_kp1_no_bv :
      BitVec.uaddOverflow k.toBitVec (1 : u64).toBitVec = false := by
    have : ¬ UInt64.addOverflow k 1 := by
      rw [UInt64.addOverflow_iff]
      have h_one : (1 : u64).toNat = 1 := rfl
      rw [h_one]; omega
    simpa [UInt64.addOverflow] using this
  have h_kp1_eq : (k +? (1 : u64) : RustM u64) = pure (k + 1) := by
    show (rust_primitives.ops.arith.Add.add k 1 : RustM u64) = pure (k + 1)
    show (if BitVec.uaddOverflow k.toBitVec (1 : u64).toBitVec
          then (.fail .integerOverflow : RustM u64)
          else pure (k + 1)) = _
    rw [h_kp1_no_bv]; rfl
  have h_kp1_toNat : (k + 1).toNat = k.toNat + 1 := by
    rw [UInt64.toNat_add]
    have h_one : (1 : u64).toNat = 1 := rfl
    rw [h_one]
    exact Nat.mod_eq_of_lt h_kp1_no_overflow
  have h_i_usize_toNat :
      (UInt64.toUSize64
        (k / (USize64.ofNat numbers.val.size).toUInt64)).toNat
        = k.toNat / numbers.val.size := by
    show ((k / (USize64.ofNat numbers.val.size).toUInt64).toNat.toUSize64).toNat = _
    show (USize64.ofNat (k / (USize64.ofNat numbers.val.size).toUInt64).toNat).toNat = _
    rw [USize64.toNat_ofNat_of_lt'
          (k / (USize64.ofNat numbers.val.size).toUInt64).toNat_lt]
    rw [UInt64.toNat_div, h_n_u64_toNat]
  have h_j_usize_toNat :
      (UInt64.toUSize64
        (k % (USize64.ofNat numbers.val.size).toUInt64)).toNat
        = k.toNat % numbers.val.size := by
    show ((k % (USize64.ofNat numbers.val.size).toUInt64).toNat.toUSize64).toNat = _
    show (USize64.ofNat (k % (USize64.ofNat numbers.val.size).toUInt64).toNat).toNat = _
    rw [USize64.toNat_ofNat_of_lt'
          (k % (USize64.ofNat numbers.val.size).toUInt64).toNat_lt]
    rw [UInt64.toNat_mod, h_n_u64_toNat]
  have h_i_lt :
      (UInt64.toUSize64
        (k / (USize64.ofNat numbers.val.size).toUInt64)).toNat
          < numbers.val.size := by
    rw [h_i_usize_toNat]; exact h_i_lt_n
  have h_j_lt :
      (UInt64.toUSize64
        (k % (USize64.ofNat numbers.val.size).toUInt64)).toNat
          < numbers.val.size := by
    rw [h_j_usize_toNat]; exact h_j_lt_n
  have h_num_i :
      (numbers[UInt64.toUSize64
                (k / (USize64.ofNat numbers.val.size).toUInt64)]_?
        : RustM i64)
        = pure (numbers.val[UInt64.toUSize64
                (k / (USize64.ofNat numbers.val.size).toUInt64)]'h_i_lt) := by
    show (if h : (UInt64.toUSize64
                  (k / (USize64.ofNat numbers.val.size).toUInt64)).toNat
                  < numbers.val.size
          then pure (numbers.val[UInt64.toUSize64
                  (k / (USize64.ofNat numbers.val.size).toUInt64)])
          else (.fail .arrayOutOfBounds : RustM i64)) = _
    rw [dif_pos h_i_lt]
  have h_num_j :
      (numbers[UInt64.toUSize64
                (k % (USize64.ofNat numbers.val.size).toUInt64)]_?
        : RustM i64)
        = pure (numbers.val[UInt64.toUSize64
                (k % (USize64.ofNat numbers.val.size).toUInt64)]'h_j_lt) := by
    show (if h : (UInt64.toUSize64
                  (k % (USize64.ofNat numbers.val.size).toUInt64)).toNat
                  < numbers.val.size
          then pure (numbers.val[UInt64.toUSize64
                  (k % (USize64.ofNat numbers.val.size).toUInt64)])
          else (.fail .arrayOutOfBounds : RustM i64)) = _
    rw [dif_pos h_j_lt]
  rw [step_unfold numbers threshold k hnn_fits hk_lt] at hat
  simp only [h_div_eq, h_mod_eq, h_num_i, h_num_j, h_kp1_eq,
             rust_primitives.hax.cast_op, Cast.cast,
             rust_primitives.cmp.gt, rust_primitives.cmp.lt,
             rust_primitives.cmp.ne,
             rust_primitives.hax.logical_op.and,
             pure_bind, decide_eq_true_eq] at hat
  have h_a_eq :
      numbers.val[UInt64.toUSize64
                    (k / (USize64.ofNat numbers.val.size).toUInt64)]'h_i_lt
        = numbers.val[k.toNat / numbers.val.size]'h_i_lt_n := by
    show numbers.val[(UInt64.toUSize64
                       (k / (USize64.ofNat numbers.val.size).toUInt64)).toNat]'h_i_lt
        = numbers.val[k.toNat / numbers.val.size]'h_i_lt_n
    congr 1
  have h_a'_eq :
      numbers.val[UInt64.toUSize64
                    (k % (USize64.ofNat numbers.val.size).toUInt64)]'h_j_lt
        = numbers.val[k.toNat % numbers.val.size]'h_j_lt_n := by
    show numbers.val[(UInt64.toUSize64
                       (k % (USize64.ofNat numbers.val.size).toUInt64)).toNat]'h_j_lt
        = numbers.val[k.toNat % numbers.val.size]'h_j_lt_n
    congr 1
  -- Case-split on the outer `if a_i > a_j`.
  by_cases h_gt :
      numbers.val[UInt64.toUSize64
                    (k / (USize64.ofNat numbers.val.size).toUInt64)]'h_i_lt
      > numbers.val[UInt64.toUSize64
                    (k % (USize64.ofNat numbers.val.size).toUInt64)]'h_j_lt
  · -- Branch: a_i > a_j. diff = a_i - a_j.
    rw [if_pos h_gt] at hat
    obtain ⟨diff, h_sub_ok, h_rest⟩ := (RustM_bind_ok_iff _ _ _).mp hat
    obtain ⟨h_no_ov, h_diff_eq⟩ := i64_sub_extract _ _ diff h_sub_ok
    subst h_diff_eq
    have h_no_subOv : ¬ Int64.subOverflow
        (numbers.val[UInt64.toUSize64
                       (k / (USize64.ofNat numbers.val.size).toUInt64)]'h_i_lt)
        (numbers.val[UInt64.toUSize64
                       (k % (USize64.ofNat numbers.val.size).toUInt64)]'h_j_lt) := by
      show ¬ BitVec.ssubOverflow _ _ = true
      rw [h_no_ov]; decide
    have h_diff_toInt :
        ((numbers.val[UInt64.toUSize64
                        (k / (USize64.ofNat numbers.val.size).toUInt64)]'h_i_lt) -
          (numbers.val[UInt64.toUSize64
                        (k % (USize64.ofNat numbers.val.size).toUInt64)]'h_j_lt)).toInt
        = (numbers.val[UInt64.toUSize64
                        (k / (USize64.ofNat numbers.val.size).toUInt64)]'h_i_lt).toInt -
          (numbers.val[UInt64.toUSize64
                        (k % (USize64.ofNat numbers.val.size).toUInt64)]'h_j_lt).toInt :=
      Int64.toInt_sub_of_not_subOverflow h_no_subOv
    have h_int_gt :
        (numbers.val[UInt64.toUSize64
                      (k % (USize64.ofNat numbers.val.size).toUInt64)]'h_j_lt).toInt
        < (numbers.val[UInt64.toUSize64
                       (k / (USize64.ofNat numbers.val.size).toUInt64)]'h_i_lt).toInt :=
      Int64.lt_iff_toInt_lt.mp h_gt
    have h_natAbs :
        (((numbers.val[k.toNat / numbers.val.size]'h_i_lt_n).toInt -
          (numbers.val[k.toNat % numbers.val.size]'h_j_lt_n).toInt).natAbs : Int) =
        (numbers.val[k.toNat / numbers.val.size]'h_i_lt_n).toInt -
        (numbers.val[k.toNat % numbers.val.size]'h_j_lt_n).toInt := by
      apply Int.natAbs_of_nonneg
      rw [← h_a_eq, ← h_a'_eq]; omega
    by_cases h_cond :
        ((UInt64.toUSize64 (k / (USize64.ofNat numbers.val.size).toUInt64) !=
            UInt64.toUSize64 (k % (USize64.ofNat numbers.val.size).toUInt64)) &&
          decide
            ((numbers.val[UInt64.toUSize64
                            (k / (USize64.ofNat numbers.val.size).toUInt64)]'h_i_lt) -
              (numbers.val[UInt64.toUSize64
                            (k % (USize64.ofNat numbers.val.size).toUInt64)]'h_j_lt) <
             threshold)) = true
    · rw [if_pos h_cond] at h_rest
      have h_pure : (pure true : RustM Bool) = RustM.ok true := rfl
      rw [h_pure] at h_rest
      injection h_rest with h_b1
      injection h_b1 with h_b2
      rw [Bool.and_eq_true] at h_cond
      obtain ⟨h_ne_bool, h_lt_bool⟩ := h_cond
      have h_ne : UInt64.toUSize64 (k / (USize64.ofNat numbers.val.size).toUInt64) ≠
                  UInt64.toUSize64 (k % (USize64.ofNat numbers.val.size).toUInt64) :=
        (USize64_bne_iff_ne _ _).mp h_ne_bool
      have h_lt_diff :
          (numbers.val[UInt64.toUSize64
                       (k / (USize64.ofNat numbers.val.size).toUInt64)]'h_i_lt) -
          (numbers.val[UInt64.toUSize64
                       (k % (USize64.ofNat numbers.val.size).toUInt64)]'h_j_lt)
          < threshold := of_decide_eq_true h_lt_bool
      have h_lt_int :
          ((numbers.val[UInt64.toUSize64
                        (k / (USize64.ofNat numbers.val.size).toUInt64)]'h_i_lt) -
            (numbers.val[UInt64.toUSize64
                        (k % (USize64.ofNat numbers.val.size).toUInt64)]'h_j_lt)).toInt
          < threshold.toInt := Int64.lt_iff_toInt_lt.mp h_lt_diff
      rw [h_diff_toInt] at h_lt_int
      left
      refine ⟨?_, ?_, h_b2.symm⟩
      · intro h_eq
        apply h_ne
        apply USize64.toNat_inj.mp
        rw [h_i_usize_toNat, h_j_usize_toNat]
        exact h_eq
      · rw [h_natAbs]
        rw [← h_a_eq, ← h_a'_eq]
        exact h_lt_int
    · rw [if_neg h_cond] at h_rest
      right
      refine ⟨?_, k + 1, h_kp1_toNat, h_rest⟩
      have h_cond_false :
          ((UInt64.toUSize64 (k / (USize64.ofNat numbers.val.size).toUInt64) !=
              UInt64.toUSize64 (k % (USize64.ofNat numbers.val.size).toUInt64)) &&
            decide
              ((numbers.val[UInt64.toUSize64
                            (k / (USize64.ofNat numbers.val.size).toUInt64)]'h_i_lt) -
                (numbers.val[UInt64.toUSize64
                            (k % (USize64.ofNat numbers.val.size).toUInt64)]'h_j_lt) <
                threshold)) = false := by
        cases h_b : ((UInt64.toUSize64 (k / (USize64.ofNat numbers.val.size).toUInt64) !=
              UInt64.toUSize64 (k % (USize64.ofNat numbers.val.size).toUInt64)) &&
            decide
              ((numbers.val[UInt64.toUSize64
                            (k / (USize64.ofNat numbers.val.size).toUInt64)]'h_i_lt) -
                (numbers.val[UInt64.toUSize64
                            (k % (USize64.ofNat numbers.val.size).toUInt64)]'h_j_lt) <
                threshold)) with
        | true => exact absurd h_b h_cond
        | false => rfl
      rw [Bool.and_eq_false_iff] at h_cond_false
      rcases h_cond_false with h_bne_false | h_dec_false
      · left
        have h_eq_usize :
            UInt64.toUSize64 (k / (USize64.ofNat numbers.val.size).toUInt64) =
            UInt64.toUSize64 (k % (USize64.ofNat numbers.val.size).toUInt64) := by
          cases h_beq :
              (UInt64.toUSize64 (k / (USize64.ofNat numbers.val.size).toUInt64) ==
               UInt64.toUSize64 (k % (USize64.ofNat numbers.val.size).toUInt64)) with
          | true => exact eq_of_beq h_beq
          | false =>
            exfalso
            have h_bne :
                (UInt64.toUSize64 (k / (USize64.ofNat numbers.val.size).toUInt64) !=
                  UInt64.toUSize64 (k % (USize64.ofNat numbers.val.size).toUInt64)) = true := by
              show (!(UInt64.toUSize64 (k / (USize64.ofNat numbers.val.size).toUInt64) ==
                       UInt64.toUSize64 (k % (USize64.ofNat numbers.val.size).toUInt64))) = true
              rw [h_beq]; rfl
            rw [h_bne] at h_bne_false
            cases h_bne_false
        have h_toNat_eq :
            (UInt64.toUSize64 (k / (USize64.ofNat numbers.val.size).toUInt64)).toNat =
            (UInt64.toUSize64 (k % (USize64.ofNat numbers.val.size).toUInt64)).toNat := by
          rw [h_eq_usize]
        rw [h_i_usize_toNat, h_j_usize_toNat] at h_toNat_eq
        exact h_toNat_eq
      · right
        intro h_close
        rw [h_natAbs] at h_close
        rw [← h_a_eq, ← h_a'_eq] at h_close
        rw [← h_diff_toInt] at h_close
        have h_lt_diff :
            (numbers.val[UInt64.toUSize64
                         (k / (USize64.ofNat numbers.val.size).toUInt64)]'h_i_lt) -
            (numbers.val[UInt64.toUSize64
                         (k % (USize64.ofNat numbers.val.size).toUInt64)]'h_j_lt)
            < threshold := Int64.lt_iff_toInt_lt.mpr h_close
        exact (of_decide_eq_false h_dec_false) h_lt_diff
  · -- Branch: a_i ≤ a_j. diff = a_j - a_i.
    rw [if_neg h_gt] at hat
    obtain ⟨diff, h_sub_ok, h_rest⟩ := (RustM_bind_ok_iff _ _ _).mp hat
    obtain ⟨h_no_ov, h_diff_eq⟩ := i64_sub_extract _ _ diff h_sub_ok
    subst h_diff_eq
    have h_no_subOv : ¬ Int64.subOverflow
        (numbers.val[UInt64.toUSize64
                       (k % (USize64.ofNat numbers.val.size).toUInt64)]'h_j_lt)
        (numbers.val[UInt64.toUSize64
                       (k / (USize64.ofNat numbers.val.size).toUInt64)]'h_i_lt) := by
      show ¬ BitVec.ssubOverflow _ _ = true
      rw [h_no_ov]; decide
    have h_diff_toInt :
        ((numbers.val[UInt64.toUSize64
                        (k % (USize64.ofNat numbers.val.size).toUInt64)]'h_j_lt) -
          (numbers.val[UInt64.toUSize64
                        (k / (USize64.ofNat numbers.val.size).toUInt64)]'h_i_lt)).toInt
        = (numbers.val[UInt64.toUSize64
                        (k % (USize64.ofNat numbers.val.size).toUInt64)]'h_j_lt).toInt -
          (numbers.val[UInt64.toUSize64
                        (k / (USize64.ofNat numbers.val.size).toUInt64)]'h_i_lt).toInt :=
      Int64.toInt_sub_of_not_subOverflow h_no_subOv
    have h_int_le :
        (numbers.val[UInt64.toUSize64
                      (k / (USize64.ofNat numbers.val.size).toUInt64)]'h_i_lt).toInt
        ≤ (numbers.val[UInt64.toUSize64
                       (k % (USize64.ofNat numbers.val.size).toUInt64)]'h_j_lt).toInt := by
      have : ¬ (numbers.val[UInt64.toUSize64
                            (k % (USize64.ofNat numbers.val.size).toUInt64)]'h_j_lt).toInt
              < (numbers.val[UInt64.toUSize64
                             (k / (USize64.ofNat numbers.val.size).toUInt64)]'h_i_lt).toInt := by
        intro h
        exact h_gt (Int64.lt_iff_toInt_lt.mpr h)
      omega
    have h_natAbs :
        (((numbers.val[k.toNat / numbers.val.size]'h_i_lt_n).toInt -
          (numbers.val[k.toNat % numbers.val.size]'h_j_lt_n).toInt).natAbs : Int) =
        (numbers.val[k.toNat % numbers.val.size]'h_j_lt_n).toInt -
        (numbers.val[k.toNat / numbers.val.size]'h_i_lt_n).toInt := by
      rw [show (((numbers.val[k.toNat / numbers.val.size]'h_i_lt_n).toInt -
                  (numbers.val[k.toNat % numbers.val.size]'h_j_lt_n).toInt).natAbs : Int) =
                (((numbers.val[k.toNat % numbers.val.size]'h_j_lt_n).toInt -
                  (numbers.val[k.toNat / numbers.val.size]'h_i_lt_n).toInt).natAbs : Int) from by
                rw [int_natAbs_sub_comm]]
      apply Int.natAbs_of_nonneg
      rw [← h_a_eq, ← h_a'_eq]; omega
    by_cases h_cond :
        ((UInt64.toUSize64 (k / (USize64.ofNat numbers.val.size).toUInt64) !=
            UInt64.toUSize64 (k % (USize64.ofNat numbers.val.size).toUInt64)) &&
          decide
            ((numbers.val[UInt64.toUSize64
                            (k % (USize64.ofNat numbers.val.size).toUInt64)]'h_j_lt) -
              (numbers.val[UInt64.toUSize64
                            (k / (USize64.ofNat numbers.val.size).toUInt64)]'h_i_lt) <
             threshold)) = true
    · rw [if_pos h_cond] at h_rest
      have h_pure : (pure true : RustM Bool) = RustM.ok true := rfl
      rw [h_pure] at h_rest
      injection h_rest with h_b1
      injection h_b1 with h_b2
      rw [Bool.and_eq_true] at h_cond
      obtain ⟨h_ne_bool, h_lt_bool⟩ := h_cond
      have h_ne : UInt64.toUSize64 (k / (USize64.ofNat numbers.val.size).toUInt64) ≠
                  UInt64.toUSize64 (k % (USize64.ofNat numbers.val.size).toUInt64) :=
        (USize64_bne_iff_ne _ _).mp h_ne_bool
      have h_lt_diff :
          (numbers.val[UInt64.toUSize64
                       (k % (USize64.ofNat numbers.val.size).toUInt64)]'h_j_lt) -
          (numbers.val[UInt64.toUSize64
                       (k / (USize64.ofNat numbers.val.size).toUInt64)]'h_i_lt)
          < threshold := of_decide_eq_true h_lt_bool
      have h_lt_int :
          ((numbers.val[UInt64.toUSize64
                        (k % (USize64.ofNat numbers.val.size).toUInt64)]'h_j_lt) -
            (numbers.val[UInt64.toUSize64
                        (k / (USize64.ofNat numbers.val.size).toUInt64)]'h_i_lt)).toInt
          < threshold.toInt := Int64.lt_iff_toInt_lt.mp h_lt_diff
      rw [h_diff_toInt] at h_lt_int
      left
      refine ⟨?_, ?_, h_b2.symm⟩
      · intro h_eq
        apply h_ne
        apply USize64.toNat_inj.mp
        rw [h_i_usize_toNat, h_j_usize_toNat]
        exact h_eq
      · rw [h_natAbs]
        rw [← h_a_eq, ← h_a'_eq]
        exact h_lt_int
    · rw [if_neg h_cond] at h_rest
      right
      refine ⟨?_, k + 1, h_kp1_toNat, h_rest⟩
      have h_cond_false :
          ((UInt64.toUSize64 (k / (USize64.ofNat numbers.val.size).toUInt64) !=
              UInt64.toUSize64 (k % (USize64.ofNat numbers.val.size).toUInt64)) &&
            decide
              ((numbers.val[UInt64.toUSize64
                            (k % (USize64.ofNat numbers.val.size).toUInt64)]'h_j_lt) -
                (numbers.val[UInt64.toUSize64
                            (k / (USize64.ofNat numbers.val.size).toUInt64)]'h_i_lt) <
                threshold)) = false := by
        cases h_b : ((UInt64.toUSize64 (k / (USize64.ofNat numbers.val.size).toUInt64) !=
              UInt64.toUSize64 (k % (USize64.ofNat numbers.val.size).toUInt64)) &&
            decide
              ((numbers.val[UInt64.toUSize64
                            (k % (USize64.ofNat numbers.val.size).toUInt64)]'h_j_lt) -
                (numbers.val[UInt64.toUSize64
                            (k / (USize64.ofNat numbers.val.size).toUInt64)]'h_i_lt) <
                threshold)) with
        | true => exact absurd h_b h_cond
        | false => rfl
      rw [Bool.and_eq_false_iff] at h_cond_false
      rcases h_cond_false with h_bne_false | h_dec_false
      · left
        have h_eq_usize :
            UInt64.toUSize64 (k / (USize64.ofNat numbers.val.size).toUInt64) =
            UInt64.toUSize64 (k % (USize64.ofNat numbers.val.size).toUInt64) := by
          cases h_beq :
              (UInt64.toUSize64 (k / (USize64.ofNat numbers.val.size).toUInt64) ==
               UInt64.toUSize64 (k % (USize64.ofNat numbers.val.size).toUInt64)) with
          | true => exact eq_of_beq h_beq
          | false =>
            exfalso
            have h_bne :
                (UInt64.toUSize64 (k / (USize64.ofNat numbers.val.size).toUInt64) !=
                  UInt64.toUSize64 (k % (USize64.ofNat numbers.val.size).toUInt64)) = true := by
              show (!(UInt64.toUSize64 (k / (USize64.ofNat numbers.val.size).toUInt64) ==
                       UInt64.toUSize64 (k % (USize64.ofNat numbers.val.size).toUInt64))) = true
              rw [h_beq]; rfl
            rw [h_bne] at h_bne_false
            cases h_bne_false
        have h_toNat_eq :
            (UInt64.toUSize64 (k / (USize64.ofNat numbers.val.size).toUInt64)).toNat =
            (UInt64.toUSize64 (k % (USize64.ofNat numbers.val.size).toUInt64)).toNat := by
          rw [h_eq_usize]
        rw [h_i_usize_toNat, h_j_usize_toNat] at h_toNat_eq
        exact h_toNat_eq
      · right
        intro h_close
        rw [h_natAbs] at h_close
        rw [← h_a_eq, ← h_a'_eq] at h_close
        rw [← h_diff_toInt] at h_close
        have h_lt_diff :
            (numbers.val[UInt64.toUSize64
                         (k % (USize64.ofNat numbers.val.size).toUInt64)]'h_j_lt) -
            (numbers.val[UInt64.toUSize64
                         (k / (USize64.ofNat numbers.val.size).toUInt64)]'h_i_lt)
            < threshold := Int64.lt_iff_toInt_lt.mpr h_close
        exact (of_decide_eq_false h_dec_false) h_lt_diff

/-- Strong inductive lemma for completeness.

    If at offset `k` the function returns `RustM.ok false`, then for every
    pair `(i, j)` with `i, j < n`, `k.toNat ≤ i*n + j`, and `i ≠ j`, the
    indices don't form a close pair. Induction on `m := n*n - k.toNat`. -/
private theorem complete_aux
    (numbers : RustSlice i64) (threshold : i64) :
    ∀ (m : Nat) (k : u64),
      numbers.val.size * numbers.val.size - k.toNat ≤ m →
      clever_000_has_close_elements.has_close_elements_at numbers threshold k
        = RustM.ok false →
      ∀ (i j : Nat) (hi : i < numbers.val.size) (hj : j < numbers.val.size),
        k.toNat ≤ i * numbers.val.size + j →
        i ≠ j →
        ¬ ((((numbers.val[i]'hi).toInt - (numbers.val[j]'hj).toInt).natAbs : Int)
              < threshold.toInt) := by
  intro m
  induction m with
  | zero =>
    intro k hmk hat i j hi hj hkij hij hclose
    have h_kge : k.toNat ≥ numbers.val.size * numbers.val.size := by omega
    have h_ij_lt : i * numbers.val.size + j < numbers.val.size * numbers.val.size :=
      ij_lt_nn _ _ _ hi hj
    omega
  | succ m ih =>
    intro k hmk hat i j hi hj hkij hij hclose
    by_cases h_kge : k.toNat ≥ numbers.val.size * numbers.val.size
    · have h_ij_lt : i * numbers.val.size + j < numbers.val.size * numbers.val.size :=
        ij_lt_nn _ _ _ hi hj
      omega
    · have h_klt : k.toNat < numbers.val.size * numbers.val.size := by omega
      have hnn_fits : numbers.val.size * numbers.val.size < 2 ^ 64 := by
        by_cases hlt : numbers.val.size * numbers.val.size < 2 ^ 64
        · exact hlt
        exfalso
        have hge : numbers.val.size * numbers.val.size ≥ 2 ^ 64 := Nat.le_of_not_lt hlt
        have h_n_fit : numbers.val.size < 2 ^ 64 := by
          have h_lt := numbers.size_lt_usizeSize
          have heq : (USize64.size : Nat) = 2 ^ 64 := by decide
          rw [← heq]; exact h_lt
        have h_n_toNat :
            (USize64.ofNat numbers.val.size).toUInt64.toNat = numbers.val.size := by
          show (USize64.ofNat numbers.val.size).toNat.toUInt64.toNat = numbers.val.size
          rw [USize64.toNat_ofNat_of_lt' h_n_fit]
          exact UInt64.toNat_ofNat_of_lt' h_n_fit
        have h_mul_overflow :
            BitVec.umulOverflow (USize64.ofNat numbers.val.size).toUInt64.toBitVec
                                (USize64.ofNat numbers.val.size).toUInt64.toBitVec = true := by
          have : UInt64.mulOverflow (USize64.ofNat numbers.val.size).toUInt64
                                    (USize64.ofNat numbers.val.size).toUInt64 := by
            rw [UInt64.mulOverflow_iff, h_n_toNat]; omega
          simpa [UInt64.mulOverflow] using this
        have h_mul_fail :
            ((USize64.ofNat numbers.val.size).toUInt64 *? (USize64.ofNat numbers.val.size).toUInt64
              : RustM u64) = .fail .integerOverflow := by
          show (rust_primitives.ops.arith.Mul.mul _ _ : RustM u64) = .fail .integerOverflow
          show (if BitVec.umulOverflow _ _ then (.fail .integerOverflow : RustM u64)
                else pure _) = .fail .integerOverflow
          rw [h_mul_overflow]; rfl
        unfold clever_000_has_close_elements.has_close_elements_at at hat
        simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
                   rust_primitives.hax.cast_op, Cast.cast, pure_bind] at hat
        rw [h_mul_fail] at hat
        simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, Option.bind] at hat
        cases hat
      obtain ⟨h_div_lt, h_mod_lt, h_disj⟩ :=
        step_analyze numbers threshold k false hnn_fits h_klt hat
      rcases h_disj with ⟨_, _, h_b_true⟩ | ⟨h_not_close, k', h_k', h_rest⟩
      · exact absurd h_b_true (by decide)
      · by_cases h_at_k : i * numbers.val.size + j ≤ k.toNat
        · have h_eq_k : i * numbers.val.size + j = k.toNat := by omega
          have h_n_pos : 0 < numbers.val.size := by
            rcases Nat.eq_zero_or_pos numbers.val.size with hz | hp
            · exfalso; rw [hz] at h_klt; omega
            · exact hp
          have h_i_eq : i = k.toNat / numbers.val.size := by
            have h := h_eq_k
            rw [Nat.add_comm] at h
            rw [← h, Nat.add_mul_div_right _ _ h_n_pos, Nat.div_eq_of_lt hj]
            omega
          have h_j_eq : j = k.toNat % numbers.val.size := by
            rw [← h_eq_k, Nat.add_comm (i * _) j, Nat.add_mul_mod_self_right,
                Nat.mod_eq_of_lt hj]
          subst h_i_eq
          subst h_j_eq
          rcases h_not_close with h_div_eq_mod | h_not_close
          · exact hij h_div_eq_mod
          · exact h_not_close hclose
        · have h_kp1_le : k'.toNat ≤ i * numbers.val.size + j := by
            rw [h_k']; omega
          apply ih k' (by rw [h_k']; omega) h_rest i j hi hj h_kp1_le hij hclose

/-- Helper: from a successful `ok b` result, we can derive that `n * n`
    fits in `u64`. -/
private theorem fit_from_ok
    (numbers : RustSlice i64) (threshold : i64) (k : u64) (b : Bool)
    (hat : clever_000_has_close_elements.has_close_elements_at numbers threshold k
            = RustM.ok b) :
    numbers.val.size * numbers.val.size < 2 ^ 64 := by
  by_cases hlt : numbers.val.size * numbers.val.size < 2 ^ 64
  · exact hlt
  exfalso
  have hge : numbers.val.size * numbers.val.size ≥ 2 ^ 64 := Nat.le_of_not_lt hlt
  have h_n_fit : numbers.val.size < 2 ^ 64 := by
    have h_lt := numbers.size_lt_usizeSize
    have heq : (USize64.size : Nat) = 2 ^ 64 := by decide
    rw [← heq]; exact h_lt
  have h_n_toNat : (USize64.ofNat numbers.val.size).toUInt64.toNat = numbers.val.size := by
    show (USize64.ofNat numbers.val.size).toNat.toUInt64.toNat = numbers.val.size
    rw [USize64.toNat_ofNat_of_lt' h_n_fit]
    exact UInt64.toNat_ofNat_of_lt' h_n_fit
  have h_mul_overflow :
      BitVec.umulOverflow (USize64.ofNat numbers.val.size).toUInt64.toBitVec
                          (USize64.ofNat numbers.val.size).toUInt64.toBitVec = true := by
    have : UInt64.mulOverflow (USize64.ofNat numbers.val.size).toUInt64
                              (USize64.ofNat numbers.val.size).toUInt64 := by
      rw [UInt64.mulOverflow_iff, h_n_toNat]; omega
    simpa [UInt64.mulOverflow] using this
  have h_mul_fail :
      ((USize64.ofNat numbers.val.size).toUInt64 *? (USize64.ofNat numbers.val.size).toUInt64
        : RustM u64) = .fail .integerOverflow := by
    show (rust_primitives.ops.arith.Mul.mul _ _ : RustM u64) = .fail .integerOverflow
    show (if BitVec.umulOverflow _ _ then (.fail .integerOverflow : RustM u64)
          else pure _) = .fail .integerOverflow
    rw [h_mul_overflow]; rfl
  unfold clever_000_has_close_elements.has_close_elements_at at hat
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length,
             rust_primitives.hax.cast_op, Cast.cast, pure_bind] at hat
  rw [h_mul_fail] at hat
  simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
             Option.bind] at hat
  cases hat

/-- Strong inductive lemma for soundness. -/
private theorem sound_aux
    (numbers : RustSlice i64) (threshold : i64) :
    ∀ (m : Nat) (k : u64),
      numbers.val.size * numbers.val.size - k.toNat ≤ m →
      clever_000_has_close_elements.has_close_elements_at numbers threshold k
        = RustM.ok true →
      close_pair_exists numbers threshold := by
  have base_contradiction :
      ∀ (k : u64),
        k.toNat ≥ numbers.val.size * numbers.val.size →
        clever_000_has_close_elements.has_close_elements_at numbers threshold k
          = RustM.ok true →
        False := by
    intro k h_kge hat
    have hnn_fits : numbers.val.size * numbers.val.size < 2 ^ 64 :=
      fit_from_ok numbers threshold k true hat
    have h_false := base_case numbers threshold k hnn_fits h_kge
    rw [h_false] at hat
    exact absurd hat (by decide)
  intro m
  induction m with
  | zero =>
    intro k hmk hat
    exact (base_contradiction k (by omega) hat).elim
  | succ m ih =>
    intro k hmk hat
    by_cases h_kge : k.toNat ≥ numbers.val.size * numbers.val.size
    · exact (base_contradiction k h_kge hat).elim
    · have h_klt : k.toNat < numbers.val.size * numbers.val.size := by omega
      have hnn_fits : numbers.val.size * numbers.val.size < 2 ^ 64 :=
        fit_from_ok numbers threshold k true hat
      obtain ⟨h_div_lt, h_mod_lt, h_disj⟩ :=
        step_analyze numbers threshold k true hnn_fits h_klt hat
      rcases h_disj with ⟨h_close_ne, h_close_lt, _⟩ | ⟨_h_not_close, k', h_k', h_rest⟩
      · exact ⟨k.toNat / numbers.val.size, k.toNat % numbers.val.size,
                h_div_lt, h_mod_lt, h_close_ne, h_close_lt⟩
      · apply ih k' _ h_rest
        rw [h_k']
        omega

/-- Soundness (postcondition, "true" direction): if the function reports a
    close pair, one must actually exist. -/
theorem sound_no_false_positive
    (numbers : RustSlice i64) (threshold : i64)
    (h : clever_000_has_close_elements.has_close_elements numbers threshold
           = RustM.ok true) :
    close_pair_exists numbers threshold := by
  unfold clever_000_has_close_elements.has_close_elements at h
  exact sound_aux numbers threshold
    (numbers.val.size * numbers.val.size) 0 (by simp) h

/-- Completeness (postcondition, "false" direction): if the function returns
    `false`, no close pair exists. -/
theorem complete_no_false_negative
    (numbers : RustSlice i64) (threshold : i64)
    (h : clever_000_has_close_elements.has_close_elements numbers threshold
           = RustM.ok false) :
    ¬ close_pair_exists numbers threshold := by
  unfold clever_000_has_close_elements.has_close_elements at h
  rintro ⟨i, j, hi, hj, hij, hclose⟩
  have hzero : (0 : u64).toNat ≤ i * numbers.val.size + j := by
    simp
  exact complete_aux numbers threshold
    (numbers.val.size * numbers.val.size) 0 (by simp) h i j hi hj hzero hij hclose

end Clever_000_has_close_elementsObligations
