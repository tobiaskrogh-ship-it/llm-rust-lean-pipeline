-- Companion obligations file for the `clever_076_iscube` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_076_iscube

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_076_iscubeObligations

/-! ## i64 ⇄ Int bridge helpers -/

private theorem i64_zero_toInt : (0 : i64).toInt = 0 := by decide
private theorem i64_one_toInt : (1 : i64).toInt = 1 := by decide

private theorem i64_toInt_lt (x : i64) : x.toInt < 2 ^ 63 := by
  have h := Int64.toInt_lt x; simpa using h

private theorem i64_toInt_ge (x : i64) : -(2 ^ 63 : Int) ≤ x.toInt := by
  have h := Int64.le_toInt x; simpa using h

private theorem h63_eq : (2 : Int) ^ (64 - 1) = 2 ^ 63 := by decide

/-- `RustM.ok`-headed bind reduction. -/
@[simp]
private theorem RustM_ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    RustM.ok a >>= f = f a := pure_bind a f

/-! ## Contract clauses derived from the Rust property tests.

  * `small_cases` — 13 unit pins (9 cubes / 4 non-cubes) on specific
    values: `iscube` returns `true` on `0, 1, 8, 27, 64, 125, -1, -8, -27`
    and `false` on `2, 9, 26, 28`.
  * `matches_brute_force` — main equivalence with a naive oracle on
    `n.toInt ∈ [-2^30, 2^30]`.  Bracketed by `iscube_sound` (true →
    witness exists) together with `iscube_non_cubes_rejected` (no
    witness, safe range → false) and `iscube_actual_cubes_recognized`
    (witness present, safe range → true).
  * `soundness` — every `ok true` is justified by an integer witness.
  * `completeness` — every cube `k³` with `|k| ≤ 1024` is recognised.

### Feasibility notes

`cube_walks_to` computes `k * k * k` at each step and recurses with
`k + 1`.  The genuine failure modes in the i64 model are:

  1. Signed multiplication overflow at `k *? k` and `(k*k) *? k`
     (fires once `|k|` approaches `2^21`, since `(2^21)^3 = 2^63`).
  2. Signed addition overflow at `k +? 1` (fires at `k = i64::MAX`).
  3. The wrapper's `-? n` unary negation overflow at `n = i64::MIN`.

  * **Soundness** is universally feasible: an `ok true` from the wrapper
    constrains the inner trace of cube values to expose the witness.
    No precondition is needed.
  * **Completeness** at a cube `k³` requires the walk to reach
    `k.natAbs` without overflow.  `|k| ≤ 1024` makes every intermediate
    cube fit easily in i64 (max `1024^3 = 2^30`), matching the
    proptest's bound.
  * **Non-recognition** (`n` not a cube → `ok false`) requires the
    walk to overshoot before any overflow fires.  `|n.toInt| ≤ 2^30`
    keeps the walk to `k ≤ 1025` (since `1024^3 = 2^30 ≤ |n|`
    forces the walker to test up to `1025^3`), well within the i64
    cubing range, and rules out the `-? n` panic at `i64::MIN`. -/

/-! ## Unit pins from the `small_cases` test.

These are sanity pins on specific values.  `iscube` evaluates
end-to-end through the `partial_fixpoint` kernel, so each pin is
dischargeable by `native_decide`. -/

/-- `iscube(0) = true` (since `0³ = 0`). -/
theorem iscube_0_true :
    clever_076_iscube.iscube (0 : i64) = RustM.ok true := by native_decide

/-- `iscube(1) = true` (since `1³ = 1`). -/
theorem iscube_1_true :
    clever_076_iscube.iscube (1 : i64) = RustM.ok true := by native_decide

/-- `iscube(8) = true` (since `2³ = 8`). -/
theorem iscube_8_true :
    clever_076_iscube.iscube (8 : i64) = RustM.ok true := by native_decide

/-- `iscube(27) = true` (since `3³ = 27`). -/
theorem iscube_27_true :
    clever_076_iscube.iscube (27 : i64) = RustM.ok true := by native_decide

/-- `iscube(64) = true` (since `4³ = 64`). -/
theorem iscube_64_true :
    clever_076_iscube.iscube (64 : i64) = RustM.ok true := by native_decide

/-- `iscube(125) = true` (since `5³ = 125`). -/
theorem iscube_125_true :
    clever_076_iscube.iscube (125 : i64) = RustM.ok true := by native_decide

/-- `iscube(-1) = true` (since `(-1)³ = -1`). -/
theorem iscube_neg_1_true :
    clever_076_iscube.iscube (-1 : i64) = RustM.ok true := by native_decide

/-- `iscube(-8) = true` (since `(-2)³ = -8`). -/
theorem iscube_neg_8_true :
    clever_076_iscube.iscube (-8 : i64) = RustM.ok true := by native_decide

/-- `iscube(-27) = true` (since `(-3)³ = -27`). -/
theorem iscube_neg_27_true :
    clever_076_iscube.iscube (-27 : i64) = RustM.ok true := by native_decide

/-- `iscube(2) = false`. -/
theorem iscube_2_false :
    clever_076_iscube.iscube (2 : i64) = RustM.ok false := by native_decide

/-- `iscube(9) = false`. -/
theorem iscube_9_false :
    clever_076_iscube.iscube (9 : i64) = RustM.ok false := by native_decide

/-- `iscube(26) = false`. -/
theorem iscube_26_false :
    clever_076_iscube.iscube (26 : i64) = RustM.ok false := by native_decide

/-- `iscube(28) = false`. -/
theorem iscube_28_false :
    clever_076_iscube.iscube (28 : i64) = RustM.ok false := by native_decide

/-! ## Branch lemmas for `cube_walks_to`.

Five reductions of the recursive definition:
  * terminate on `cube = n` (with no overflow in `k*k` or `(k*k)*k`)
  * overshoot on `cube > n`
  * recursive step on `cube < n` (with `k + 1` not overflowing)
  * failure on `k *? k` overflow
  * failure on `(k * k) *? k` overflow
  * failure on `k +? 1` overflow during the recursive step
-/

/-- `k *? k = pure (k * k)` when no overflow. -/
private theorem i64_mul_pure (a b : i64) (h_no : ¬ Int64.mulOverflow a b) :
    (a *? b : RustM i64) = pure (a * b) := by
  have h_bv : BitVec.smulOverflow a.toBitVec b.toBitVec = false := by
    cases hb : BitVec.smulOverflow a.toBitVec b.toBitVec with
    | false => rfl
    | true => exact absurd hb h_no
  show (rust_primitives.ops.arith.Mul.mul a b : RustM i64) = pure (a * b)
  show (if BitVec.smulOverflow a.toBitVec b.toBitVec then
          (.fail .integerOverflow : RustM i64)
        else pure (a * b)) = pure (a * b)
  rw [h_bv]; rfl

/-- `k *? k = .fail .integerOverflow` when it overflows. -/
private theorem i64_mul_fail (a b : i64) (h_ov : Int64.mulOverflow a b) :
    (a *? b : RustM i64) = .fail .integerOverflow := by
  have h_bv : BitVec.smulOverflow a.toBitVec b.toBitVec = true := h_ov
  show (rust_primitives.ops.arith.Mul.mul a b : RustM i64) = .fail .integerOverflow
  show (if BitVec.smulOverflow a.toBitVec b.toBitVec then
          (.fail .integerOverflow : RustM i64)
        else pure (a * b)) = _
  rw [h_bv]; rfl

/-- `k +? 1 = pure (k + 1)` when no overflow. -/
private theorem i64_add_pure (a b : i64) (h_no : ¬ Int64.addOverflow a b) :
    (a +? b : RustM i64) = pure (a + b) := by
  have h_bv : BitVec.saddOverflow a.toBitVec b.toBitVec = false := by
    cases hb : BitVec.saddOverflow a.toBitVec b.toBitVec with
    | false => rfl
    | true => exact absurd hb h_no
  show (rust_primitives.ops.arith.Add.add a b : RustM i64) = pure (a + b)
  show (if BitVec.saddOverflow a.toBitVec b.toBitVec then
          (.fail .integerOverflow : RustM i64)
        else pure (a + b)) = pure (a + b)
  rw [h_bv]; rfl

/-- `k +? 1 = .fail .integerOverflow` when it overflows. -/
private theorem i64_add_fail (a b : i64) (h_ov : Int64.addOverflow a b) :
    (a +? b : RustM i64) = .fail .integerOverflow := by
  have h_bv : BitVec.saddOverflow a.toBitVec b.toBitVec = true := h_ov
  show (rust_primitives.ops.arith.Add.add a b : RustM i64) = .fail .integerOverflow
  show (if BitVec.saddOverflow a.toBitVec b.toBitVec then
          (.fail .integerOverflow : RustM i64)
        else pure (a + b)) = _
  rw [h_bv]; rfl

/-- `-? a = pure (-a)` when `a ≠ Int64.minValue`. -/
private theorem i64_neg_pure (a : i64) (h_ne : a ≠ Int64.minValue) :
    (-? a : RustM i64) = pure (-a) := by
  show (rust_primitives.ops.arith.Neg.neg a : RustM i64) = pure (-a)
  show (if a = Int64.minValue
        then (.fail .integerOverflow : RustM i64)
        else pure (-a)) = _
  rw [if_neg h_ne]

/-! ## Integer cube arithmetic helpers (no `linarith`/`ring` available). -/

/-- For `x ≥ 1`, `x ≤ x * x * x`. -/
private theorem cube_ge_self (x : Int) (hx1 : 1 ≤ x) : x ≤ x * x * x := by
  have hx0 : 0 ≤ x := by omega
  have h_sq_ge_one : 1 ≤ x * x := by
    have h_mul : (1 : Int) * 1 ≤ x * x := Int.mul_le_mul hx1 hx1 (by decide) hx0
    simpa using h_mul
  have h_step : (1 : Int) * x ≤ (x * x) * x :=
    Int.mul_le_mul_of_nonneg_right h_sq_ge_one hx0
  simpa using h_step

/-- For `x ≥ 0`, `0 ≤ x * x * x`. -/
private theorem cube_nneg (x : Int) (hx : 0 ≤ x) : 0 ≤ x * x * x := by
  have h_sq : 0 ≤ x * x := Int.mul_nonneg hx hx
  exact Int.mul_nonneg h_sq hx

/-- For any Int `k`, `0 ≤ k * k`. -/
private theorem int_sq_nneg (k : Int) : 0 ≤ k * k := by
  by_cases hk : 0 ≤ k
  · exact Int.mul_nonneg hk hk
  · have h_neg_nneg : 0 ≤ -k := by omega
    have h := Int.mul_nonneg h_neg_nneg h_neg_nneg
    rw [Int.neg_mul_neg] at h
    exact h

/-- Cube of a negated value equals negation of the cube. -/
private theorem cube_neg (k : Int) : (-k) * (-k) * (-k) = -(k * k * k) := by
  have h1 : (-k) * (-k) = k * k := Int.neg_mul_neg k k
  calc (-k) * (-k) * (-k) = (k * k) * (-k) := by rw [h1]
    _ = -(k * k * k) := Int.mul_neg _ _

/-- Cubes are monotone on non-negative reals. -/
private theorem cube_le_cube (a b : Int) (ha : 0 ≤ a) (hab : a ≤ b) :
    a * a * a ≤ b * b * b := by
  have hb : 0 ≤ b := Int.le_trans ha hab
  have h1 : a * a ≤ b * b :=
    Int.mul_le_mul hab hab ha hb
  have h2 : a * a * a ≤ b * b * a :=
    Int.mul_le_mul_of_nonneg_right h1 ha
  have h3 : b * b * a ≤ b * b * b :=
    Int.mul_le_mul_of_nonneg_left hab (Int.mul_nonneg hb hb)
  exact Int.le_trans h2 h3

/-- Strict cube monotonicity: `a < b` and `0 ≤ a` imply `a^3 < b^3`. -/
private theorem cube_lt_cube (a b : Int) (ha : 0 ≤ a) (hab : a < b) :
    a * a * a < b * b * b := by
  have hb : 0 ≤ b := Int.le_trans ha (Int.le_of_lt hab)
  have hb_pos : 0 < b := Int.lt_of_le_of_lt ha hab
  by_cases ha0 : a = 0
  · subst ha0
    simp only [Int.mul_zero]
    have h_bb_pos : 0 < b * b := Int.mul_pos hb_pos hb_pos
    exact Int.mul_pos h_bb_pos hb_pos
  · have ha_pos : 0 < a := by omega
    have h_aa_lt_bb : a * a < b * b := by
      have h1 : a * a < a * b :=
        Int.mul_lt_mul_of_pos_left hab ha_pos
      have h2 : a * b < b * b :=
        Int.mul_lt_mul_of_pos_right hab hb_pos
      exact Int.lt_trans h1 h2
    have h_aaa_le_bba : a * a * a ≤ b * b * a :=
      Int.mul_le_mul_of_nonneg_right (Int.le_of_lt h_aa_lt_bb) ha
    have h_bba_lt_bbb : b * b * a < b * b * b :=
      Int.mul_lt_mul_of_pos_left hab (Int.mul_pos hb_pos hb_pos)
    exact Int.lt_of_le_of_lt h_aaa_le_bba h_bba_lt_bbb

/-- `cube_walks_to` returns `ok true` when the cube fits and equals `n`. -/
private theorem cube_walks_to_terminate (n k : i64)
    (h_no_kk : ¬ Int64.mulOverflow k k)
    (h_no_kkk : ¬ Int64.mulOverflow (k * k) k)
    (h_eq : (k * k * k) = n) :
    clever_076_iscube.cube_walks_to n k = RustM.ok true := by
  conv => lhs; unfold clever_076_iscube.cube_walks_to
  rw [i64_mul_pure k k h_no_kk]
  simp only [pure_bind]
  rw [i64_mul_pure (k * k) k h_no_kkk]
  simp only [pure_bind]
  have h_dec : decide (k * k * k = n) = true := decide_eq_true h_eq
  simp only [show ((k * k * k) ==? n : RustM Bool) =
                 (pure (decide ((k * k * k) = n)) : RustM Bool) from rfl,
             h_dec, pure_bind, ↓reduceIte]
  rfl

/-- `cube_walks_to` returns `ok false` when the cube fits and overshoots `n`. -/
private theorem cube_walks_to_overshoot (n k : i64)
    (h_no_kk : ¬ Int64.mulOverflow k k)
    (h_no_kkk : ¬ Int64.mulOverflow (k * k) k)
    (h_gt : n.toInt < (k * k * k).toInt) :
    clever_076_iscube.cube_walks_to n k = RustM.ok false := by
  conv => lhs; unfold clever_076_iscube.cube_walks_to
  rw [i64_mul_pure k k h_no_kk]
  simp only [pure_bind]
  rw [i64_mul_pure (k * k) k h_no_kkk]
  simp only [pure_bind]
  have h_ne : ¬ (k * k * k) = n := by
    intro he
    have : (k * k * k).toInt = n.toInt := by rw [he]
    omega
  have h_gt' : (k * k * k) > n := Int64.lt_iff_toInt_lt.mpr h_gt
  have h_dec_eq : decide ((k * k * k) = n) = false := decide_eq_false h_ne
  have h_dec_gt : decide ((k * k * k) > n) = true := decide_eq_true h_gt'
  simp only [show ((k * k * k) ==? n : RustM Bool) =
                 (pure (decide ((k * k * k) = n)) : RustM Bool) from rfl,
             show ((k * k * k) >? n : RustM Bool) =
                 (pure (decide ((k * k * k) > n)) : RustM Bool) from rfl,
             h_dec_eq, h_dec_gt, pure_bind, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- Recursive step: when the cube fits, undershoots `n`, and `k + 1` fits,
    `cube_walks_to n k = cube_walks_to n (k + 1)`. -/
private theorem cube_walks_to_step (n k : i64)
    (h_no_kk : ¬ Int64.mulOverflow k k)
    (h_no_kkk : ¬ Int64.mulOverflow (k * k) k)
    (h_lt : (k * k * k).toInt < n.toInt)
    (h_no_add : ¬ Int64.addOverflow k 1) :
    clever_076_iscube.cube_walks_to n k =
      clever_076_iscube.cube_walks_to n (k + 1) := by
  conv => lhs; unfold clever_076_iscube.cube_walks_to
  rw [i64_mul_pure k k h_no_kk]
  simp only [pure_bind]
  rw [i64_mul_pure (k * k) k h_no_kkk]
  simp only [pure_bind]
  have h_ne : ¬ (k * k * k) = n := by
    intro he
    have : (k * k * k).toInt = n.toInt := by rw [he]
    omega
  have h_not_gt : ¬ (k * k * k) > n := by
    intro hgt
    have := Int64.lt_iff_toInt_lt.mp hgt
    omega
  have h_dec_eq : decide ((k * k * k) = n) = false := decide_eq_false h_ne
  have h_dec_gt : decide ((k * k * k) > n) = false := decide_eq_false h_not_gt
  simp only [show ((k * k * k) ==? n : RustM Bool) =
                 (pure (decide ((k * k * k) = n)) : RustM Bool) from rfl,
             show ((k * k * k) >? n : RustM Bool) =
                 (pure (decide ((k * k * k) > n)) : RustM Bool) from rfl,
             h_dec_eq, h_dec_gt, pure_bind, Bool.false_eq_true, ↓reduceIte]
  rw [i64_add_pure k 1 h_no_add]
  simp only [pure_bind]

/-- Failure when the first multiplication overflows. -/
private theorem cube_walks_to_fail_mul1 (n k : i64)
    (h_ov : Int64.mulOverflow k k) :
    clever_076_iscube.cube_walks_to n k = RustM.fail .integerOverflow := by
  conv => lhs; unfold clever_076_iscube.cube_walks_to
  rw [i64_mul_fail k k h_ov]
  rfl

/-- Failure when the second multiplication overflows. -/
private theorem cube_walks_to_fail_mul2 (n k : i64)
    (h_no_kk : ¬ Int64.mulOverflow k k)
    (h_ov : Int64.mulOverflow (k * k) k) :
    clever_076_iscube.cube_walks_to n k = RustM.fail .integerOverflow := by
  conv => lhs; unfold clever_076_iscube.cube_walks_to
  rw [i64_mul_pure k k h_no_kk]
  simp only [pure_bind]
  rw [i64_mul_fail (k * k) k h_ov]
  rfl

/-- Failure when `k +? 1` overflows during the recursive step. -/
private theorem cube_walks_to_step_fail (n k : i64)
    (h_no_kk : ¬ Int64.mulOverflow k k)
    (h_no_kkk : ¬ Int64.mulOverflow (k * k) k)
    (h_lt : (k * k * k).toInt < n.toInt)
    (h_ov_add : Int64.addOverflow k 1) :
    clever_076_iscube.cube_walks_to n k = RustM.fail .integerOverflow := by
  conv => lhs; unfold clever_076_iscube.cube_walks_to
  rw [i64_mul_pure k k h_no_kk]
  simp only [pure_bind]
  rw [i64_mul_pure (k * k) k h_no_kkk]
  simp only [pure_bind]
  have h_ne : ¬ (k * k * k) = n := by
    intro he
    have : (k * k * k).toInt = n.toInt := by rw [he]
    omega
  have h_not_gt : ¬ (k * k * k) > n := by
    intro hgt
    have := Int64.lt_iff_toInt_lt.mp hgt
    omega
  have h_dec_eq : decide ((k * k * k) = n) = false := decide_eq_false h_ne
  have h_dec_gt : decide ((k * k * k) > n) = false := decide_eq_false h_not_gt
  simp only [show ((k * k * k) ==? n : RustM Bool) =
                 (pure (decide ((k * k * k) = n)) : RustM Bool) from rfl,
             show ((k * k * k) >? n : RustM Bool) =
                 (pure (decide ((k * k * k) > n)) : RustM Bool) from rfl,
             h_dec_eq, h_dec_gt, pure_bind, Bool.false_eq_true, ↓reduceIte]
  rw [i64_add_fail k 1 h_ov_add]
  rfl

/-! ## Soundness workhorse for `cube_walks_to`.

If `cube_walks_to n k` returns `ok true`, with `n ≥ 0` and `k ≥ 0`,
then there is some non-negative `k0` with `k0 * k0 * k0 = n.toInt`.

The measure is `(n.toInt + 1 - k.toInt).toNat`, which strictly decreases
on each recursive step (since `k.toInt < n.toInt` in the recurse branch). -/

private theorem cube_walks_to_sound_aux (n : i64) (h_n_nneg : 0 ≤ n.toInt) :
    ∀ (m : Nat) (k : i64),
      0 ≤ k.toInt →
      (n.toInt + 1 - k.toInt).toNat ≤ m →
      clever_076_iscube.cube_walks_to n k = RustM.ok true →
      ∃ k0 : Int, 0 ≤ k0 ∧ k0 * k0 * k0 = n.toInt := by
  intro m
  induction m with
  | zero =>
    intro k h_k_nneg h_measure h_call
    -- (n+1-k).toNat = 0, so n+1 ≤ k, i.e., k ≥ n+1, i.e., k > n
    have h_measure_zero : (n.toInt + 1 - k.toInt).toNat = 0 := Nat.le_zero.mp h_measure
    have h_diff_le_zero : n.toInt + 1 - k.toInt ≤ 0 :=
      Int.toNat_eq_zero.mp h_measure_zero
    have h_k_gt_n : k.toInt > n.toInt := by omega
    -- Cases on cube overflow
    by_cases h_ov1 : Int64.mulOverflow k k
    · rw [cube_walks_to_fail_mul1 n k h_ov1] at h_call
      cases h_call
    by_cases h_ov2 : Int64.mulOverflow (k * k) k
    · rw [cube_walks_to_fail_mul2 n k h_ov1 h_ov2] at h_call
      cases h_call
    -- Cube fits.  Compute cube.toInt = k.toInt^3.
    have h_kk_toInt : (k * k).toInt = k.toInt * k.toInt :=
      Int64.toInt_mul_of_not_mulOverflow h_ov1
    have h_kkk_toInt : ((k * k) * k).toInt = k.toInt * k.toInt * k.toInt := by
      rw [Int64.toInt_mul_of_not_mulOverflow h_ov2, h_kk_toInt]
    -- Now k ≥ 1 (since k > n ≥ 0)
    have h_k_ge_1 : 1 ≤ k.toInt := by omega
    -- k^3 ≥ k > n
    have h_kkk_gt_n : (k * k * k).toInt > n.toInt := by
      rw [h_kkk_toInt]
      have h_k_le_cube : k.toInt ≤ k.toInt * k.toInt * k.toInt :=
        cube_ge_self k.toInt h_k_ge_1
      omega
    -- So overshoot fires, contradiction with ok true
    rw [cube_walks_to_overshoot n k h_ov1 h_ov2 h_kkk_gt_n] at h_call
    cases h_call
  | succ m ih =>
    intro k h_k_nneg h_measure h_call
    by_cases h_ov1 : Int64.mulOverflow k k
    · rw [cube_walks_to_fail_mul1 n k h_ov1] at h_call
      cases h_call
    by_cases h_ov2 : Int64.mulOverflow (k * k) k
    · rw [cube_walks_to_fail_mul2 n k h_ov1 h_ov2] at h_call
      cases h_call
    have h_kk_toInt : (k * k).toInt = k.toInt * k.toInt :=
      Int64.toInt_mul_of_not_mulOverflow h_ov1
    have h_kkk_toInt : ((k * k) * k).toInt = k.toInt * k.toInt * k.toInt := by
      rw [Int64.toInt_mul_of_not_mulOverflow h_ov2, h_kk_toInt]
    -- Case-split on cube vs n
    by_cases h_lt : (k * k * k).toInt < n.toInt
    · -- Recurse case
      by_cases h_ov_add : Int64.addOverflow k 1
      · rw [cube_walks_to_step_fail n k h_ov1 h_ov2 h_lt h_ov_add] at h_call
        cases h_call
      rw [cube_walks_to_step n k h_ov1 h_ov2 h_lt h_ov_add] at h_call
      -- Apply IH
      have h_k1_toInt : (k + 1).toInt = k.toInt + 1 := by
        rw [Int64.toInt_add_of_not_addOverflow h_ov_add, i64_one_toInt]
      have h_k1_nneg : 0 ≤ (k + 1).toInt := by rw [h_k1_toInt]; omega
      have h_kkk_lt : k.toInt * k.toInt * k.toInt < n.toInt := by
        rw [← h_kkk_toInt]; exact h_lt
      have h_k_le_n : k.toInt ≤ n.toInt := by
        by_cases hk0 : k.toInt = 0
        · rw [hk0] at h_kkk_lt
          simp at h_kkk_lt
          omega
        · have h_k_ge_1 : 1 ≤ k.toInt := by omega
          have h_k_le_cube : k.toInt ≤ k.toInt * k.toInt * k.toInt :=
            cube_ge_self k.toInt h_k_ge_1
          omega
      have h_diff_nn : 0 ≤ n.toInt + 1 - k.toInt := by omega
      have h_measure_new : (n.toInt + 1 - (k + 1).toInt).toNat ≤ m := by
        rw [h_k1_toInt]
        omega
      exact ih (k + 1) h_k1_nneg h_measure_new h_call
    · -- Not less.  Sub-cases: equal (terminate) or greater (overshoot).
      by_cases h_eq_or_gt : (k * k * k).toInt = n.toInt
      · -- Terminate: witness k.toInt
        refine ⟨k.toInt, h_k_nneg, ?_⟩
        rw [← h_kkk_toInt]
        exact h_eq_or_gt
      · -- Overshoot: contradiction
        have h_gt : n.toInt < (k * k * k).toInt := by omega
        rw [cube_walks_to_overshoot n k h_ov1 h_ov2 h_gt] at h_call
        cases h_call

/-! ## Bounded no-overflow helpers.

When `k.toInt ∈ [0, 1025]`, all of `k * k`, `(k * k) * k`, and `k + 1`
remain well within the i64 range, so the corresponding operations do
not overflow.  These bounds match the walk's range in the
completeness and rejection auxes (where `k` walks from `0` toward at
most `1025`). -/

private theorem cube_no_overflow (k : i64) (h_lo : 0 ≤ k.toInt) (h_hi : k.toInt ≤ 1025) :
    ¬ Int64.mulOverflow k k ∧ ¬ Int64.mulOverflow (k * k) k ∧
    (k * k).toInt = k.toInt * k.toInt ∧
    ((k * k) * k).toInt = k.toInt * k.toInt * k.toInt := by
  have h_sq_le : k.toInt * k.toInt ≤ 1025 * 1025 :=
    Int.mul_le_mul h_hi h_hi h_lo (by decide)
  have h_sq_nneg : 0 ≤ k.toInt * k.toInt := Int.mul_nonneg h_lo h_lo
  have h_no_mul1 : ¬ Int64.mulOverflow k k := by
    intro hov
    rw [Int64.mulOverflow_iff, h63_eq] at hov
    rcases hov with hp | hn
    · have h63 : (1025 : Int) * 1025 < 2 ^ 63 := by decide
      omega
    · omega
  have h_kk_toInt : (k * k).toInt = k.toInt * k.toInt :=
    Int64.toInt_mul_of_not_mulOverflow h_no_mul1
  have h_cube_le : k.toInt * k.toInt * k.toInt ≤ 1025 * 1025 * 1025 := by
    have h1 : k.toInt * k.toInt * k.toInt ≤ 1025 * 1025 * k.toInt :=
      Int.mul_le_mul_of_nonneg_right h_sq_le h_lo
    have h2 : 1025 * 1025 * k.toInt ≤ 1025 * 1025 * 1025 :=
      Int.mul_le_mul_of_nonneg_left h_hi (by decide)
    exact Int.le_trans h1 h2
  have h_cube_nneg : 0 ≤ k.toInt * k.toInt * k.toInt :=
    Int.mul_nonneg h_sq_nneg h_lo
  have h_no_mul2 : ¬ Int64.mulOverflow (k * k) k := by
    intro hov
    rw [Int64.mulOverflow_iff, h63_eq] at hov
    rw [h_kk_toInt] at hov
    rcases hov with hp | hn
    · have h63 : (1025 : Int) * 1025 * 1025 < 2 ^ 63 := by decide
      omega
    · omega
  have h_kkk_toInt : ((k * k) * k).toInt = k.toInt * k.toInt * k.toInt := by
    rw [Int64.toInt_mul_of_not_mulOverflow h_no_mul2, h_kk_toInt]
  exact ⟨h_no_mul1, h_no_mul2, h_kk_toInt, h_kkk_toInt⟩

/-- When `k.toInt + 1 < 2^63`, the addition `k +? 1` does not overflow. -/
private theorem add_one_no_overflow (k : i64) (h_hi : k.toInt + 1 < 2 ^ 63) :
    ¬ Int64.addOverflow k 1 := by
  intro hov
  rw [Int64.addOverflow_iff, i64_one_toInt, h63_eq] at hov
  have h_lo := i64_toInt_ge k
  rcases hov with hp | hn
  · omega
  · omega

/-! ## Completeness workhorse for `cube_walks_to`.

If `target` is a non-negative integer with `target ≤ 1024` and
`target * target * target = n.toInt`, then for every `k` with
`0 ≤ k.toInt ≤ target`, `cube_walks_to n k = ok true`.

The measure is `(target - k.toInt).toNat`, which decreases by 1 on
each recursive step. -/

private theorem cube_walks_to_complete (n : i64) (target : Int)
    (h_target_nneg : 0 ≤ target)
    (h_target_bound : target ≤ 1024)
    (h_target_eq : target * target * target = n.toInt) :
    ∀ (m : Nat) (k : i64),
      0 ≤ k.toInt →
      k.toInt ≤ target →
      (target - k.toInt).toNat ≤ m →
      clever_076_iscube.cube_walks_to n k = RustM.ok true := by
  intro m
  induction m with
  | zero =>
    intro k h_k_nneg h_k_le_target h_measure
    have h_diff_zero : target - k.toInt ≤ 0 :=
      Int.toNat_eq_zero.mp (Nat.le_zero.mp h_measure)
    have h_k_eq : k.toInt = target := by omega
    have h_k_le_1025 : k.toInt ≤ 1025 := by omega
    obtain ⟨h_no_mul1, h_no_mul2, h_kk_toInt, h_kkk_toInt⟩ :=
      cube_no_overflow k h_k_nneg h_k_le_1025
    have h_eq : (k * k * k) = n := by
      apply Int64.toInt_inj.mp
      rw [h_kkk_toInt, h_k_eq, h_target_eq]
    exact cube_walks_to_terminate n k h_no_mul1 h_no_mul2 h_eq
  | succ m ih =>
    intro k h_k_nneg h_k_le_target h_measure
    by_cases h_k_eq : k.toInt = target
    · have h_k_le_1025 : k.toInt ≤ 1025 := by omega
      obtain ⟨h_no_mul1, h_no_mul2, h_kk_toInt, h_kkk_toInt⟩ :=
        cube_no_overflow k h_k_nneg h_k_le_1025
      have h_eq : (k * k * k) = n := by
        apply Int64.toInt_inj.mp
        rw [h_kkk_toInt, h_k_eq, h_target_eq]
      exact cube_walks_to_terminate n k h_no_mul1 h_no_mul2 h_eq
    -- k < target
    have h_k_lt : k.toInt < target := by omega
    have h_k_le_1025 : k.toInt ≤ 1025 := by omega
    obtain ⟨h_no_mul1, h_no_mul2, h_kk_toInt, h_kkk_toInt⟩ :=
      cube_no_overflow k h_k_nneg h_k_le_1025
    have h_lt : (k * k * k).toInt < n.toInt := by
      rw [h_kkk_toInt, ← h_target_eq]
      exact cube_lt_cube k.toInt target h_k_nneg h_k_lt
    have h_no_add : ¬ Int64.addOverflow k 1 := by
      apply add_one_no_overflow
      have : k.toInt ≤ 1024 := by omega
      have h_bound : (1024 : Int) + 1 < 2 ^ 63 := by decide
      omega
    rw [cube_walks_to_step n k h_no_mul1 h_no_mul2 h_lt h_no_add]
    have h_k1_toInt : (k + 1).toInt = k.toInt + 1 := by
      rw [Int64.toInt_add_of_not_addOverflow h_no_add, i64_one_toInt]
    apply ih (k + 1)
    · rw [h_k1_toInt]; omega
    · rw [h_k1_toInt]; omega
    · rw [h_k1_toInt]; omega

/-! ## Rejection workhorse for `cube_walks_to`.

If `0 ≤ n.toInt ≤ 2^30` and `n.toInt` is not a non-negative integer
cube, then for every `k` with `0 ≤ k.toInt ≤ 1025`,
`cube_walks_to n k = ok false`.

The measure is `(1025 - k.toInt).toNat`.  At `k = 1025`, the cube
`k^3 = 1025^3 > 2^30 ≥ n`, so the walk overshoots and terminates with
`false`. -/

private theorem cube_walks_to_reject (n : i64)
    (h_n_nneg : 0 ≤ n.toInt) (h_n_bound : n.toInt ≤ 2 ^ 30)
    (h_not_cube : ¬ ∃ k0 : Int, 0 ≤ k0 ∧ k0 * k0 * k0 = n.toInt) :
    ∀ (m : Nat) (k : i64),
      0 ≤ k.toInt →
      k.toInt ≤ 1025 →
      (1025 - k.toInt).toNat ≤ m →
      clever_076_iscube.cube_walks_to n k = RustM.ok false := by
  intro m
  induction m with
  | zero =>
    intro k h_k_nneg h_k_le_1025 h_measure
    have h_diff_zero : 1025 - k.toInt ≤ 0 :=
      Int.toNat_eq_zero.mp (Nat.le_zero.mp h_measure)
    have h_k_eq : k.toInt = 1025 := by omega
    obtain ⟨h_no_mul1, h_no_mul2, h_kk_toInt, h_kkk_toInt⟩ :=
      cube_no_overflow k h_k_nneg h_k_le_1025
    have h_gt : n.toInt < (k * k * k).toInt := by
      rw [h_kkk_toInt, h_k_eq]
      have : (1025 : Int) * 1025 * 1025 > 2 ^ 30 := by decide
      omega
    exact cube_walks_to_overshoot n k h_no_mul1 h_no_mul2 h_gt
  | succ m ih =>
    intro k h_k_nneg h_k_le_1025 h_measure
    by_cases h_k_eq : k.toInt = 1025
    · obtain ⟨h_no_mul1, h_no_mul2, h_kk_toInt, h_kkk_toInt⟩ :=
        cube_no_overflow k h_k_nneg h_k_le_1025
      have h_gt : n.toInt < (k * k * k).toInt := by
        rw [h_kkk_toInt, h_k_eq]
        have : (1025 : Int) * 1025 * 1025 > 2 ^ 30 := by decide
        omega
      exact cube_walks_to_overshoot n k h_no_mul1 h_no_mul2 h_gt
    have h_k_lt_1025 : k.toInt < 1025 := by omega
    obtain ⟨h_no_mul1, h_no_mul2, h_kk_toInt, h_kkk_toInt⟩ :=
      cube_no_overflow k h_k_nneg h_k_le_1025
    -- Case-split on cube vs n
    by_cases h_lt : (k * k * k).toInt < n.toInt
    · -- recurse
      have h_no_add : ¬ Int64.addOverflow k 1 := by
        apply add_one_no_overflow
        have h_bound : (1024 : Int) + 1 < 2 ^ 63 := by decide
        omega
      rw [cube_walks_to_step n k h_no_mul1 h_no_mul2 h_lt h_no_add]
      have h_k1_toInt : (k + 1).toInt = k.toInt + 1 := by
        rw [Int64.toInt_add_of_not_addOverflow h_no_add, i64_one_toInt]
      apply ih (k + 1)
      · rw [h_k1_toInt]; omega
      · rw [h_k1_toInt]; omega
      · rw [h_k1_toInt]; omega
    by_cases h_eq : (k * k * k).toInt = n.toInt
    · -- terminate true — contradiction with h_not_cube
      exfalso
      apply h_not_cube
      refine ⟨k.toInt, h_k_nneg, ?_⟩
      rw [← h_kkk_toInt]; exact h_eq
    -- cube > n: overshoot
    have h_gt : n.toInt < (k * k * k).toInt := by omega
    exact cube_walks_to_overshoot n k h_no_mul1 h_no_mul2 h_gt

/-! ## Soundness: every `ok true` is witnessed by an integer cube root.

If `iscube n` returns `true`, there exists an integer `k` with
`k * k * k = n.toInt`.  Universal: a successful `ok true` already
constrains the inner trace of `cube` values to expose the witness;
for `n < 0` the witness is the negation of the inner walk's terminal
counter.  Captures the proptest `soundness`. -/
theorem iscube_sound (n : i64)
    (h : clever_076_iscube.iscube n = RustM.ok true) :
    ∃ k : Int, k * k * k = n.toInt := by
  unfold clever_076_iscube.iscube at h
  simp only [show (n <? (0 : i64) : RustM Bool) = pure (decide (n < (0 : i64))) from rfl,
             pure_bind] at h
  by_cases hn : n.toInt < 0
  · -- Negative branch: -? n then cube_walks_to (-n) 0
    have h_n_lt : n < (0 : i64) := by
      apply Int64.lt_iff_toInt_lt.mpr
      rw [i64_zero_toInt]; exact hn
    have h_dec : decide (n < (0 : i64)) = true := decide_eq_true h_n_lt
    simp only [h_dec, ↓reduceIte] at h
    -- Show n ≠ Int64.minValue (otherwise -? n fails)
    by_cases h_min : n = Int64.minValue
    · exfalso
      rw [h_min] at h
      have h_neg_fail : (-? (Int64.minValue : i64) : RustM i64) = .fail .integerOverflow := by
        show (rust_primitives.ops.arith.Neg.neg (Int64.minValue : i64) : RustM i64)
              = .fail .integerOverflow
        show (if (Int64.minValue : i64) = Int64.minValue
              then (.fail .integerOverflow : RustM i64)
              else pure (-Int64.minValue)) = _
        rw [if_pos rfl]
      rw [h_neg_fail] at h
      cases h
    have h_neg_pure : (-? n : RustM i64) = pure (-n) := i64_neg_pure n h_min
    rw [h_neg_pure] at h
    simp only [pure_bind] at h
    have h_neg_toInt : (-n).toInt = -n.toInt := Int64.toInt_neg_of_ne_intMin h_min
    have h_neg_nneg : 0 ≤ (-n).toInt := by rw [h_neg_toInt]; omega
    have h_0_nneg : 0 ≤ (0 : i64).toInt := by rw [i64_zero_toInt]; decide
    have h_measure :
        ((-n).toInt + 1 - (0 : i64).toInt).toNat ≤ ((-n).toInt + 1).toNat := by
      rw [i64_zero_toInt]; omega
    rcases cube_walks_to_sound_aux (-n) h_neg_nneg ((-n).toInt + 1).toNat
        (0 : i64) h_0_nneg h_measure h with ⟨k0, h_k0_nneg, h_k0_eq⟩
    -- Witness for n.toInt is -k0
    refine ⟨-k0, ?_⟩
    have h_neg_cube : (-k0) * (-k0) * (-k0) = -(k0 * k0 * k0) := by
      have step1 : (-k0) * (-k0) = k0 * k0 := Int.neg_mul_neg k0 k0
      calc (-k0) * (-k0) * (-k0) = (k0 * k0) * (-k0) := by rw [step1]
        _ = -(k0 * k0 * k0) := Int.mul_neg _ _
    rw [h_neg_cube, h_k0_eq, h_neg_toInt]
    omega
  · -- Non-negative branch: cube_walks_to n 0
    have h_n_nneg : 0 ≤ n.toInt := by omega
    have h_not_lt : ¬ n < (0 : i64) := by
      intro hlt
      have := Int64.lt_iff_toInt_lt.mp hlt
      rw [i64_zero_toInt] at this
      omega
    have h_dec : decide (n < (0 : i64)) = false := decide_eq_false h_not_lt
    simp only [h_dec, Bool.false_eq_true, ↓reduceIte] at h
    have h_0_nneg : 0 ≤ (0 : i64).toInt := by rw [i64_zero_toInt]; decide
    have h_measure :
        (n.toInt + 1 - (0 : i64).toInt).toNat ≤ (n.toInt + 1).toNat := by
      rw [i64_zero_toInt]; omega
    rcases cube_walks_to_sound_aux n h_n_nneg (n.toInt + 1).toNat
        (0 : i64) h_0_nneg h_measure h with ⟨k0, h_k0_nneg, h_k0_eq⟩
    exact ⟨k0, h_k0_eq⟩

/-! ## Completeness: every actual cube is recognised.

For every integer `k` with `|k| ≤ 1024`, `iscube` on the i64 lift of
`k³` returns `true`.  The bound keeps both the input and every
intermediate cube within i64 (since `1024^3 = 2^30 ≪ 2^63`).
Captures the proptest `completeness`. -/
theorem iscube_actual_cubes_recognized (k : Int)
    (h_lo : -1024 ≤ k) (h_hi : k ≤ 1024) :
    clever_076_iscube.iscube (Int64.ofInt (k * k * k)) = RustM.ok true := by
  -- Bounds on k*k*k
  have h_kkk_le_pos : k * k * k ≤ 1024 * 1024 * 1024 := by
    by_cases hk : 0 ≤ k
    · exact cube_le_cube k 1024 hk h_hi
    · have h_neg : k < 0 := by omega
      have h_sq_nneg : 0 ≤ k * k := int_sq_nneg k
      have h_le_zero : k ≤ 0 := by omega
      have h_kkk_nonpos : k * k * k ≤ 0 :=
        Int.mul_nonpos_of_nonneg_of_nonpos h_sq_nneg h_le_zero
      have h_pos_bound : (0 : Int) ≤ 1024 * 1024 * 1024 := by decide
      omega
  have h_kkk_ge_neg : -(1024 * 1024 * 1024 : Int) ≤ k * k * k := by
    by_cases hk : 0 ≤ k
    · have h_kkk_nneg : 0 ≤ k * k * k := cube_nneg k hk
      have h_neg_bound : -(1024 * 1024 * 1024 : Int) ≤ 0 := by decide
      omega
    · have h_jpos : 0 ≤ -k := by omega
      have h_jle : -k ≤ 1024 := by omega
      have h_jcube_le : (-k) * (-k) * (-k) ≤ 1024 * 1024 * 1024 :=
        cube_le_cube (-k) 1024 h_jpos h_jle
      rw [cube_neg] at h_jcube_le
      omega
  have h_kkk_lo : -(2^63 : Int) ≤ k * k * k := by
    have h_pow : -(2^63 : Int) ≤ -(1024 * 1024 * 1024 : Int) := by decide
    omega
  have h_kkk_hi : k * k * k < 2^63 := by
    have h_pow : (1024 * 1024 * 1024 : Int) < 2^63 := by decide
    omega
  -- Compute n.toInt
  have h_n_toInt : (Int64.ofInt (k * k * k) : i64).toInt = k * k * k :=
    Int64.toInt_ofInt_of_le h_kkk_lo h_kkk_hi
  -- Unfold iscube
  unfold clever_076_iscube.iscube
  simp only [show ((Int64.ofInt (k * k * k) : i64) <? (0 : i64) : RustM Bool) =
                 pure (decide ((Int64.ofInt (k * k * k) : i64) < (0 : i64))) from rfl,
             pure_bind]
  -- Case-split on sign of k * k * k
  by_cases h_neg : k * k * k < 0
  · -- Negative branch
    have h_n_lt_0 : (Int64.ofInt (k * k * k) : i64) < (0 : i64) := by
      apply Int64.lt_iff_toInt_lt.mpr
      rw [h_n_toInt, i64_zero_toInt]; exact h_neg
    have h_dec : decide ((Int64.ofInt (k * k * k) : i64) < (0 : i64)) = true :=
      decide_eq_true h_n_lt_0
    simp only [h_dec, ↓reduceIte]
    -- n ≠ Int64.minValue since n.toInt ≥ -2^30 > -2^63
    have h_n_ne_min : (Int64.ofInt (k * k * k) : i64) ≠ Int64.minValue := by
      intro h_eq
      have h_t : (Int64.ofInt (k * k * k) : i64).toInt = Int64.minValue.toInt := by rw [h_eq]
      rw [h_n_toInt] at h_t
      have h_min : Int64.minValue.toInt = -(2^63 : Int) := by decide
      rw [h_min] at h_t
      -- h_t : k*k*k = -2^63, but k*k*k ≥ -1024^3 = -2^30 > -2^63
      have h_neg_bound : (-(1024 * 1024 * 1024 : Int)) > -(2^63 : Int) := by decide
      omega
    have h_neg_pure :
        (-? (Int64.ofInt (k * k * k) : i64) : RustM i64) =
          pure (-(Int64.ofInt (k * k * k) : i64)) := i64_neg_pure _ h_n_ne_min
    rw [h_neg_pure]
    simp only [pure_bind]
    -- Now: cube_walks_to (-n) 0 = ok true
    -- Use complete with target = -k.
    -- Note: k < 0 (since k*k*k < 0), so target = -k ≥ 1.
    have h_k_lt_0 : k < 0 := by
      by_cases hk : 0 ≤ k
      · exfalso
        have h_kkk_nneg : 0 ≤ k * k * k := cube_nneg k hk
        omega
      · omega
    have h_target_nneg : 0 ≤ -k := by omega
    have h_target_bound : -k ≤ 1024 := by omega
    have h_neg_n_toInt :
        (-(Int64.ofInt (k * k * k) : i64)).toInt = -(k * k * k) := by
      rw [Int64.toInt_neg_of_ne_intMin h_n_ne_min, h_n_toInt]
    have h_target_eq : (-k) * (-k) * (-k) = (-(Int64.ofInt (k * k * k) : i64)).toInt := by
      rw [cube_neg, h_neg_n_toInt]
    have h_0_nneg : 0 ≤ (0 : i64).toInt := by rw [i64_zero_toInt]; decide
    have h_0_le_target : (0 : i64).toInt ≤ -k := by rw [i64_zero_toInt]; exact h_target_nneg
    have h_measure : ((-k) - (0 : i64).toInt).toNat ≤ (-k).toNat := by
      rw [i64_zero_toInt]; omega
    exact cube_walks_to_complete _ (-k) h_target_nneg h_target_bound h_target_eq
      (-k).toNat (0 : i64) h_0_nneg h_0_le_target h_measure
  · -- Non-negative branch: k * k * k ≥ 0
    have h_n_ge_0 : (0 : i64) ≤ (Int64.ofInt (k * k * k) : i64) := by
      apply Int64.le_iff_toInt_le.mpr
      rw [h_n_toInt, i64_zero_toInt]; omega
    have h_not_lt : ¬ (Int64.ofInt (k * k * k) : i64) < (0 : i64) := by
      intro hlt
      have := Int64.lt_iff_toInt_lt.mp hlt
      rw [h_n_toInt, i64_zero_toInt] at this
      omega
    have h_dec : decide ((Int64.ofInt (k * k * k) : i64) < (0 : i64)) = false :=
      decide_eq_false h_not_lt
    simp only [h_dec, Bool.false_eq_true, ↓reduceIte]
    -- Use complete with target = k (must be ≥ 0)
    have h_k_nneg : 0 ≤ k := by
      by_cases hk : 0 ≤ k
      · exact hk
      · exfalso
        have hk' : k < 0 := by omega
        have h_sq_pos : 0 < k * k := by
          have h_neg_pos : 0 < -k := by omega
          have h_neg_sq : 0 < (-k) * (-k) := Int.mul_pos h_neg_pos h_neg_pos
          rw [Int.neg_mul_neg] at h_neg_sq
          exact h_neg_sq
        have h_kkk_neg : k * k * k < 0 :=
          Int.mul_neg_of_pos_of_neg h_sq_pos hk'
        omega
    have h_target_eq : k * k * k = (Int64.ofInt (k * k * k) : i64).toInt := h_n_toInt.symm
    have h_0_nneg : 0 ≤ (0 : i64).toInt := by rw [i64_zero_toInt]; decide
    have h_0_le_k : (0 : i64).toInt ≤ k := by rw [i64_zero_toInt]; exact h_k_nneg
    have h_measure : (k - (0 : i64).toInt).toNat ≤ k.toNat := by
      rw [i64_zero_toInt]; omega
    exact cube_walks_to_complete _ k h_k_nneg h_hi h_target_eq
      k.toNat (0 : i64) h_0_nneg h_0_le_k h_measure

/-! ## Non-recognition on the safe range.

If `n.toInt ∈ [-2^30, 2^30]` and `n` is not a perfect integer cube,
`iscube n` returns `false`.  The bound matches the proptest's
`matches_brute_force` range and keeps every cube computed during the
walk inside i64; it also rules out `n = i64::MIN` so the wrapper's
`-? n` cannot panic.  Together with `iscube_actual_cubes_recognized`
and `iscube_sound`, captures the bidirectional content of the
`matches_brute_force` proptest. -/
theorem iscube_non_cubes_rejected (n : i64)
    (h_lo : -(2 ^ 30 : Int) ≤ n.toInt)
    (h_hi : n.toInt ≤ 2 ^ 30)
    (h_not_cube : ¬ ∃ k : Int, k * k * k = n.toInt) :
    clever_076_iscube.iscube n = RustM.ok false := by
  unfold clever_076_iscube.iscube
  simp only [show (n <? (0 : i64) : RustM Bool) = pure (decide (n < (0 : i64))) from rfl,
             pure_bind]
  by_cases hn : n.toInt < 0
  · -- Negative branch
    have h_n_lt_0 : n < (0 : i64) := by
      apply Int64.lt_iff_toInt_lt.mpr
      rw [i64_zero_toInt]; exact hn
    have h_dec : decide (n < (0 : i64)) = true := decide_eq_true h_n_lt_0
    simp only [h_dec, ↓reduceIte]
    have h_n_ne_min : n ≠ Int64.minValue := by
      intro h_eq
      have h_t : n.toInt = Int64.minValue.toInt := by rw [h_eq]
      have h_min : Int64.minValue.toInt = -(2^63 : Int) := by decide
      rw [h_min] at h_t
      have h_bound : -(2 ^ 30 : Int) > -(2^63 : Int) := by decide
      omega
    have h_neg_pure : (-? n : RustM i64) = pure (-n) := i64_neg_pure n h_n_ne_min
    rw [h_neg_pure]
    simp only [pure_bind]
    -- Now: cube_walks_to (-n) 0 = ok false
    have h_neg_toInt : (-n).toInt = -n.toInt := Int64.toInt_neg_of_ne_intMin h_n_ne_min
    have h_neg_nneg : 0 ≤ (-n).toInt := by rw [h_neg_toInt]; omega
    have h_neg_bound : (-n).toInt ≤ 2 ^ 30 := by rw [h_neg_toInt]; omega
    have h_not_cube_neg : ¬ ∃ k0 : Int, 0 ≤ k0 ∧ k0 * k0 * k0 = (-n).toInt := by
      intro ⟨k0, _, hk0⟩
      apply h_not_cube
      refine ⟨-k0, ?_⟩
      rw [cube_neg, hk0, h_neg_toInt]
      omega
    have h_0_nneg : 0 ≤ (0 : i64).toInt := by rw [i64_zero_toInt]; decide
    have h_0_le_1025 : (0 : i64).toInt ≤ 1025 := by rw [i64_zero_toInt]; decide
    have h_measure : (1025 - (0 : i64).toInt).toNat ≤ 1025 := by
      rw [i64_zero_toInt]; decide
    exact cube_walks_to_reject (-n) h_neg_nneg h_neg_bound h_not_cube_neg
      1025 (0 : i64) h_0_nneg h_0_le_1025 h_measure
  · -- Non-negative branch
    have h_n_nneg : 0 ≤ n.toInt := by omega
    have h_not_lt : ¬ n < (0 : i64) := by
      intro hlt
      have := Int64.lt_iff_toInt_lt.mp hlt
      rw [i64_zero_toInt] at this
      omega
    have h_dec : decide (n < (0 : i64)) = false := decide_eq_false h_not_lt
    simp only [h_dec, Bool.false_eq_true, ↓reduceIte]
    -- Now: cube_walks_to n 0 = ok false
    have h_not_cube_n : ¬ ∃ k0 : Int, 0 ≤ k0 ∧ k0 * k0 * k0 = n.toInt := by
      intro ⟨k0, _, hk0⟩
      exact h_not_cube ⟨k0, hk0⟩
    have h_0_nneg : 0 ≤ (0 : i64).toInt := by rw [i64_zero_toInt]; decide
    have h_0_le_1025 : (0 : i64).toInt ≤ 1025 := by rw [i64_zero_toInt]; decide
    have h_measure : (1025 - (0 : i64).toInt).toNat ≤ 1025 := by
      rw [i64_zero_toInt]; decide
    exact cube_walks_to_reject n h_n_nneg h_hi h_not_cube_n
      1025 (0 : i64) h_0_nneg h_0_le_1025 h_measure

end Clever_076_iscubeObligations
