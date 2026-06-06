-- Companion obligations file for the `align_to_usize` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import align_to_usize

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Align_to_usizeObligations

open align_to_usize

/-! ### Helper lemmas (internal scaffolding)

These `private theorem`s reduce the monadic `RustM` plumbing of the
extracted `align_to` / `from_size_alignment` / `max_size_for_align` /
`is_power_of_two_usize` so the public obligations can be discharged. -/

/-- `RustM.ok` is `pure`, so binding it just applies the continuation. -/
private theorem ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    (RustM.ok a) >>= f = f a := rfl

/-- `pure` in `RustM` is `RustM.ok`. -/
private theorem pure_eq_ok {α : Type} (a : α) :
    (pure a : RustM α) = RustM.ok a := rfl

/-- The Rust `>` extracts to `pure (decide (a > b))`. -/
private theorem hgt (a b : usize) :
    (a >? b) = RustM.ok (decide (a > b)) := rfl

/-- `2^63` as a `usize` literal has `toNat = 2^63` (it fits in 64 bits). -/
private theorem c63_toNat :
    (9223372036854775808 : usize).toNat = 9223372036854775808 := by simp

/-- Rust subtraction does not panic when there is no underflow. -/
private theorem hsub_ok (a b : usize) (hba : b.toNat ≤ a.toNat) :
    (a -? b) = RustM.ok (a - b) := by
  have hno : ¬ BitVec.usubOverflow a.toBitVec b.toBitVec := by
    intro hov
    have hso : USize64.subOverflow a b := hov
    rw [USize64.subOverflow_iff] at hso
    omega
  show (if BitVec.usubOverflow a.toBitVec b.toBitVec
        then (RustM.fail Error.integerOverflow : RustM usize)
        else pure (a - b)) = RustM.ok (a - b)
  rw [if_neg hno]
  rfl

/-- A non-zero `usize` is at least `1`. -/
private theorem one_le_of_ne_zero (x : usize) (hx : x ≠ 0) :
    (1 : usize).toNat ≤ x.toNat := by
  have h1 : (1 : usize).toNat = 1 := by simp
  have h0 : (0 : usize).toNat = 0 := by simp
  rw [h1]
  rcases Nat.eq_zero_or_pos x.toNat with hz | hp
  · exact absurd (USize64.toNat_inj.mp (by rw [hz, h0])) hx
  · omega

/-- `max_size_for_align` is total whenever `align ≤ 2^63` (no underflow). -/
private theorem msfa_ok (align : usize)
    (hal : align.toNat ≤ 9223372036854775808) :
    max_size_for_align align
      = RustM.ok ((9223372036854775808 : usize) - align) := by
  unfold max_size_for_align
  apply hsub_ok
  rw [c63_toNat]
  exact hal

/-- Equational form of `is_power_of_two_usize` for non-zero inputs. The
    extracted body evaluates `x - 1` *unconditionally* (the Rust `&&`
    short-circuit is gone), so totality needs `x ≠ 0`. -/
private theorem ipow2_unfold (x : usize) (hx : x ≠ 0) :
    is_power_of_two_usize x
      = RustM.ok ((x != 0) && ((x &&& (x - 1)) == 0)) := by
  unfold is_power_of_two_usize
  simp only [rust_primitives.cmp.ne, rust_primitives.cmp.eq,
             rust_primitives.hax.logical_op.and, pure_bind]
  rw [hsub_ok x (1 : usize) (one_le_of_ne_zero x hx)]
  rfl

/-- `0 -? 1` underflows and panics (no short-circuit in the extraction). -/
private theorem sub_under_fail :
    ((0 : usize) -? (1 : usize)) = RustM.fail Error.integerOverflow := by
  have hov : BitVec.usubOverflow (0 : usize).toBitVec (1 : usize).toBitVec = true := by
    have hso : USize64.subOverflow (0 : usize) (1 : usize) = true := by
      rw [USize64.subOverflow_iff]; simp
    simpa [USize64.subOverflow] using hso
  show (if BitVec.usubOverflow (0 : usize).toBitVec (1 : usize).toBitVec
        then (RustM.fail Error.integerOverflow : RustM usize)
        else pure ((0 : usize) - 1)) = RustM.fail Error.integerOverflow
  rw [hov]
  rfl

/-- `is_power_of_two_usize 0` panics: the unconditional `0 - 1` underflows. -/
private theorem is_pow2_zero :
    is_power_of_two_usize (0 : usize) = RustM.fail Error.integerOverflow := by
  unfold is_power_of_two_usize
  simp only [rust_primitives.cmp.ne, rust_primitives.cmp.eq,
             rust_primitives.hax.logical_op.and, pure_bind]
  rw [sub_under_fail]
  rfl

/-- A power-of-two `align` is non-zero (otherwise the unconditional
    `x - 1` underflows and `is_power_of_two_usize` fails). -/
private theorem pow2_ne_zero (x : usize)
    (h : is_power_of_two_usize x = RustM.ok true) : x ≠ 0 := by
  rintro rfl
  rw [is_pow2_zero] at h
  exact absurd h (by decide)

/-- A power-of-two `usize` is at most `2^63` (its single set bit is at
    position ≤ 63). This is the structural fact that keeps the inlined
    `max_size_for_align` subtraction from underflowing. -/
private theorem pow2_le (x : usize)
    (h : is_power_of_two_usize x = RustM.ok true) :
    x.toNat ≤ 9223372036854775808 := by
  have hx : x ≠ 0 := pow2_ne_zero x h
  rw [ipow2_unfold x hx] at h
  simp only [RustM.ok] at h
  injection h with h1
  injection h1 with h2
  -- h2 : ((x != 0) && ((x &&& (x - 1)) == 0)) = true
  have hb : x &&& (x - 1) = 0 := by
    rcases hb2 : ((x &&& (x - 1)) == 0) with _ | _
    · rw [hb2, Bool.and_false] at h2
      exact absurd h2 (by decide)
    · simpa using hb2
  have hbit' : x.toBitVec &&& (x.toBitVec - 1#64) = 0#64 := by
    have := congrArg USize64.toBitVec hb
    simpa using this
  have hxb : x.toBitVec ≠ 0#64 := by
    simpa [← USize64.toBitVec_inj] using hx
  clear h2 hb hx
  have hble : x.toBitVec ≤ (9223372036854775808#64 : BitVec 64) := by
    bv_decide
  have hle : x.toBitVec.toNat ≤ (9223372036854775808#64 : BitVec 64).toNat :=
    BitVec.le_def.mp hble
  have hc : (9223372036854775808#64 : BitVec 64).toNat = 9223372036854775808 := by
    have hlt : (9223372036854775808 : Nat) < 2 ^ 64 := by decide
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  show x.toBitVec.toNat ≤ 9223372036854775808
  rw [← hc]; exact hle

/-- The bound `(2^63 - align)` as a `Nat`, given no underflow. -/
private theorem msfa_toNat (align : usize)
    (hal : align.toNat ≤ 9223372036854775808) :
    ((9223372036854775808 : usize) - align).toNat
      = 9223372036854775808 - align.toNat := by
  rw [USize64.toNat_sub_of_le' (by rw [c63_toNat]; exact hal), c63_toNat]

/-- Reduce `from_size_alignment` once the truth value `b` of the size
    guard is known.  `rw [hb]` substitutes the guard *before* anything
    forces the kernel to reduce the `2^63` literal, so this is
    kernel-light (no `decide` of a `2^63`-sized BitVec is ever
    evaluated). -/
private theorem fsa_core (size align : usize)
    (hal : align.toNat ≤ 9223372036854775808) (b : Bool)
    (hb : decide (size > ((9223372036854775808 : usize) - align)) = b) :
    from_size_alignment size align
      = (if b then RustM.ok (core_models.result.Result.Err LayoutError.mk)
              else RustM.ok (core_models.result.Result.Ok (Layout.mk size align))) := by
  unfold from_size_alignment
  rw [msfa_ok align hal, ok_bind]
  show (size >? ((9223372036854775808 : usize) - align)) >>=
        (fun c => if c then pure (core_models.result.Result.Err LayoutError.mk)
                  else pure (core_models.result.Result.Ok (Layout.mk size align)))
      = (if b then RustM.ok (core_models.result.Result.Err LayoutError.mk)
              else RustM.ok (core_models.result.Result.Ok (Layout.mk size align)))
  rw [hgt, hb, ok_bind]
  show (if b then pure (core_models.result.Result.Err LayoutError.mk)
             else pure (core_models.result.Result.Ok (Layout.mk size align)))
      = (if b then RustM.ok (core_models.result.Result.Err LayoutError.mk)
              else RustM.ok (core_models.result.Result.Ok (Layout.mk size align)))
  cases b <;> rfl

/-- `from_size_alignment` succeeds when `align ≤ 2^63` and the size fits
    the bound. -/
private theorem fsa_ok (size align : usize)
    (hal : align.toNat ≤ 9223372036854775808)
    (hsz : size.toNat ≤ 9223372036854775808 - align.toNat) :
    from_size_alignment size align
      = RustM.ok (core_models.result.Result.Ok (Layout.mk size align)) := by
  have hcond : decide (size > ((9223372036854775808 : usize) - align)) = false := by
    rw [decide_eq_false_iff_not, gt_iff_lt, USize64.lt_iff_toNat_lt,
        msfa_toNat align hal]
    omega
  simpa using fsa_core size align hal false hcond

/-- `from_size_alignment` errors when `align ≤ 2^63` but the size exceeds
    the bound. -/
private theorem fsa_err (size align : usize)
    (hal : align.toNat ≤ 9223372036854775808)
    (hsz : 9223372036854775808 - align.toNat < size.toNat) :
    from_size_alignment size align
      = RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  have hcond : decide (size > ((9223372036854775808 : usize) - align)) = true := by
    rw [decide_eq_true_eq, gt_iff_lt, USize64.lt_iff_toNat_lt,
        msfa_toNat align hal]
    omega
  simpa using fsa_core size align hal true hcond

/-- Reduce `align_to` to `from_size_alignment` on the raised alignment,
    once we know `align` is a power of two (so the outer guard passes).
    The inlined `usize::max` becomes the `if a.align > align` choice. -/
private theorem align_to_pos (layout : Layout) (align : usize)
    (hpa : is_power_of_two_usize align = RustM.ok true) :
    align_to layout align
      = from_size_alignment (Layout.size layout)
          (if Layout.align layout > align then Layout.align layout else align) := by
  unfold align_to
  simp only [hpa, ok_bind, hgt, ↓reduceIte]
  by_cases hP : Layout.align layout > align
  · simp [hP]
  · simp [hP]

/-! ### Public obligations -/

/-- Precondition / failure (non-power-of-two `align`): when the
    power-of-two check `is_power_of_two_usize align` evaluates to `false`
    (this includes `align = 0`, since the `x != 0` short-circuit makes the
    helper total), `align_to` returns `Err(LayoutError)` regardless of the
    layout.

    Captures the property test `prop_non_power_of_two_align_is_error`
    (and the first `align_to` assertion of the `layout_errors` unit test):
    `align_to(layout, align).is_err()` for every non-power-of-two `align`.
    A buggy implementation that fell through to `from_size_alignment` on a
    non-power-of-two alignment would falsify this. -/
theorem align_to_non_pow2_err (layout : Layout) (align : usize)
    (h : is_power_of_two_usize align = RustM.ok false) :
    align_to layout align
      = RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  unfold align_to
  rw [h]
  rfl

/-- Postcondition (valid inputs): when both `align` and the layout's own
    alignment are powers of two, and the size fits within the contract
    bound `spec_max_size_for_align(new_align)` (= `2^63 - new_align`,
    where `new_align = max(layout.align, align)`), `align_to` returns
    `Ok` with the size unchanged and the alignment raised to exactly
    `new_align`.

    Captures the property test
    `prop_valid_inputs_preserve_size_and_raise_alignment`. The
    `is_power_of_two_usize layout.align` hypothesis mirrors the test's
    `gen_pow2` layout-alignment invariant; without it `new_align` could
    exceed `2^63` and the inlined `max_size_for_align` subtraction would
    underflow. A buggy implementation that mutated the size, used `min`
    instead of `max`, or kept the original alignment would falsify
    this. -/
theorem align_to_ok_preserves_size_raises_align
    (layout : Layout) (align : usize)
    (hpa : is_power_of_two_usize align = RustM.ok true)
    (hpl : is_power_of_two_usize (Layout.align layout) = RustM.ok true)
    (new_align : usize)
    (hna : new_align =
      (if Layout.align layout > align then Layout.align layout else align))
    (hsize : (Layout.size layout).toNat ≤ 9223372036854775808 - new_align.toNat) :
    align_to layout align
      = RustM.ok (core_models.result.Result.Ok
          (Layout.mk (size := Layout.size layout) (align := new_align))) := by
  rw [align_to_pos layout align hpa, ← hna]
  exact fsa_ok (Layout.size layout) new_align
    (by rw [hna]; split
        · exact pow2_le _ hpl
        · exact pow2_le _ hpa)
    hsize

/-- Failure (size overflow): when both alignments are powers of two but
    the size strictly exceeds the contract bound
    `spec_max_size_for_align(new_align)` (= `2^63 - new_align`), the
    resulting layout would overflow `isize`, so `align_to` returns
    `Err(LayoutError)`.

    Captures the property test `prop_size_overflow_is_error` (and the
    second `align_to` assertion of `layout_errors`, where
    `align = isize::MAX as usize + 1 = 2^63` forces `max_size_for_align`
    to `0`). A buggy implementation that omitted the size guard would
    falsify this. -/
theorem align_to_size_overflow_err
    (layout : Layout) (align : usize)
    (hpa : is_power_of_two_usize align = RustM.ok true)
    (hpl : is_power_of_two_usize (Layout.align layout) = RustM.ok true)
    (new_align : usize)
    (hna : new_align =
      (if Layout.align layout > align then Layout.align layout else align))
    (hsize : 9223372036854775808 - new_align.toNat < (Layout.size layout).toNat) :
    align_to layout align
      = RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  rw [align_to_pos layout align hpa, ← hna]
  exact fsa_err (Layout.size layout) new_align
    (by rw [hna]; split
        · exact pow2_le _ hpl
        · exact pow2_le _ hpa)
    hsize

/-- Concrete unit test (`layout_errors`, first assertion):
    `align_to({size:2, align:1}, 3)` errors because `3` is not a power of
    two (`3 & 2 = 2 ≠ 0`). -/
theorem align_to_not_pow2_concrete :
    align_to (Layout.mk (size := (2 : usize)) (align := (1 : usize)))
        (3 : usize)
      = RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  apply align_to_non_pow2_err
  decide

/-- Concrete unit test (`layout_errors`, second assertion): with
    `align = isize::MAX as usize + 1 = 2^63` (a power of two),
    `new_align = max(1, 2^63) = 2^63`, so `max_size_for_align` is `0` and
    the size `2` overflows — `align_to` errors. -/
theorem align_to_isize_overflow_concrete :
    align_to (Layout.mk (size := (2 : usize)) (align := (1 : usize)))
        (9223372036854775808 : usize)
      = RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  exact align_to_size_overflow_err
    (Layout.mk (size := (2 : usize)) (align := (1 : usize)))
    (9223372036854775808 : usize)
    (by decide)
    (by decide)
    (9223372036854775808 : usize)
    (by simp)
    (by simp)

/-- Concrete unit test (`raises_alignment`, first assertion):
    `align_to({size:2, align:1}, 4)` raises the alignment to `4` and
    preserves the size. -/
theorem align_to_raises_alignment_concrete :
    align_to (Layout.mk (size := (2 : usize)) (align := (1 : usize)))
        (4 : usize)
      = RustM.ok (core_models.result.Result.Ok
          (Layout.mk (size := (2 : usize)) (align := (4 : usize)))) := by
  exact align_to_ok_preserves_size_raises_align
    (Layout.mk (size := (2 : usize)) (align := (1 : usize)))
    (4 : usize)
    (by decide)
    (by decide)
    (4 : usize)
    (by simp)
    (by simp)

/-- Concrete unit test (`raises_alignment`, second assertion): already
    sufficiently aligned — `align_to({size:16, align:8}, 4)` keeps the
    larger alignment `8` (the `layout.align > align` branch) and the
    size unchanged. -/
theorem align_to_already_aligned_concrete :
    align_to (Layout.mk (size := (16 : usize)) (align := (8 : usize)))
        (4 : usize)
      = RustM.ok (core_models.result.Result.Ok
          (Layout.mk (size := (16 : usize)) (align := (8 : usize)))) := by
  exact align_to_ok_preserves_size_raises_align
    (Layout.mk (size := (16 : usize)) (align := (8 : usize)))
    (4 : usize)
    (by decide)
    (by decide)
    (8 : usize)
    (by simp)
    (by simp)

end Align_to_usizeObligations
