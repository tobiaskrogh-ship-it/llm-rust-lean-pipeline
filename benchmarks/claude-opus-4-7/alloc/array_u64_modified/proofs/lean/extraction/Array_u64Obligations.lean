-- Companion obligations file for the `array_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import array_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Array_u64Obligations

/-! ### Helper lemmas (internal scaffolding)

These `private theorem`s reduce the monadic `RustM` plumbing of the
extracted `array_u64` / `max_size_for_align`.  `array_u64` is
`core::alloc::Layout::array` monomorphized to `u64` (element size =
align = 8).  `max_size_for_align 8` evaluates to
`(2^63 - 1 + 1) - 8 = 2^63 - 8 = 9223372036854775800`, and the guard
rejects `n` exactly when `n > (2^63 - 8) / 8 = 1152921504606846975`. -/

/-- `RustM.ok` is `pure`, so binding it just applies the continuation. -/
private theorem ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    (RustM.ok a) >>= f = f a := rfl

/-- `pure` in `RustM` is `RustM.ok`. -/
private theorem pure_eq_ok {α : Type} (a : α) :
    (pure a : RustM α) = RustM.ok a := rfl

/-! Constant `toNat` reductions (the inlined `isize::MAX (+1)` literal,
the element size `8`, the static `1`, and the division threshold). -/

private theorem c63m1_toNat :
    (9223372036854775807 : usize).toNat = 9223372036854775807 := by simp

private theorem c63_toNat :
    (9223372036854775808 : usize).toNat = 9223372036854775808 := by simp

private theorem c8_toNat : (8 : usize).toNat = 8 := by simp

private theorem c1_toNat : (1 : usize).toNat = 1 := by simp

private theorem cq_toNat :
    (1152921504606846975 : usize).toNat = 1152921504606846975 := by simp

/-- Rust addition does not panic when there is no overflow. -/
private theorem hadd_ok (a b : usize) (h : a.toNat + b.toNat < 2 ^ 64) :
    (a +? b) = RustM.ok (a + b) := by
  have hno : ¬ BitVec.uaddOverflow a.toBitVec b.toBitVec := by
    rw [USize64.uaddOverflow_iff]; omega
  show (if BitVec.uaddOverflow a.toBitVec b.toBitVec
        then (RustM.fail Error.integerOverflow : RustM usize)
        else pure (a + b)) = RustM.ok (a + b)
  rw [if_neg hno]
  rfl

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

/-- Rust multiplication does not panic when there is no overflow. -/
private theorem hmul_ok (a b : usize) (h : a.toNat * b.toNat < 2 ^ 64) :
    (a *? b) = RustM.ok (a * b) := by
  have hno : ¬ BitVec.umulOverflow a.toBitVec b.toBitVec := by
    rw [USize64.umulOverflow_iff]; omega
  show (if BitVec.umulOverflow a.toBitVec b.toBitVec
        then (RustM.fail Error.integerOverflow : RustM usize)
        else pure (a * b)) = RustM.ok (a * b)
  rw [if_neg hno]
  rfl

/-- Rust division does not panic for a non-zero divisor. -/
private theorem hdiv_ok (a b : usize) (h : b ≠ 0) :
    (a /? b) = RustM.ok (a / b) := by
  show (if b = 0 then (RustM.fail Error.divisionByZero : RustM usize)
        else pure (a / b)) = RustM.ok (a / b)
  rw [if_neg h]
  rfl

/-- The Rust `>` extracts to `pure (decide (a > b))`. -/
private theorem hgt (a b : usize) :
    (a >? b) = RustM.ok (decide (a > b)) := rfl

/-- The Rust `!=` of the static element size `8` against `0` is `true`. -/
private theorem hne8 :
    ((8 : usize) !=? (0 : usize)) = RustM.ok true := by decide

/-- The Rust short-circuit `&&` (both operands already forced) is `pure (a && b)`. -/
private theorem hand (a b : Bool) :
    (a &&? b) = RustM.ok (a && b) := rfl

/-- `max_size_for_align 8 = (2^63 - 1 + 1) - 8 = 9223372036854775800`.
    The `+1` cannot overflow (`2^63 - 1 + 1 = 2^63 < 2^64`) and the
    subtraction cannot underflow (`8 ≤ 2^63`). -/
private theorem msfa8 :
    array_u64.max_size_for_align (8 : usize)
      = RustM.ok (9223372036854775800 : usize) := by
  unfold array_u64.max_size_for_align
  rw [hadd_ok (9223372036854775807 : usize) (1 : usize)
        (by rw [c63m1_toNat, c1_toNat]; decide),
      ok_bind,
      hsub_ok ((9223372036854775807 : usize) + (1 : usize)) (8 : usize)
        (by decide)]
  congr 1

/-- `max_size_for_align 8 / 8 = 9223372036854775800 / 8
    = 1152921504606846975` (the static divisor `8` is non-zero). -/
private theorem hdivval :
    (9223372036854775800 : usize) /? (8 : usize)
      = RustM.ok (1152921504606846975 : usize) := by
  rw [hdiv_ok (9223372036854775800 : usize) (8 : usize) (by decide)]
  congr 1

/-- One-step reduction of the whole function once the truth value `b` of
    the size guard `n > 1152921504606846975` is known.  Substituting the
    guard *before* the kernel is forced to reduce anything is
    kernel-light. -/
private theorem array_u64_core (n : usize) (b : Bool)
    (hb : decide (n > (1152921504606846975 : usize)) = b) :
    array_u64.array_u64 n
      = (if b then RustM.ok (core_models.result.Result.Err array_u64.LayoutError.mk)
              else ((8 : usize) *? n) >>= fun array_size =>
                     RustM.ok (core_models.result.Result.Ok
                       (array_u64.Layout.mk (size := array_size)
                         (align := (8 : usize))))) := by
  unfold array_u64.array_u64
  simp only [hne8, msfa8, hdivval, hgt, hand, ok_bind, Bool.true_and]
  rw [hb]
  cases b <;> rfl

/-- Failure form: when the guard fires, the function returns
    `Ok (Err LayoutError)` (note `RustM.ok`, i.e. no panic). -/
private theorem array_u64_err (n : usize)
    (h : n > (1152921504606846975 : usize)) :
    array_u64.array_u64 n
      = RustM.ok (core_models.result.Result.Err array_u64.LayoutError.mk) := by
  simpa using array_u64_core n true (decide_eq_true h)

/-- Success form: when the guard does not fire, the function returns
    `Ok (Layout { size := 8 * n, align := 8 })`.  The guard's negation
    bounds `n.toNat ≤ 1152921504606846975`, which makes the unchecked
    `8 * n` multiplication non-overflowing (`8 * n ≤ 2^63 - 8 < 2^64`). -/
private theorem array_u64_ok (n : usize)
    (h : ¬ n > (1152921504606846975 : usize)) :
    array_u64.array_u64 n
      = RustM.ok (core_models.result.Result.Ok
          (array_u64.Layout.mk (size := (8 : usize) * n)
            (align := (8 : usize)))) := by
  have hle : n.toNat ≤ 1152921504606846975 := by
    simp only [gt_iff_lt, USize64.lt_iff_toNat_lt, cq_toNat] at h
    omega
  have hfits : (8 : usize).toNat * n.toNat < 2 ^ 64 := by
    rw [c8_toNat]
    have h1 : 8 * n.toNat ≤ 9223372036854775800 := by omega
    have h2 : (9223372036854775800 : Nat) < 2 ^ 64 := by decide
    exact Nat.lt_of_le_of_lt h1 h2
  have hc := array_u64_core n false (decide_eq_false h)
  rw [hmul_ok (8 : usize) n hfits, ok_bind] at hc
  simpa using hc

/-! ### Public obligations

`array_u64` is `core::alloc::Layout::array` monomorphized to `u64`
(element size = align = 8).  The inlined `max_size_for_align(8)` evaluates
to `(2^63 - 1 + 1) - 8 = 2^63 - 8`, and the guard rejects `n` exactly when
`n > (2^63 - 8) / 8 = 1152921504606846975`.  Equivalently, the call
succeeds iff the total byte size `8 * n` fits in `isize::MAX`
(`= 2^63 - 1 = 9223372036854775807`) — this is the `byte_size_fits`
characterisation the property tests assert. -/

/-- Postcondition (success / functional correctness): when the total byte
    size `8 * n` fits within `isize::MAX` (`= 9223372036854775807`),
    `array_u64 n` returns `Ok (Layout { size := 8 * n, align := 8 })`.

    Captures `prop_success_yields_size_8n_and_align_8` (both the
    `size == 8*n` output/input relation and the constant `align == 8`),
    the `is_ok` halves of `prop_ok_iff_byte_size_fits_isize_max` and
    `layout_array_edge_cases`, and the `basic_cases` unit test. A buggy
    implementation that mutated the size, used the wrong element size, or
    returned a different alignment would falsify this. -/
theorem array_u64_ok_size_8n_align_8 (n : usize)
    (hfit : n.toNat * 8 ≤ 9223372036854775807) :
    array_u64.array_u64 n
      = RustM.ok (core_models.result.Result.Ok
          (array_u64.Layout.mk (size := (8 : usize) * n) (align := (8 : usize)))) := by
  apply array_u64_ok
  simp only [gt_iff_lt, USize64.lt_iff_toNat_lt, cq_toNat]
  omega

/-- Failure condition (overflow): when the total byte size `8 * n` would
    exceed `isize::MAX` (`= 9223372036854775807`), `array_u64 n` returns
    `Err(LayoutError)` — and returns it as `RustM.ok (Err …)`, i.e. it does
    NOT panic / overflow.

    Captures `prop_overflow_inputs_yield_error` and the `is_err` halves of
    `prop_ok_iff_byte_size_fits_isize_max` and `layout_array_edge_cases`. A
    buggy implementation that omitted the size guard (and thus overflowed
    the unchecked `8 * n` multiplication) would falsify this. -/
theorem array_u64_overflow_err (n : usize)
    (hbig : 9223372036854775807 < n.toNat * 8) :
    array_u64.array_u64 n
      = RustM.ok (core_models.result.Result.Err array_u64.LayoutError.mk) := by
  apply array_u64_err
  rw [gt_iff_lt, USize64.lt_iff_toNat_lt, cq_toNat]
  omega

/-- Totality / no-panic: for every `usize` input, `array_u64 n` returns a
    value successfully (never `RustM.fail`). The division-derived guard
    `n > max_size_for_align(8) / 8` ensures the `8 * n` multiplication in
    the success branch cannot overflow, even for `n = usize::MAX`.

    Captures the "the call never panics … even for `usize::MAX`" clause of
    `prop_overflow_inputs_yield_error`. A buggy implementation that
    multiplied before checking the bound would falsify this on large
    inputs. -/
theorem array_u64_total (n : usize) :
    ∃ r : core_models.result.Result array_u64.Layout array_u64.LayoutError,
      array_u64.array_u64 n = RustM.ok r := by
  by_cases hc : n > (1152921504606846975 : usize)
  · exact ⟨_, array_u64_err n hc⟩
  · exact ⟨_, array_u64_ok n hc⟩

/-- Concrete unit test (`basic_cases`, first assertion):
    `array_u64(0)` yields `Layout { size := 0, align := 8 }`. -/
theorem array_u64_zero_concrete :
    array_u64.array_u64 (0 : usize)
      = RustM.ok (core_models.result.Result.Ok
          (array_u64.Layout.mk (size := (0 : usize)) (align := (8 : usize)))) := by
  have h0 : (8 : usize) * (0 : usize) = (0 : usize) := by decide
  rw [array_u64_ok (0 : usize) (by decide), h0]

/-- Concrete unit test (`basic_cases`, second assertion):
    `array_u64(3)` yields `Layout { size := 24, align := 8 }`. -/
theorem array_u64_three_concrete :
    array_u64.array_u64 (3 : usize)
      = RustM.ok (core_models.result.Result.Ok
          (array_u64.Layout.mk (size := (24 : usize)) (align := (8 : usize)))) := by
  have h0 : (8 : usize) * (3 : usize) = (24 : usize) := by decide
  rw [array_u64_ok (3 : usize) (by decide), h0]

end Array_u64Obligations
