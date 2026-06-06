-- Companion obligations file for the `extend_packed_usize` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import extend_packed_usize

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Extend_packed_usizeObligations

open extend_packed_usize

/-! ### Contract

`extend_packed` is `core::alloc::Layout::extend_packed`.  It computes
`new_size = layout.size + next.size` (the `next` alignment is dropped),
then defers to the inlined `from_size_alignment new_size layout.align`.
The inlined `max_size_for_align align` is `(2^63 - 1 + 1) - align
= 2^63 - align` (the `+1` cannot overflow; the `- align` cannot
underflow as long as `align ≤ 2^63 = 9223372036854775808`).

Precondition (from the source comment and the property-test generators):
each input `size` is at most `isize::MAX = 2^63 - 1
= 9223372036854775807`, so the leading `layout.size + next.size`
addition cannot overflow `usize`.  The alignment is at most
`2^63 = 9223372036854775808` (the largest power-of-two alignment the
suite uses), so `max_size_for_align` does not underflow.

`isize::MAX  = 9223372036854775807`  (= 2^63 - 1)
`2^63        = 9223372036854775808`  (= isize::MAX + 1) -/

/-! ### Helper lemmas (internal scaffolding)

These `private theorem`s reduce the monadic `RustM` plumbing of the
extracted `extend_packed` / `from_size_alignment` / `max_size_for_align`.
The structure mirrors the `align_to_usize` reference (same inlined
`from_size_alignment`), with the leading `layout.size +? next.size`
addition discharged from the size precondition, and the
`(2^63 - 1) +? 1` literal fold borrowed from the `array_u64`
`max_size_for_align`. -/

/-- `RustM.ok` is `pure`, so binding it just applies the continuation. -/
private theorem ok_bind {α β : Type} (a : α) (f : α → RustM β) :
    (RustM.ok a) >>= f = f a := rfl

/-- The Rust `>` extracts to `pure (decide (a > b))`. -/
private theorem hgt (a b : usize) :
    (a >? b) = RustM.ok (decide (a > b)) := rfl

/-- `isize::MAX = 2^63 - 1` as a `usize` literal has `toNat = 2^63 - 1`. -/
private theorem c63m1_toNat :
    (9223372036854775807 : usize).toNat = 9223372036854775807 := by simp

/-- `2^63` as a `usize` literal has `toNat = 2^63` (it fits in 64 bits). -/
private theorem c63_toNat :
    (9223372036854775808 : usize).toNat = 9223372036854775808 := by simp

/-- The static `1` literal has `toNat = 1`. -/
private theorem c1_toNat : (1 : usize).toNat = 1 := by simp

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

/-- `isize::MAX + 1 = 2^63` as a `usize`.  The `+1` cannot overflow
    (`2^63 - 1 + 1 = 2^63 < 2^64`), proved through `toNat`. -/
private theorem add_lit :
    (9223372036854775807 : usize) + (1 : usize) = (9223372036854775808 : usize) := by
  apply USize64.toNat_inj.mp
  rw [USize64.toNat_add_of_lt (by rw [c63m1_toNat, c1_toNat]; decide),
      c63m1_toNat, c1_toNat, c63_toNat]

/-- `max_size_for_align align = (2^63 - 1 + 1) - align = 2^63 - align`,
    total whenever `align ≤ 2^63` (no underflow).  The `+1` cannot
    overflow.  `rw [add_lit]` folds the literal *before* the kernel is
    forced to evaluate any `2^63`-sized `BitVec`, keeping the proof
    kernel-light. -/
private theorem msfa_ok (align : usize)
    (hal : align.toNat ≤ 9223372036854775808) :
    max_size_for_align align
      = RustM.ok ((9223372036854775808 : usize) - align) := by
  unfold max_size_for_align
  rw [hadd_ok (9223372036854775807 : usize) (1 : usize)
        (by rw [c63m1_toNat, c1_toNat]; decide),
      ok_bind, add_lit,
      hsub_ok (9223372036854775808 : usize) align (by rw [c63_toNat]; exact hal)]

/-- The bound `(2^63 - align)` as a `Nat`, given no underflow. -/
private theorem msfa_toNat (align : usize)
    (hal : align.toNat ≤ 9223372036854775808) :
    ((9223372036854775808 : usize) - align).toNat
      = 9223372036854775808 - align.toNat := by
  rw [USize64.toNat_sub_of_le' (by rw [c63_toNat]; exact hal), c63_toNat]

/-- Reduce `from_size_alignment` once the truth value `b` of the size
    guard is known.  `rw [hb]` substitutes the guard *before* anything
    forces the kernel to reduce the `2^63` literal, so this is
    kernel-light. -/
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

/-- The leading `layout.size +? next.size` cannot overflow when each
    operand is at most `isize::MAX = 2^63 - 1` (so the sum is at most
    `2^64 - 2 < 2^64`). -/
private theorem ep_add_ok (a b : usize)
    (ha : a.toNat ≤ 9223372036854775807)
    (hb : b.toNat ≤ 9223372036854775807) :
    (a +? b) = RustM.ok (a + b) := by
  apply hadd_ok
  have h2 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
  omega

/-- Reduce `extend_packed` to `from_size_alignment` on the (non-overflowing)
    sum of the two sizes; the `next` alignment is never consulted. -/
private theorem ep_reduce (layout next : Layout)
    (hl : (Layout.size layout).toNat ≤ 9223372036854775807)
    (hn : (Layout.size next).toNat ≤ 9223372036854775807) :
    extend_packed layout next
      = from_size_alignment (Layout.size layout + Layout.size next)
          (Layout.align layout) := by
  unfold extend_packed
  rw [ep_add_ok (Layout.size layout) (Layout.size next) hl hn, ok_bind]

/-! ### Public obligations -/

/-- Postcondition (success / functional correctness): under the size
    precondition (`layout.size, next.size ≤ isize::MAX`) and a
    non-underflowing alignment (`layout.align ≤ 2^63`), whenever the
    total `layout.size + next.size` fits within
    `max_size_for_align(layout.align) = 2^63 - layout.align`,
    `extend_packed` returns
    `Ok (Layout { size := layout.size + next.size, align := layout.align })`.

    Captures `ok_size_is_exact_sum` (the result size is *exactly* the
    sum — no padding is inserted), the `Ok` half of
    `ok_iff_sum_within_max_size_for_align`, and the layout-alignment
    half of `next_align_is_ignored_and_layout_align_preserved` (the
    result alignment is `layout.align`).  A buggy implementation that
    padded/aligned the size, swapped in `next.align`, or used the wrong
    alignment would falsify this. -/
theorem extend_packed_ok_size_is_exact_sum
    (layout next : Layout)
    (hl : (Layout.size layout).toNat ≤ 9223372036854775807)
    (hn : (Layout.size next).toNat ≤ 9223372036854775807)
    (ha : (Layout.align layout).toNat ≤ 9223372036854775808)
    (hfit : (Layout.size layout).toNat + (Layout.size next).toNat
              ≤ 9223372036854775808 - (Layout.align layout).toNat) :
    extend_packed layout next
      = RustM.ok (core_models.result.Result.Ok
          (Layout.mk (size := Layout.size layout + Layout.size next)
                     (align := Layout.align layout))) := by
  rw [ep_reduce layout next hl hn]
  have hsum : (Layout.size layout + Layout.size next).toNat
                = (Layout.size layout).toNat + (Layout.size next).toNat := by
    apply USize64.toNat_add_of_lt
    have h2 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
    omega
  have hsz : (Layout.size layout + Layout.size next).toNat
                ≤ 9223372036854775808 - (Layout.align layout).toNat := by
    rw [hsum]; exact hfit
  exact fsa_ok (Layout.size layout + Layout.size next) (Layout.align layout) ha hsz

/-- Failure condition (size too big for the alignment): under the same
    size / alignment precondition, when the total
    `layout.size + next.size` strictly exceeds
    `max_size_for_align(layout.align) = 2^63 - layout.align`,
    `extend_packed` returns `Err(LayoutError)` — delivered as
    `RustM.ok (Err …)`, i.e. it does NOT panic / overflow.

    Captures the `Err` half of `ok_iff_sum_within_max_size_for_align`
    and the `overflowing_size_errors` failure mode.  A buggy
    implementation that dropped the `from_size_alignment` guard would
    falsify this. -/
theorem extend_packed_overflow_err
    (layout next : Layout)
    (hl : (Layout.size layout).toNat ≤ 9223372036854775807)
    (hn : (Layout.size next).toNat ≤ 9223372036854775807)
    (ha : (Layout.align layout).toNat ≤ 9223372036854775808)
    (hbig : 9223372036854775808 - (Layout.align layout).toNat
              < (Layout.size layout).toNat + (Layout.size next).toNat) :
    extend_packed layout next
      = RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  rw [ep_reduce layout next hl hn]
  have hsum : (Layout.size layout + Layout.size next).toNat
                = (Layout.size layout).toNat + (Layout.size next).toNat := by
    apply USize64.toNat_add_of_lt
    have h2 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
    omega
  have hsz : 9223372036854775808 - (Layout.align layout).toNat
                < (Layout.size layout + Layout.size next).toNat := by
    rw [hsum]; exact hbig
  exact fsa_err (Layout.size layout + Layout.size next) (Layout.align layout) ha hsz

/-- Postcondition (input independence): the alignment of `next` is
    ignored — for a fixed `layout` and a fixed `next.size`, the result
    (value *and* `Ok`/`Err`) does not depend on `next.align`.

    Captures the independence half of
    `next_align_is_ignored_and_layout_align_preserved` (`prev == r` as
    only `next.align` varies).  A buggy implementation that consulted
    `next.align` (e.g. padded to it) would falsify this. -/
theorem extend_packed_next_align_ignored
    (layout : Layout) (sz a1 a2 : usize) :
    extend_packed layout (Layout.mk (size := sz) (align := a1))
      = extend_packed layout (Layout.mk (size := sz) (align := a2)) := by
  unfold extend_packed
  rfl

/-- Totality / no-panic: under the size precondition
    (`layout.size, next.size ≤ isize::MAX`) and a non-underflowing
    alignment (`layout.align ≤ 2^63`), `extend_packed` always returns a
    value successfully (never `RustM.fail`).  The leading addition
    cannot overflow (each operand `≤ 2^63 - 1`, so the sum `≤ 2^64 - 2`)
    and the inlined `max_size_for_align` subtraction cannot underflow.

    Captures the "never panics — returns `Err` on overflow instead of
    trapping" failure-model clause underlying `overflowing_size_errors`.
    A buggy implementation that added before guarding, or that let the
    alignment subtraction underflow, would falsify this. -/
theorem extend_packed_total
    (layout next : Layout)
    (hl : (Layout.size layout).toNat ≤ 9223372036854775807)
    (hn : (Layout.size next).toNat ≤ 9223372036854775807)
    (ha : (Layout.align layout).toNat ≤ 9223372036854775808) :
    ∃ r : core_models.result.Result Layout LayoutError,
      extend_packed layout next = RustM.ok r := by
  by_cases hc : (Layout.size layout).toNat + (Layout.size next).toNat
                  ≤ 9223372036854775808 - (Layout.align layout).toNat
  · exact ⟨_, extend_packed_ok_size_is_exact_sum layout next hl hn ha hc⟩
  · have hbig : 9223372036854775808 - (Layout.align layout).toNat
                  < (Layout.size layout).toNat + (Layout.size next).toNat := by
      omega
    exact ⟨_, extend_packed_overflow_err layout next hl hn ha hbig⟩

/-- Concrete unit test (`adds_sizes_without_padding`):
    `extend_packed({size:2, align:4}, {size:3, align:2})`
    yields `Ok (Layout { size := 5, align := 4 })` — sizes add with no
    padding and `next.align = 2` is ignored. -/
theorem extend_packed_adds_sizes_concrete :
    extend_packed (Layout.mk (size := (2 : usize)) (align := (4 : usize)))
        (Layout.mk (size := (3 : usize)) (align := (2 : usize)))
      = RustM.ok (core_models.result.Result.Ok
          (Layout.mk (size := (5 : usize)) (align := (4 : usize)))) := by
  have h := extend_packed_ok_size_is_exact_sum
    (Layout.mk (size := (2 : usize)) (align := (4 : usize)))
    (Layout.mk (size := (3 : usize)) (align := (2 : usize)))
    (by decide) (by decide) (by decide) (by decide)
  rw [h]
  have e : Layout.size (Layout.mk (size := (2 : usize)) (align := (4 : usize)))
            + Layout.size (Layout.mk (size := (3 : usize)) (align := (2 : usize)))
            = (5 : usize) := by decide
  rw [e]

/-- Concrete unit test (`overflowing_size_errors`): with
    `layout.size = isize::MAX = 9223372036854775807` and `next.size = 2`,
    the total `9223372036854775809` exceeds
    `max_size_for_align(1) = 2^63 - 1 = 9223372036854775807`, so
    `extend_packed` errors (without panicking on the leading add). -/
theorem extend_packed_overflow_concrete :
    extend_packed
        (Layout.mk (size := (9223372036854775807 : usize)) (align := (1 : usize)))
        (Layout.mk (size := (2 : usize)) (align := (1 : usize)))
      = RustM.ok (core_models.result.Result.Err LayoutError.mk) := by
  exact extend_packed_overflow_err
    (Layout.mk (size := (9223372036854775807 : usize)) (align := (1 : usize)))
    (Layout.mk (size := (2 : usize)) (align := (1 : usize)))
    (by decide) (by decide) (by decide) (by decide)

end Extend_packed_usizeObligations
