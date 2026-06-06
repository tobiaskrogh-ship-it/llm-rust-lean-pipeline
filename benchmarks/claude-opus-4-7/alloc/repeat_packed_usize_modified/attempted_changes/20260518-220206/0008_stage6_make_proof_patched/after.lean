-- Companion obligations file for the `repeat_packed_usize` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import repeat_packed_usize

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Repeat_packed_usizeObligations

-- `MAX_ALIGN = isize::MAX + 1 = 2^63`; `usize::MAX = 2^64 - 1`. These are the
-- inlined literals appearing in the extracted `max_size_for_align` /
-- `repeat_packed`.

/-! ## Definitional unfolding of the Hax partial operators (all `rfl`) -/

/-- `x +? y` is, by `rfl`, the overflow-guarded `if` (cf. the reference
    `max_size_for_align`'s `hax_add_def_usize`). -/
private theorem hax_add_def_usize (x y : usize) :
    x +? y = if USize64.addOverflow x y
             then RustM.fail Error.integerOverflow
             else pure (x + y) := rfl

/-- Definitional unfolding of the partial `usize` subtraction. -/
private theorem hax_sub_def_usize (x y : usize) :
    x -? y = if USize64.subOverflow x y
             then RustM.fail Error.integerOverflow
             else pure (x - y) := rfl

/-- Definitional unfolding of the partial `usize` multiplication. -/
private theorem hax_mul_def_usize (x y : usize) :
    x *? y = if USize64.mulOverflow x y
             then RustM.fail Error.integerOverflow
             else pure (x * y) := rfl

/-- Definitional unfolding of the partial unsigned `usize` division: it only
    fails on division by zero (no overflow case for unsigned). -/
private theorem hax_div_def_usize (x y : usize) :
    x /? y = if y = (0 : usize)
             then RustM.fail Error.divisionByZero
             else pure (x / y) := rfl

/-- `x !=? y` is, by `rfl`, `pure (x != y)`. -/
private theorem hax_ne_def (x y : usize) : (x !=? y) = pure (x != y) := rfl

/-- `x >? y` is, by `rfl`, `pure (decide (x > y))`. -/
private theorem hax_gt_def (x y : usize) : (x >? y) = pure (decide (x > y)) := rfl

/-- `a &&? b` is, by `rfl`, `pure (a && b)`. -/
private theorem hax_and_def (a b : Bool) : (a &&? b) = pure (a && b) := rfl

/-! ## Closed-literal constant folds (all `decide`) -/

/-- The static inner sum `isize::MAX + 1` evaluates to `2^63`. -/
private theorem const_add :
    (9223372036854775807 : usize) + (1 : usize) = (9223372036854775808 : usize) := by
  decide

/-- `MAX_ALIGN = 2^63 < 2^64`, so its `toNat` is the literal itself. -/
private theorem const_toNat :
    (9223372036854775808 : usize).toNat = 9223372036854775808 := by decide

/-- `usize::MAX = 2^64 - 1`; its `toNat` is the literal itself. -/
private theorem cMAX_toNat :
    (18446744073709551615 : usize).toNat = 18446744073709551615 := by decide

/-- The static inner add `isize::MAX + 1` never overflows `usize`. -/
private theorem no_add_overflow :
    ¬ USize64.addOverflow (9223372036854775807 : usize) (1 : usize) := by decide

/-- `2^64` as a closed `Nat` literal (used to feed `omega`, which cannot
    evaluate `Nat.pow`). -/
private theorem e64 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide

/-! ## Numeric (Nat) bridge lemmas -/

/-- A positive `usize` has positive `toNat`. -/
private theorem toNat_pos_of_ne_zero {n : usize} (hn : n ≠ 0) : 0 < n.toNat := by
  rcases Nat.eq_zero_or_pos n.toNat with h0 | h0
  · exact absurd (USize64.toNat_inj.mp (by simp [h0])) hn
  · exact h0

/-- `n != 0 = true` when `n ≠ 0`. -/
private theorem ne_zero_bool {n : usize} (hn : n ≠ 0) : (n != (0 : usize)) = true := by
  simp [hn]

/-- The division-based overflow predicate, lifted to `Nat`:
    `size > usize::MAX / n` iff `usize::MAX/n < size` over `toNat`. -/
private theorem size_gt_maxdiv_iff (s n : usize) :
    (s > ((18446744073709551615 : usize) / n))
      ↔ 18446744073709551615 / n.toNat < s.toNat := by
  simp only [gt_iff_lt, USize64.lt_iff_toNat_lt, USize64.toNat_div, cMAX_toNat]

/-- `s ≤ usize::MAX / n` whenever the product `s * n` fits in `usize`
    (`≤ 2^64 - 1`).  Standard Euclidean-division reasoning. -/
private theorem size_le_maxdiv_of_mul_le {s nn : Nat} (hpos : 0 < nn)
    (h : s * nn ≤ 18446744073709551615) : s ≤ 18446744073709551615 / nn :=
  (Nat.le_div_iff_mul_le hpos).mpr h

/-- Conversely, if `s * n ≥ 2^64` then `usize::MAX / n < s`: the
    division-based guard fires exactly when the multiplication overflows. -/
private theorem maxdiv_lt_size_of_mul_ge {s nn : Nat} (hpos : 0 < nn)
    (h : 18446744073709551616 ≤ s * nn) : 18446744073709551615 / nn < s := by
  have hcontra : ¬ (s ≤ 18446744073709551615 / nn) := by
    intro hle
    have := (Nat.le_div_iff_mul_le hpos).mp hle
    omega
  omega

/-! ## `max_size_for_align` / `from_size_alignment` reductions -/

/-- `(2^63 : usize) - align` has `toNat` equal to `2^63 - align.toNat`
    (no underflow because `align ≤ 2^63`). -/
private theorem maxsize_toNat (align : usize) (h : align.toNat ≤ 9223372036854775808) :
    ((9223372036854775808 : usize) - align).toNat
      = 9223372036854775808 - align.toNat := by
  have hle : align ≤ (9223372036854775808 : usize) := by
    rw [USize64.le_iff_toNat_le, const_toNat]; exact h
  rw [USize64.toNat_sub_of_le _ _ hle, const_toNat]

/-- Equational form of the inlined `max_size_for_align`: under the legal-align
    precondition it returns exactly `(isize::MAX + 1) - align = 2^63 - align`.
    Transposed verbatim from the reference `max_size_for_align`. -/
private theorem max_size_eq (align : usize) (h : align.toNat ≤ 9223372036854775808) :
    repeat_packed_usize.max_size_for_align align
      = pure ((9223372036854775808 : usize) - align) := by
  have hsub : ¬ USize64.subOverflow ((9223372036854775807 : usize) + 1) align := by
    rw [USize64.subOverflow_iff, const_add, const_toNat]
    omega
  unfold repeat_packed_usize.max_size_for_align
  rw [hax_add_def_usize, if_neg no_add_overflow]
  simp only [pure_bind]
  rw [hax_sub_def_usize, if_neg hsub, const_add]

/-- Equational form of the inlined `from_size_alignment`: with a legal align,
    it returns `Err` exactly when `size > 2^63 - align`, else `Ok`. -/
private theorem from_size_alignment_eq (s align : usize)
    (h : align.toNat ≤ 9223372036854775808) :
    repeat_packed_usize.from_size_alignment s align
      = (if s.toNat > 9223372036854775808 - align.toNat
         then RustM.ok (core_models.result.Result.Err repeat_packed_usize.LayoutError.mk)
         else RustM.ok (core_models.result.Result.Ok
                (repeat_packed_usize.Layout.mk s align))) := by
  unfold repeat_packed_usize.from_size_alignment
  rw [max_size_eq align h]
  simp only [pure_bind]
  rw [hax_gt_def]
  simp only [pure_bind]
  have hiff : (s > ((9223372036854775808 : usize) - align))
                ↔ (s.toNat > 9223372036854775808 - align.toNat) := by
    simp only [gt_iff_lt, USize64.lt_iff_toNat_lt, maxsize_toNat align h]
  by_cases hR : s.toNat > 9223372036854775808 - align.toNat
  · rw [if_pos hR, if_pos (decide_eq_true (hiff.mpr hR))]
    rfl
  · rw [if_neg hR, decide_eq_false (fun hQ => hR (hiff.mp hQ))]
    simp only [Bool.false_eq_true, if_false]
    rfl

/-! ## Reduction of the `repeat_packed` do-block

NOTE on an extraction infidelity uncovered here: Rust's `&&` short-circuits,
so in the Rust source `usize::MAX / n` is never evaluated when `n == 0`.
The Hax extraction does NOT preserve that laziness — the extracted Lean
binds `(18446744073709551615 : usize) /? n` *unconditionally* (via a `←`
hoisted out of the strict `&&?`).  Consequently, for `n = 0`, the extracted
model returns `RustM.fail Error.divisionByZero` (see
`model_diverges_at_zero`), whereas the real Rust function would succeed with
`Ok(Layout { size: 0, align })`.  This makes the `n = 0` case of the two
success obligations unprovable against the extracted module without either
fixing the extraction (forbidden at this stage) or strengthening the
precondition with `n ≠ 0`.  All reductions below therefore assume `n ≠ 0`,
which holds automatically for the two failure obligations. -/

/-- Concrete witness of the extraction infidelity: at `n = 0` the extracted
    model diverges (division by zero) regardless of the layout. -/
private theorem model_diverges_at_zero (layout : repeat_packed_usize.Layout) :
    repeat_packed_usize.repeat_packed layout 0
      = RustM.fail Error.divisionByZero := by
  unfold repeat_packed_usize.repeat_packed
  rw [hax_ne_def]
  simp only [pure_bind]
  rw [hax_div_def_usize, if_pos rfl]
  rfl

/-- Master reduction (requires `n ≠ 0`): the whole do-block collapses to a
    single guarded `if`.  The guard is the extracted division-based overflow
    predicate `(n != 0) && (size > usize::MAX / n)`. -/
private theorem repeat_packed_reduce (layout : repeat_packed_usize.Layout) (n : usize)
    (hn : n ≠ 0) :
    repeat_packed_usize.repeat_packed layout n
      = (if ((n != (0 : usize))
              && decide (layout.size > ((18446744073709551615 : usize) / n)))
         then pure (core_models.result.Result.Err repeat_packed_usize.LayoutError.mk)
         else ((layout.size *? n) >>= fun s =>
                repeat_packed_usize.from_size_alignment s layout.align)) := by
  unfold repeat_packed_usize.repeat_packed
  simp only [hax_ne_def, hax_div_def_usize, if_neg hn, hax_gt_def, hax_and_def,
             pure_bind]

/-- Guard-true branch: the division-based overflow guard fires, so the
    function returns `Err` *before* `from_size_alignment` (no align
    precondition needed). -/
private theorem repeat_packed_err_of_guard (layout : repeat_packed_usize.Layout)
    (n : usize) (hn : n ≠ 0)
    (hgt : layout.size.toNat > 18446744073709551615 / n.toNat) :
    repeat_packed_usize.repeat_packed layout n
      = RustM.ok (core_models.result.Result.Err repeat_packed_usize.LayoutError.mk) := by
  rw [repeat_packed_reduce layout n hn, ne_zero_bool hn, Bool.true_and]
  have hQ : layout.size > ((18446744073709551615 : usize) / n) :=
    (size_gt_maxdiv_iff layout.size n).mpr hgt
  rw [if_pos (decide_eq_true hQ)]
  rfl

/-- Guard-false branch: the overflow guard does not fire, so control reaches
    `size := layout.size * n; from_size_alignment size align`. -/
private theorem repeat_packed_else_of_not_guard (layout : repeat_packed_usize.Layout)
    (n : usize) (hn : n ≠ 0)
    (hnotguard : ¬ (layout.size.toNat > 18446744073709551615 / n.toNat)) :
    repeat_packed_usize.repeat_packed layout n
      = ((layout.size *? n) >>= fun s =>
          repeat_packed_usize.from_size_alignment s layout.align) := by
  rw [repeat_packed_reduce layout n hn]
  have hQf : decide (layout.size > ((18446744073709551615 : usize) / n)) = false := by
    apply decide_eq_false
    rw [size_gt_maxdiv_iff layout.size n]
    exact hnotguard
  rw [hQf, Bool.and_false]
  simp only [Bool.false_eq_true, if_false]

/-- Combined "else" equation: under `n ≠ 0`, a legal align, no `usize`
    multiplication overflow, and the guard not firing, `repeat_packed`
    equals the `from_size_alignment` outcome on the exact product. -/
private theorem repeat_packed_else_eq (layout : repeat_packed_usize.Layout) (n : usize)
    (hn : n ≠ 0)
    (halign : layout.align.toNat ≤ 9223372036854775808)
    (hprod : layout.size.toNat * n.toNat < 2 ^ 64)
    (hnotguard : ¬ (layout.size.toNat > 18446744073709551615 / n.toNat)) :
    repeat_packed_usize.repeat_packed layout n
      = (if layout.size.toNat * n.toNat > 9223372036854775808 - layout.align.toNat
         then RustM.ok (core_models.result.Result.Err repeat_packed_usize.LayoutError.mk)
         else RustM.ok (core_models.result.Result.Ok
                (repeat_packed_usize.Layout.mk (layout.size * n) layout.align))) := by
  rw [repeat_packed_else_of_not_guard layout n hn hnotguard, mul_pure_aux hprod]
  simp only [pure_bind]
  rw [from_size_alignment_eq (layout.size * n) layout.align halign,
      USize64.toNat_mul_of_lt hprod]
where
  mul_pure_aux {x y : usize} (h : x.toNat * y.toNat < 2 ^ 64) :
      (x *? y : RustM usize) = pure (x * y) := by
    have hno : ¬ USize64.mulOverflow x y := by
      rw [USize64.mulOverflow_iff]; omega
    rw [hax_mul_def_usize, if_neg hno]

/-! ## The four contract obligations -/

/-- Postcondition (success, "packed"): captures the first claim of the Rust
    property test `ok_is_packed_and_preserves_align` — when the inputs do not
    overflow `usize` and stay within the `isize` size limit, `repeat_packed`
    succeeds and the result size is *exactly* `size * n` (no inter-instance
    padding). Stated over `.toNat` so it pins the exact product with no wrap.

    Precondition: `align ≤ 2^63` (so the inlined `max_size_for_align` does not
    underflow / panic) and `size * n ≤ max_size_for_align(align) = 2^63 - align`
    (within the `isize` size limit; this bound also forces `size * n` not to
    overflow `usize`, so the division-based overflow guard is `false`).

    PROOF STATUS: the `n ≠ 0` case is fully discharged below (see the
    `repeat_packed_else_eq` scaffolding).  The `n = 0` case is left as `sorry`.

    * Stuck sub-goal: after `by_cases hn0 : n = 0`, the `n = 0` branch goal is
      `∃ r, repeat_packed layout 0 = RustM.ok (Result.Ok r) ∧ …`.  By
      `model_diverges_at_zero`, the extracted model evaluates to
      `RustM.fail Error.divisionByZero` for `n = 0` (Hax did not preserve
      Rust's `&&` short-circuit; `usize::MAX /? 0` is bound unconditionally),
      so no witness `r` can satisfy `RustM.fail _ = RustM.ok (Result.Ok r)`.
      The obligation as stated is therefore false for `n = 0` against the
      extracted module.
    * Structural unblock: regenerating the extraction so that Rust's `&&`
      short-circuit is preserved (the `usize::MAX / n` division guarded by
      `n != 0` rather than hoisted out of a strict `&&?`) would make the
      `n = 0` case return `Ok(Layout { size = 0, align })`, closing this in one
      line via `repeat_packed_else_eq`.  Alternatively, strengthening this
      obligation's precondition with `n ≠ 0` closes it immediately. -/
theorem repeat_packed_ok_is_packed
    (layout : repeat_packed_usize.Layout) (n : usize)
    (halign : layout.align.toNat ≤ 9223372036854775808)
    (hlimit : layout.size.toNat * n.toNat
                ≤ 9223372036854775808 - layout.align.toNat) :
    ∃ r : repeat_packed_usize.Layout,
      repeat_packed_usize.repeat_packed layout n
          = RustM.ok (core_models.result.Result.Ok r)
      ∧ r.size.toNat = layout.size.toNat * n.toNat := by
  by_cases hn0 : n = 0
  · -- n = 0: extraction infidelity (see docstring + `model_diverges_at_zero`).
    sorry
  · have hpos : 0 < n.toNat := toNat_pos_of_ne_zero hn0
    have hcMAX : layout.size.toNat * n.toNat ≤ 18446744073709551615 := by omega
    have hprod : layout.size.toNat * n.toNat < 2 ^ 64 := by
      have e := e64; omega
    have hnotguard : ¬ (layout.size.toNat > 18446744073709551615 / n.toNat) := by
      have := size_le_maxdiv_of_mul_le hpos hcMAX; omega
    have hnotexceed :
        ¬ (layout.size.toNat * n.toNat > 9223372036854775808 - layout.align.toNat) := by
      omega
    refine ⟨repeat_packed_usize.Layout.mk (layout.size * n) layout.align, ?_, ?_⟩
    · rw [repeat_packed_else_eq layout n hn0 halign hprod hnotguard, if_neg hnotexceed]
    · show (layout.size * n).toNat = layout.size.toNat * n.toNat
      exact USize64.toNat_mul_of_lt hprod

/-- Postcondition (success, alignment preserved): captures the second,
    independent claim of `ok_is_packed_and_preserves_align` — the original
    alignment is carried through unchanged (`out.align() == align`). Split
    from the packed-size claim so each contract clause is its own theorem.

    PROOF STATUS: identical to `repeat_packed_ok_is_packed` — the `n ≠ 0`
    case is fully discharged; the `n = 0` case is `sorry` for the same
    extraction-infidelity reason (Hax did not preserve Rust's `&&`
    short-circuit, so the model divides by zero at `n = 0`; see
    `model_diverges_at_zero`).  Structural unblock: regenerate the extraction
    with a short-circuiting `&&`, or strengthen the precondition with
    `n ≠ 0`. -/
theorem repeat_packed_preserves_align
    (layout : repeat_packed_usize.Layout) (n : usize)
    (halign : layout.align.toNat ≤ 9223372036854775808)
    (hlimit : layout.size.toNat * n.toNat
                ≤ 9223372036854775808 - layout.align.toNat) :
    ∃ r : repeat_packed_usize.Layout,
      repeat_packed_usize.repeat_packed layout n
          = RustM.ok (core_models.result.Result.Ok r)
      ∧ r.align = layout.align := by
  by_cases hn0 : n = 0
  · -- n = 0: extraction infidelity (see docstring + `model_diverges_at_zero`).
    sorry
  · have hpos : 0 < n.toNat := toNat_pos_of_ne_zero hn0
    have hcMAX : layout.size.toNat * n.toNat ≤ 18446744073709551615 := by omega
    have hprod : layout.size.toNat * n.toNat < 2 ^ 64 := by
      have e := e64; omega
    have hnotguard : ¬ (layout.size.toNat > 18446744073709551615 / n.toNat) := by
      have := size_le_maxdiv_of_mul_le hpos hcMAX; omega
    have hnotexceed :
        ¬ (layout.size.toNat * n.toNat > 9223372036854775808 - layout.align.toNat) := by
      omega
    refine ⟨repeat_packed_usize.Layout.mk (layout.size * n) layout.align, ?_, rfl⟩
    rw [repeat_packed_else_eq layout n hn0 halign hprod hnotguard, if_neg hnotexceed]

/-- Failure boundary (isize size limit): captures the `n_bad` direction of the
    Rust property test `isize_size_limit_boundary` — when `size * n` does not
    overflow `usize` (so the checked multiplication succeeds and control
    reaches `from_size_alignment`) but the product exceeds the `isize` size
    limit `max_size_for_align(align) = 2^63 - align`, `repeat_packed` returns
    `Err(LayoutError)` (a handled error, modelled by `RustM.ok (.Err …)`, not
    a panic). The `is_ok` (`n_ok`) direction of the same test is captured by
    `repeat_packed_ok_is_packed` / `repeat_packed_preserves_align`. -/
theorem repeat_packed_exceeds_isize_limit_is_err
    (layout : repeat_packed_usize.Layout) (n : usize)
    (hmul : layout.size.toNat * n.toNat < 2 ^ 64)
    (halign : layout.align.toNat ≤ 9223372036854775808)
    (hexceed : 9223372036854775808 - layout.align.toNat
                 < layout.size.toNat * n.toNat) :
    repeat_packed_usize.repeat_packed layout n
      = RustM.ok
          (core_models.result.Result.Err repeat_packed_usize.LayoutError.mk) := by
  -- `hexceed` forces the product (hence `n`) to be positive.
  have hpos : 0 < n.toNat := by
    rcases Nat.eq_zero_or_pos n.toNat with h0 | h0
    · exfalso; rw [h0, Nat.mul_zero] at hexceed; omega
    · exact h0
  have hn0 : n ≠ 0 := by
    intro h; rw [h] at hpos; simp at hpos
  have hcMAX : layout.size.toNat * n.toNat ≤ 18446744073709551615 := by
    have e := e64; omega
  have hnotguard : ¬ (layout.size.toNat > 18446744073709551615 / n.toNat) := by
    have := size_le_maxdiv_of_mul_le hpos hcMAX; omega
  have hexc : layout.size.toNat * n.toNat > 9223372036854775808 - layout.align.toNat := by
    omega
  rw [repeat_packed_else_eq layout n hn0 halign hmul hnotguard, if_pos hexc]

/-- Failure condition (multiplication overflow): captures the Rust property
    test `mul_overflow_is_err` — when `size * n` overflows `usize`, the
    division-based overflow guard (`n != 0 && size > usize::MAX / n`) fires and
    `repeat_packed` returns `Err(LayoutError)`; it must not wrap around and
    report a bogus small layout. This is a handled error, modelled by
    `RustM.ok (.Err …)`, not a panic. The alignment is irrelevant here because
    the overflow branch returns before `from_size_alignment` is reached. -/
theorem repeat_packed_mul_overflow_is_err
    (layout : repeat_packed_usize.Layout) (n : usize)
    (hov : 2 ^ 64 ≤ layout.size.toNat * n.toNat) :
    repeat_packed_usize.repeat_packed layout n
      = RustM.ok
          (core_models.result.Result.Err repeat_packed_usize.LayoutError.mk) := by
  -- `hov` forces the product (hence `n`) to be positive.
  have e := e64
  have hpos : 0 < n.toNat := by
    rcases Nat.eq_zero_or_pos n.toNat with h0 | h0
    · exfalso; rw [h0, Nat.mul_zero] at hov; omega
    · exact h0
  have hn0 : n ≠ 0 := by
    intro h; rw [h] at hpos; simp at hpos
  have hge : 18446744073709551616 ≤ layout.size.toNat * n.toNat := by omega
  have hgt : layout.size.toNat > 18446744073709551615 / n.toNat :=
    maxdiv_lt_size_of_mul_ge hpos hge
  exact repeat_packed_err_of_guard layout n hn0 hgt

end Repeat_packed_usizeObligations
