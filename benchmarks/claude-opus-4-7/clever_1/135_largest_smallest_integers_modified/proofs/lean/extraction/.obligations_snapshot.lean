-- Companion obligations file for the `clever_135_largest_smallest_integers` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_135_largest_smallest_integers

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_135_largest_smallest_integersObligations

/-! ## Theorems for the first component (largest negative).

The Rust property tests assert:

* `first_some_iff_has_negative` — `a.is_some() ↔ ∃ x ∈ v, x < 0`
* `first_is_largest_negative` — when `a = Some(x)`:
    `x < 0`, `x ∈ v`, and `∀ y ∈ v, y < 0 → y ≤ x`.

The latter is split into one theorem per sub-clause. -/

/-- Liveness: the first component is `Some` exactly when `lst` contains a
    negative element. Covers proptest `first_some_iff_has_negative`. -/
theorem first_some_iff_has_negative
    (lst : RustSlice i64)
    (a b : core_models.option.Option i64)
    (hres : clever_135_largest_smallest_integers.largest_smallest_integers lst
              = RustM.ok (rust_primitives.hax.Tuple2.mk a b)) :
    (∃ x : i64, a = core_models.option.Option.Some x) ↔
    (∃ (i : Nat) (hi : i < lst.val.size), (lst.val[i]'hi).toInt < 0) := by
  sorry

/-- Value-property: when the first component is `Some x`, `x` is negative.
    Sub-clause of proptest `first_is_largest_negative`. -/
theorem first_some_value_is_negative
    (lst : RustSlice i64) (x : i64) (b : core_models.option.Option i64)
    (hres : clever_135_largest_smallest_integers.largest_smallest_integers lst
              = RustM.ok (rust_primitives.hax.Tuple2.mk
                            (core_models.option.Option.Some x) b)) :
    x.toInt < 0 := by
  sorry

/-- Membership: when the first component is `Some x`, `x` appears in `lst`.
    Sub-clause of proptest `first_is_largest_negative`. -/
theorem first_some_value_in_list
    (lst : RustSlice i64) (x : i64) (b : core_models.option.Option i64)
    (hres : clever_135_largest_smallest_integers.largest_smallest_integers lst
              = RustM.ok (rust_primitives.hax.Tuple2.mk
                            (core_models.option.Option.Some x) b)) :
    ∃ (i : Nat) (hi : i < lst.val.size), (lst.val[i]'hi) = x := by
  sorry

/-- Maximality: when the first component is `Some x`, every negative element
    of `lst` is at most `x`.
    Sub-clause of proptest `first_is_largest_negative`. -/
theorem first_some_value_is_largest_negative
    (lst : RustSlice i64) (x : i64) (b : core_models.option.Option i64)
    (hres : clever_135_largest_smallest_integers.largest_smallest_integers lst
              = RustM.ok (rust_primitives.hax.Tuple2.mk
                            (core_models.option.Option.Some x) b)) :
    ∀ (i : Nat) (hi : i < lst.val.size),
      (lst.val[i]'hi).toInt < 0 → (lst.val[i]'hi).toInt ≤ x.toInt := by
  sorry

/-! ## Theorems for the second component (smallest positive).

The Rust property tests assert:

* `second_some_iff_has_positive` — `b.is_some() ↔ ∃ x ∈ v, x > 0`
* `second_is_smallest_positive` — when `b = Some(y)`:
    `y > 0`, `y ∈ v`, and `∀ z ∈ v, z > 0 → y ≤ z`. -/

/-- Liveness: the second component is `Some` exactly when `lst` contains a
    positive element. Covers proptest `second_some_iff_has_positive`. -/
theorem second_some_iff_has_positive
    (lst : RustSlice i64)
    (a b : core_models.option.Option i64)
    (hres : clever_135_largest_smallest_integers.largest_smallest_integers lst
              = RustM.ok (rust_primitives.hax.Tuple2.mk a b)) :
    (∃ y : i64, b = core_models.option.Option.Some y) ↔
    (∃ (i : Nat) (hi : i < lst.val.size), 0 < (lst.val[i]'hi).toInt) := by
  sorry

/-- Value-property: when the second component is `Some y`, `y` is positive.
    Sub-clause of proptest `second_is_smallest_positive`. -/
theorem second_some_value_is_positive
    (lst : RustSlice i64) (a : core_models.option.Option i64) (y : i64)
    (hres : clever_135_largest_smallest_integers.largest_smallest_integers lst
              = RustM.ok (rust_primitives.hax.Tuple2.mk a
                            (core_models.option.Option.Some y))) :
    0 < y.toInt := by
  sorry

/-- Membership: when the second component is `Some y`, `y` appears in `lst`.
    Sub-clause of proptest `second_is_smallest_positive`. -/
theorem second_some_value_in_list
    (lst : RustSlice i64) (a : core_models.option.Option i64) (y : i64)
    (hres : clever_135_largest_smallest_integers.largest_smallest_integers lst
              = RustM.ok (rust_primitives.hax.Tuple2.mk a
                            (core_models.option.Option.Some y))) :
    ∃ (i : Nat) (hi : i < lst.val.size), (lst.val[i]'hi) = y := by
  sorry

/-- Minimality: when the second component is `Some y`, every positive element
    of `lst` is at least `y`.
    Sub-clause of proptest `second_is_smallest_positive`. -/
theorem second_some_value_is_smallest_positive
    (lst : RustSlice i64) (a : core_models.option.Option i64) (y : i64)
    (hres : clever_135_largest_smallest_integers.largest_smallest_integers lst
              = RustM.ok (rust_primitives.hax.Tuple2.mk a
                            (core_models.option.Option.Some y))) :
    ∀ (i : Nat) (hi : i < lst.val.size),
      0 < (lst.val[i]'hi).toInt → y.toInt ≤ (lst.val[i]'hi).toInt := by
  sorry

end Clever_135_largest_smallest_integersObligations
