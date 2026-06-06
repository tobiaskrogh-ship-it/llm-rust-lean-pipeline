-- Companion obligations file for the `clever_125_is_sorted` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_125_is_sorted

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_125_is_sortedObligations

/-! ## Specification predicates.

The Rust function `is_sorted lst` is intended to return `true` iff `lst`
is non-decreasing AND no value appears more than twice. We capture the
two clauses as separate predicates on the underlying list. -/

/-- `total_count l target k` is the number of indices `j < k` for which
`l.val[j] = target`. The `dite` keeps the definition total — every
theorem below applies it with `k ≤ l.val.size`, so the bounded indices
always exist. -/
private def total_count (l : RustSlice u64) (target : u64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      if h : k < l.val.size then
        (if (l.val[k]'h) = target then 1 else 0)
          + total_count l target k
      else
        total_count l target k

/-- Adjacent-pair non-decreasing predicate. -/
private def is_nondec (l : RustSlice u64) : Prop :=
  ∀ j : Nat, ∀ (hj1 : j + 1 < l.val.size),
    l.val[j]'(Nat.lt_of_succ_lt hj1) ≤ l.val[j+1]'hj1

/-- Every value appears at most twice in `l`. -/
private def multiplicity_ok (l : RustSlice u64) : Prop :=
  ∀ i : Nat, ∀ (hi : i < l.val.size),
    total_count l (l.val[i]'hi) l.val.size ≤ 2

/-! ## Contract clauses.

The proptest `matches_brute_force` asserts the biconditional
`is_sorted(l) ↔ (non-decreasing ∧ no value appears more than twice)`.
We split it into three independent theorems: two soundness clauses
(`is_sorted = ok true` implies each conjunct of the spec) and one
completeness clause (both conjuncts together imply `is_sorted = ok true`).

The proptest `triple_repeat_rejected` is the explicit negative pin-down
for the multiplicity clause: any value with count > 2 forces a `false`
return. -/

/-- Sortedness clause (soundness). If `is_sorted lst` returns `true`,
    then `lst` is non-decreasing. Captures the forward direction of
    `matches_brute_force` for the order conjunct. -/
theorem nondec_of_is_sorted_true
    (lst : RustSlice u64)
    (h : clever_125_is_sorted.is_sorted lst = RustM.ok true) :
    is_nondec lst := by
  sorry

/-- Multiplicity clause (soundness). If `is_sorted lst` returns `true`,
    then no value appears more than twice in `lst`. Captures the forward
    direction of `matches_brute_force` for the multiplicity conjunct. -/
theorem multiplicity_ok_of_is_sorted_true
    (lst : RustSlice u64)
    (h : clever_125_is_sorted.is_sorted lst = RustM.ok true) :
    multiplicity_ok lst := by
  sorry

/-- Completeness. If `lst` is non-decreasing and every value appears at
    most twice, then `is_sorted lst` returns `true`. Captures the
    backward direction of `matches_brute_force`. -/
theorem is_sorted_returns_true
    (lst : RustSlice u64)
    (h_nondec : is_nondec lst)
    (h_mult : multiplicity_ok lst) :
    clever_125_is_sorted.is_sorted lst = RustM.ok true := by
  sorry

/-- Multiplicity-violation pin-down. If some value occurs strictly more
    than twice in `lst`, then `is_sorted lst` returns `false`. Captures
    the proptest `triple_repeat_rejected` and a (stronger) generalisation
    of the contrapositive of `multiplicity_ok_of_is_sorted_true`
    (stronger because it asserts `ok false`, not just ¬`ok true`). -/
theorem triple_repeat_rejected
    (lst : RustSlice u64)
    (h : ∃ v : u64, 2 < total_count lst v lst.val.size) :
    clever_125_is_sorted.is_sorted lst = RustM.ok false := by
  sorry

end Clever_125_is_sortedObligations
