-- Companion obligations file for the `clever_144_specialFilter` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_144_specialFilter

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_144_specialFilterObligations

/-! ## Specification oracle

`first_digit_nat n` returns the leading decimal digit of a non-negative integer
`n`.  For `n < 10` it is the identity; otherwise it recurses on `n / 10`.  This
mirrors the Rust `first_digit_at` on non-negative inputs (which is all that
matters here: the contract's per-element predicate requires `v > 10`, so any
qualifying element is strictly positive and the Rust truncated division on
positive operands coincides with `Nat` floor division).
-/

/-- Leading decimal digit of `n` (returns `n` itself for `n < 10`). -/
private def first_digit_nat (n : Nat) : Nat :=
  if n < 10 then n else first_digit_nat (n / 10)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

/-- Reference predicate ("qualifies for the count") at the `Int` level.
    Mirrors the Rust `ref_qualifies` test predicate:
    `v > 10  ∧  first_digit(v) % 2 = 1  ∧  v % 10 % 2 = 1`.
    When `n ≤ 10` the conjunction's first clause is false, so the value of the
    other clauses for non-positive `n` is irrelevant; on `n > 10` we have
    `n.toNat = n` and Lean's `Int` `%` agrees with Rust's truncated `%`.

    Declared as `abbrev` so the `Decidable` instance is found automatically by
    unfolding into a conjunction of decidable atoms. -/
private abbrev qualifies_int (n : Int) : Prop :=
  10 < n ∧ (first_digit_nat n.toNat) % 2 = 1 ∧ n % 10 % 2 = 1

/-! ## Obligation theorems

Each `theorem` below captures one independent contract clause from the
property tests of `specialFilter`.  Proofs are left as `sorry` placeholders;
the proof stage discharges them.
-/

/-- **Empty-slice boundary.**  Mirrors proptest `empty_is_zero`:
    `specialFilter([]) = 0`. -/
theorem specialFilter_empty
    (nums : RustSlice i64) (h_empty : nums.val.size = 0) :
    clever_144_specialFilter.specialFilter nums = RustM.ok (0 : i64) := by
  sorry

/-- **Lower bound of the count.**  Captures the `c >= 0` half of proptest
    `count_in_range`.  The size precondition `nums.val.size < 2^63` is the
    natural Lean generalisation of the proptest's bounded vector length
    (`0..50`): without it, the inner `acc +? 1` step could overflow on a slice
    longer than `2^63` and the universal claim becomes false in the model. -/
theorem specialFilter_nonneg
    (nums : RustSlice i64) (h_size : (nums.val.size : Int) < 2^63) :
    ∃ r : i64,
      clever_144_specialFilter.specialFilter nums = RustM.ok r ∧ 0 ≤ r.toInt := by
  sorry

/-- **Upper bound of the count.**  Captures the `c <= len` half of proptest
    `count_in_range`. Same size precondition as the lower bound — the counter
    is one i64 increment per qualifying element, and the slice length must fit
    in i64 for the universal claim to be true in the model. -/
theorem specialFilter_le_size
    (nums : RustSlice i64) (h_size : (nums.val.size : Int) < 2^63) :
    ∃ r : i64,
      clever_144_specialFilter.specialFilter nums = RustM.ok r
      ∧ r.toInt ≤ (nums.val.size : Int) := by
  sorry

/-- **Additivity over concatenation.**  Mirrors proptest
    `distributes_over_concat`: `specialFilter(a ++ b) = specialFilter(a) +
    specialFilter(b)`.  The combined-size precondition `c.val.size < 2^63`
    bounds the counter on the concatenated slice (and therefore on `a` and `b`
    individually) so the inner `acc +? 1` step never overflows. -/
theorem specialFilter_additive
    (a b c : RustSlice i64)
    (h_concat : c.val = a.val ++ b.val)
    (h_c_size : (c.val.size : Int) < 2^63) :
    ∃ ra rb rc : i64,
      clever_144_specialFilter.specialFilter a = RustM.ok ra
      ∧ clever_144_specialFilter.specialFilter b = RustM.ok rb
      ∧ clever_144_specialFilter.specialFilter c = RustM.ok rc
      ∧ rc.toInt = ra.toInt + rb.toInt := by
  sorry

/-- **Per-element predicate characterisation on a singleton.**  Mirrors
    proptest `singleton_matches_predicate`: on a one-element slice `[v]`, the
    result is `1` iff `v` qualifies (i.e. `v > 10`, leading decimal digit odd,
    and trailing decimal digit odd) and `0` otherwise.

    No size precondition is needed: `size = 1` fits trivially, the counter
    rises at most to `1`, `first_digit_at v` is total on `i64` (it only
    divides by `10`, never by `-1`, so `/?` never fails), and the inner mod
    test `v %? 10` likewise cannot fail. -/
theorem specialFilter_singleton_matches_predicate (v : i64) :
    clever_144_specialFilter.specialFilter
        { val := #[v],
          size_lt_usizeSize := by show (1 : Nat) < USize64.size; decide }
      = RustM.ok (if qualifies_int v.toInt then (1 : i64) else (0 : i64)) := by
  sorry

end Clever_144_specialFilterObligations
