-- Companion obligations file for the `clever_130_digits` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_130_digits

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_130_digitsObligations

/-! ## Nat-level oracles for the contract -/

/-- Walk through the decimal digits of `n` (high to low via `/ 10`), folding
    the product of odd digits into `acc`. The Bool flag `any_odd` tracks
    whether any odd digit has been observed; if none has when the recursion
    bottoms out at `n = 0`, the final result is `0` rather than the empty
    product `acc`. Mirrors the Rust `walk_at` helper exactly. -/
private def walk_at_nat (n acc : Nat) (any_odd : Bool) : Nat :=
  if h : 0 < n then
    if (n % 10) % 2 = 1 then
      walk_at_nat (n / 10) (acc * (n % 10)) true
    else
      walk_at_nat (n / 10) acc any_odd
  else
    if any_odd then acc else 0
termination_by n
decreasing_by all_goals exact Nat.div_lt_self h (by decide)

/-- Product of the odd decimal digits of `n`, or `0` if `n = 0` or `n` has
    no odd digit at all. Mirrors the Rust `digits` wrapper. -/
private def digits_nat (n : Nat) : Nat :=
  if n = 0 then 0 else walk_at_nat n 1 false

/-- Predicate: every decimal digit of `n` is even (vacuously `true` when
    `n = 0`). Used to phrase the all-even special case. -/
private def all_digits_even_nat (n : Nat) : Bool :=
  if h : 0 < n then
    (n % 10 % 2 == 0) && all_digits_even_nat (n / 10)
  else
    true
termination_by n
decreasing_by exact Nat.div_lt_self h (by decide)

/-! ## Main contract clauses

The Rust source (`mod tests`) carries two proptests and one `known`
unit-tests block. Each contract-style assertion gets one theorem below.

* `prop_matches_reference` — main functional postcondition on every
  `u64`.  Feasibility: the product of odd decimal digits of any
  `u64` is at most `9^20 = 12_157_665_459_056_928_801 < 2^64`, so the
  universal version is true in the Lean model with no precondition.
* `prop_all_even_digits_returns_zero` — the empty-odd-set convention.
* `known` — six concrete pins closed by `native_decide`. -/

/-- Main postcondition: for every `u64 n`, `digits n` succeeds and equals
    the product of the odd decimal digits of `n` (with `0` for `n = 0` or
    the all-even case).  Captures `prop_matches_reference`. -/
theorem digits_matches_reference (n : u64) :
    clever_130_digits.digits n
      = RustM.ok (UInt64.ofNat (digits_nat n.toNat)) := by
  sorry

/-- Empty-odd-set convention: when every decimal digit of `n` is even
    (including `n = 0`), `digits n` is exactly `0`, not the empty product
    `1`.  Captures `prop_all_even_digits_returns_zero`. -/
theorem digits_all_even_returns_zero
    (n : u64) (h : all_digits_even_nat n.toNat = true) :
    clever_130_digits.digits n = RustM.ok (0 : u64) := by
  sorry

/-! ## Unit pins from `known` -/

/-- `digits 0 = 0`. -/
theorem digits_at_0 :
    clever_130_digits.digits 0 = RustM.ok (0 : u64) := by
  native_decide

/-- `digits 1 = 1`. -/
theorem digits_at_1 :
    clever_130_digits.digits 1 = RustM.ok (1 : u64) := by
  native_decide

/-- `digits 4 = 0` — all (one) digit is even. -/
theorem digits_at_4 :
    clever_130_digits.digits 4 = RustM.ok (0 : u64) := by
  native_decide

/-- `digits 235 = 15` — odd digits `3, 5` give product `15`. -/
theorem digits_at_235 :
    clever_130_digits.digits 235 = RustM.ok (15 : u64) := by
  native_decide

/-- `digits 2468 = 0` — every digit is even. -/
theorem digits_at_2468 :
    clever_130_digits.digits 2468 = RustM.ok (0 : u64) := by
  native_decide

/-- `digits 2222 = 0` — every digit is even. -/
theorem digits_at_2222 :
    clever_130_digits.digits 2222 = RustM.ok (0 : u64) := by
  native_decide

end Clever_130_digitsObligations
