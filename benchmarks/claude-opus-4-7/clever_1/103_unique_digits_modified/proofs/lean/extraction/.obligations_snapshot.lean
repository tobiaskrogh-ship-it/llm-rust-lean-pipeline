-- Companion obligations file for the `clever_103_unique_digits` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_103_unique_digits

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_103_unique_digitsObligations

/-! ## Specification oracles.

The Rust property tests are stated against a pure reference predicate
`all_odd_digits : u64 → Bool` (transcribed from the `all_odd_digits`
helper in the Rust `tests` module) and a `vec_count : Array u64 → u64 →
Nat → Nat` count function that lifts the multiset clause to a single
equation per target value.  The reference predicate returns `false` on
`0` to match the Rust convention used by the implementation
(`has_even_digit_at 0 = false ⇒ has_even_digit 0 = true ⇒ filtered
out`). -/

/-- Count occurrences of `target` among the first `k` entries of `s`. -/
private def vec_count (s : Array u64) (target : u64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      if h : k < s.size then
        (if (s[k]'h) = target then 1 else 0) + vec_count s target k
      else
        vec_count s target k

/-- Pure spec predicate: `n` has every decimal digit odd.  Matches the
    Rust `all_odd_digits` helper, which returns `false` on `n = 0`. -/
private def all_odd_digits_nat : Nat → Bool
  | 0     => false
  | n + 1 =>
      if (n + 1) % 10 % 2 = 0 then false
      else if (n + 1) / 10 = 0 then true
      else all_odd_digits_nat ((n + 1) / 10)
termination_by n => n
decreasing_by
  exact Nat.div_lt_self (Nat.succ_pos _) (by decide)

/-- Lifted spec: `n : u64` has every decimal digit odd. -/
private def all_odd_digits (n : u64) : Bool := all_odd_digits_nat n.toNat

/-! ## Anchor: empty input yields empty output. -/

/-- Anchor: `unique_digits` succeeds on an empty input slice and returns
    an empty `Vec`.  Pins the base case of the recursion. -/
theorem empty_input_yields_empty_output
    (x : RustSlice u64) (hempty : x.val.size = 0) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_103_unique_digits.unique_digits x = RustM.ok v ∧
      v.val.size = 0 := by
  sorry

/-! ## Postcondition 1: output is sorted (non-decreasing).

    Captures the proptest `output_is_sorted`.  The proptest checks
    `windows(2)`; we phrase the obligation in the matching consecutive
    form `v[k].toNat ≤ v[k+1].toNat`. -/

/-- Postcondition 1: consecutive output entries are non-decreasing. -/
theorem output_is_sorted
    (x : RustSlice u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_103_unique_digits.unique_digits x = RustM.ok v)
    (k : Nat) (hk : k + 1 < v.val.size) :
    (v.val[k]'(Nat.lt_of_succ_lt hk)).toNat ≤ (v.val[k + 1]'hk).toNat := by
  sorry

/-! ## Postcondition 2: output is the all-odd-digit input multiset.

    Captures the proptest `output_is_filter_multiset`.  Stated as a
    per-target count equation: the count of `t` in the output equals
    the count of `t` in the input when `all_odd_digits t` holds, and
    `0` otherwise.  This single equation captures
      (a) soundness — only all-odd-digit input values appear in the
          output;
      (b) completeness — every all-odd-digit input value appears in
          the output;
      (c) multiplicity preservation — duplicates are preserved. -/

/-- Postcondition 2: per-element count agrees with the filtered input. -/
theorem output_count_equals_filtered_count
    (x : RustSlice u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_103_unique_digits.unique_digits x = RustM.ok v)
    (t : u64) :
    vec_count v.val t v.val.size
      = (if all_odd_digits t then vec_count x.val t x.val.size else 0) := by
  sorry

end Clever_103_unique_digitsObligations
