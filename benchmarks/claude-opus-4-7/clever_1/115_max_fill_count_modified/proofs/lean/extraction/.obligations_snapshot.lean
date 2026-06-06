-- Companion obligations file for the `clever_115_max_fill_count` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_115_max_fill_count

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_115_max_fill_countObligations

/-! ## Specification oracles. -/

/-- Count occurrences of `target` among the first `k` entries of `s`.
    Used to express the multiset / permutation postcondition. -/
private def vec_count (s : Array u64) (target : u64) : Nat → Nat
  | 0     => 0
  | k + 1 =>
      if h : k < s.size then
        (if (s[k]'h) = target then 1 else 0) + vec_count s target k
      else
        vec_count s target k

/-- Nat-level popcount: the number of `1`-bits in the binary
    representation of `n`. Mirrors `popcount_at` in the Rust source —
    `popcount_at(n, acc) = acc + popcount_nat n.toNat`. -/
private def popcount_nat : Nat → Nat
  | 0     => 0
  | n + 1 => (n + 1) % 2 + popcount_nat ((n + 1) / 2)
termination_by n => n
decreasing_by
  exact Nat.div_lt_self (Nat.succ_pos _) (by decide)

/-- Lifted spec: popcount of a `u64` value, matching `u64::count_ones`. -/
private def popcount (x : u64) : Nat := popcount_nat x.toNat

/-! ## Obligation theorems. -/

/-- Anchor: an empty input slice yields a successful empty output. -/
theorem empty_input_yields_empty_output
    (l : RustSlice u64) (hempty : l.val.size = 0) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_115_max_fill_count.sort_by_popcount l = RustM.ok v ∧
      v.val.size = 0 := by
  sorry

/-- Postcondition (1/2): the output is a permutation of the input.
    Expressed as equality of per-target occurrence counts across the
    whole vector — i.e. equality as multisets. Corresponds to the
    `output_is_permutation_of_input` property test. -/
theorem output_is_permutation_of_input
    (l : RustSlice u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_115_max_fill_count.sort_by_popcount l = RustM.ok v)
    (target : u64) :
    vec_count v.val target v.val.size
      = vec_count l.val target l.val.size := by
  sorry

/-- Postcondition (2/2): consecutive output entries are non-decreasing
    under the lexicographic key `(popcount, value)`. Captures both the
    primary popcount-ascending order and the value-ascending tiebreaker
    within each popcount class. Corresponds to the
    `output_is_sorted_by_popcount_then_value` property test. -/
theorem output_is_sorted_by_popcount_then_value
    (l : RustSlice u64)
    (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_115_max_fill_count.sort_by_popcount l = RustM.ok v)
    (k : Nat) (hk : k + 1 < v.val.size) :
    popcount (v.val[k]'(Nat.lt_of_succ_lt hk))
        < popcount (v.val[k + 1]'hk)
    ∨ (popcount (v.val[k]'(Nat.lt_of_succ_lt hk))
          = popcount (v.val[k + 1]'hk)
        ∧ (v.val[k]'(Nat.lt_of_succ_lt hk)).toNat
            ≤ (v.val[k + 1]'hk).toNat) := by
  sorry

end Clever_115_max_fill_countObligations
