-- Companion obligations file for the `clever_160_generate_integers` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_160_generate_integers

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_160_generate_integersObligations

/-! ## Contract clauses for `generate_integers(a, b)`.

`generate_integers` returns the even single-digit integers (`0, 2, 4, 6, 8`)
in `[min(a, b), max(a, b)]`, in ascending order. The Rust property tests
break the contract into four independent clauses:

1. Soundness — every element returned is even, ≤ 8, ≥ min(a, b), ≤ max(a, b).
2. Completeness — every even single-digit integer in [min(a, b), max(a, b)]
   appears in the output.
3. Strict ascending order.
4. Symmetry — `generate_integers(a, b) = generate_integers(b, a)`.

`generate_integers` never fails on any `(a, b) : u64 × u64`: the inner
`build_at` recurses at most until `k = 9`, so `k +? 1` never overflows, and
the result `Vec` has size ≤ 5, so the `extend_from_slice` 1-element push
never overflows `USize64.size`. Statements therefore use the
`hres : generate_integers a b = RustM.ok v` form. -/

/-- Soundness clause (parity): every element of the returned `Vec` is even.

    Captures part of the Rust property test
    `every_element_is_even_single_digit_in_range`. -/
theorem all_elements_even
    (a b : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_160_generate_integers.generate_integers a b = RustM.ok v) :
    ∀ (k : Nat) (hk : k < v.val.size), (v.val[k]'hk).toNat % 2 = 0 := by
  sorry

/-- Soundness clause (single-digit upper cap): every element of the returned
    `Vec` is at most `8`.

    Captures part of the Rust property test
    `every_element_is_even_single_digit_in_range`. -/
theorem all_elements_at_most_8
    (a b : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_160_generate_integers.generate_integers a b = RustM.ok v) :
    ∀ (k : Nat) (hk : k < v.val.size), (v.val[k]'hk).toNat ≤ 8 := by
  sorry

/-- Soundness clause (lower bound): every element of the returned `Vec` is at
    least `min(a, b)`.

    Captures part of the Rust property test
    `every_element_is_even_single_digit_in_range`. -/
theorem all_elements_at_least_min
    (a b : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_160_generate_integers.generate_integers a b = RustM.ok v) :
    ∀ (k : Nat) (hk : k < v.val.size),
      min a.toNat b.toNat ≤ (v.val[k]'hk).toNat := by
  sorry

/-- Soundness clause (upper bound): every element of the returned `Vec` is at
    most `max(a, b)`.

    Captures part of the Rust property test
    `every_element_is_even_single_digit_in_range`. -/
theorem all_elements_at_most_max
    (a b : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_160_generate_integers.generate_integers a b = RustM.ok v) :
    ∀ (k : Nat) (hk : k < v.val.size),
      (v.val[k]'hk).toNat ≤ max a.toNat b.toNat := by
  sorry

/-- Completeness clause: every even single-digit integer in
    `[min(a, b), max(a, b)]` appears in the returned `Vec`.

    Captures the Rust property test
    `every_even_single_digit_in_range_is_present`. -/
theorem complete
    (a b : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_160_generate_integers.generate_integers a b = RustM.ok v)
    (x : u64)
    (hx_even : x.toNat % 2 = 0)
    (hx_le_8 : x.toNat ≤ 8)
    (hx_ge_lo : min a.toNat b.toNat ≤ x.toNat)
    (hx_le_hi : x.toNat ≤ max a.toNat b.toNat) :
    ∃ (k : Nat) (hk : k < v.val.size), (v.val[k]'hk) = x := by
  sorry

/-- Ordering clause: consecutive entries of the returned `Vec` are strictly
    increasing. Captures the Rust property test `result_is_strictly_ascending`. -/
theorem strictly_ascending
    (a b : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_160_generate_integers.generate_integers a b = RustM.ok v) :
    ∀ (k : Nat) (hk : k + 1 < v.val.size),
      (v.val[k]'(Nat.lt_of_succ_lt hk)).toNat < (v.val[k + 1]'hk).toNat := by
  sorry

/-- Symmetry clause: swapping the arguments yields the same result.

    Captures the Rust property test `symmetric_in_arguments`. -/
theorem symmetric_in_arguments
    (a b : u64) :
    clever_160_generate_integers.generate_integers a b =
      clever_160_generate_integers.generate_integers b a := by
  sorry

end Clever_160_generate_integersObligations
