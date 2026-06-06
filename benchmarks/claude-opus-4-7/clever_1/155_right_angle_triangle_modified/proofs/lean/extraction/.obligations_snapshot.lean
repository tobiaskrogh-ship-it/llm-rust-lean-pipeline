-- Companion obligations file for the `clever_155_right_angle_triangle` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_155_right_angle_triangle

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_155_right_angle_triangleObligations

open clever_155_right_angle_triangle

/-! ## Failure mode

`right_angle_triangle` performs unchecked `u64` multiplications and additions;
in the model these are represented by the partial operators `*?` / `+?` which
fail with `RustM.fail .integerOverflow` when the operation would wrap.

The Rust `#[should_panic]` test `overflow_panics_in_debug` calls the function
with `(u64::MAX, 1, 1)` — `u64::MAX * u64::MAX` overflows immediately at the
first squaring `a *? a`. The clause below captures exactly that failure path:
when `a.toNat * a.toNat ≥ 2 ^ 64`, the function returns `.fail .integerOverflow`. -/
theorem right_angle_triangle_overflow_a (a b c : u64)
    (h : 2 ^ 64 ≤ a.toNat * a.toNat) :
    right_angle_triangle a b c = RustM.fail Error.integerOverflow := by
  sorry

/-! ## Functional correctness (docstring spec)

The docstring states: "Return true iff one of the three squared-side equations
holds: `a² + b² == c²`, `a² + c² == b²`, or `b² + c² == a²`."

Stated as a Hoare triple because the postcondition is an `iff` rather than a
specific value. The three pairwise-sum preconditions are the minimal guard
that lets every branch's `+?` evaluate without overflow (and they imply
`a*?a`, `b*?b`, `c*?c` all fit, since e.g. `a*a ≤ a*a + b*b`). -/
theorem right_angle_triangle_spec (a b c : u64) :
    ⦃ ⌜ a.toNat * a.toNat + b.toNat * b.toNat < 2 ^ 64 ∧
        a.toNat * a.toNat + c.toNat * c.toNat < 2 ^ 64 ∧
        b.toNat * b.toNat + c.toNat * c.toNat < 2 ^ 64 ⌝ ⦄
    right_angle_triangle a b c
    ⦃ ⇓ r => ⌜ r = true ↔
        a.toNat * a.toNat + b.toNat * b.toNat = c.toNat * c.toNat ∨
        a.toNat * a.toNat + c.toNat * c.toNat = b.toNat * b.toNat ∨
        b.toNat * b.toNat + c.toNat * c.toNat = a.toNat * a.toNat ⌝ ⦄ := by
  sorry

/-! ## Permutation invariance

The Rust property test `permutation_invariant` asserts that the result depends
only on the multiset `{a, b, c}` — every permutation of the three arguments
gives the same answer.

We expose the two transpositions `(a b)` and `(b c)`; together they generate
the symmetric group `S_3` on the three arguments, so every other equality the
proptest asserts follows by composition.

The shared no-overflow precondition (all three pairwise sums fit) is
necessary: with a single overflowing sum, swapping arguments can change
which `+?` is evaluated first, which can change `.fail` into `.ok true`. -/
theorem right_angle_triangle_swap_ab (a b c : u64)
    (hab : a.toNat * a.toNat + b.toNat * b.toNat < 2 ^ 64)
    (hac : a.toNat * a.toNat + c.toNat * c.toNat < 2 ^ 64)
    (hbc : b.toNat * b.toNat + c.toNat * c.toNat < 2 ^ 64) :
    right_angle_triangle a b c = right_angle_triangle b a c := by
  sorry

theorem right_angle_triangle_swap_bc (a b c : u64)
    (hab : a.toNat * a.toNat + b.toNat * b.toNat < 2 ^ 64)
    (hac : a.toNat * a.toNat + c.toNat * c.toNat < 2 ^ 64)
    (hbc : b.toNat * b.toNat + c.toNat * c.toNat < 2 ^ 64) :
    right_angle_triangle a b c = right_angle_triangle a c b := by
  sorry

/-! ## Pythagorean recognition (positive direction)

The Rust property test `euclid_generated_triples_recognised` instantiates
Euclid's parametrisation `(m²-n², 2mn, m²+n²)` and asserts the function
returns `true`. Euclid's formula is a way of enumerating Pythagorean triples;
the contract clause it exercises is the more general statement below — the
function returns `true` for every Pythagorean triple (under no-overflow). -/
theorem right_angle_triangle_recognises_pythagorean (a b c : u64)
    (h_a2 : a.toNat * a.toNat < 2 ^ 64)
    (h_b2 : b.toNat * b.toNat < 2 ^ 64)
    (h_ab : a.toNat * a.toNat + b.toNat * b.toNat < 2 ^ 64)
    (h_pyth : a.toNat * a.toNat + b.toNat * b.toNat = c.toNat * c.toNat) :
    right_angle_triangle a b c = RustM.ok true := by
  sorry

/-! ## Equilateral (negative direction)

The Rust property test `equilateral_positive_is_not_right` asserts that
`right_angle_triangle a a a` is `false` for every `a ≥ 1` in its proptest
range. The contract: with positive side `a`, `2a² ≠ a²`, so none of the three
identical equations holds.

Precondition `2 * a.toNat * a.toNat < 2 ^ 64` is necessary: with `a = a = a`
the first branch's sum is `a² +? a² = 2a²`, which must not overflow for the
function to reach the comparison. -/
theorem right_angle_triangle_equilateral_positive_not_right (a : u64)
    (h_pos : 0 < a.toNat)
    (h_fits : 2 * (a.toNat * a.toNat) < 2 ^ 64) :
    right_angle_triangle a a a = RustM.ok false := by
  sorry

/-! ## Zero-side boundary cases

The Rust property test `zero_side_with_equal_others_is_right` asserts that
all three placements of a zero side with two equal other sides return `true`.
Three independent theorems, one per placement, because the placement of `0`
changes which branch fires and which `+?` must not overflow. -/

/-- `(0, n, n)`: the first branch `0² + n² == n²` is `True`. Only requires
    `n*n` to fit (then the `+0` operation is trivially safe). -/
theorem right_angle_triangle_zero_first (n : u64)
    (h_fits : n.toNat * n.toNat < 2 ^ 64) :
    right_angle_triangle 0 n n = RustM.ok true := by
  sorry

/-- `(n, 0, n)`: the first branch `n² + 0 == n²` is `True`. Only requires
    `n*n` to fit. -/
theorem right_angle_triangle_zero_middle (n : u64)
    (h_fits : n.toNat * n.toNat < 2 ^ 64) :
    right_angle_triangle n 0 n = RustM.ok true := by
  sorry

/-- `(n, n, 0)`: the first branch `n² + n² == 0` is False (for any input
    where the branch is reachable), so the function evaluates the second
    branch `n² + 0 == n²` which is True. The stronger precondition
    `2 * n² < 2^64` is needed because the first branch's `n² +? n²`
    must not overflow before the function reaches the second branch. -/
theorem right_angle_triangle_zero_last (n : u64)
    (h_fits : 2 * (n.toNat * n.toNat) < 2 ^ 64) :
    right_angle_triangle n n 0 = RustM.ok true := by
  sorry

end Clever_155_right_angle_triangleObligations
