-- Companion obligations file for the `clever_070_triangle_area` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_070_triangle_area

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_070_triangle_areaObligations

/-! ## `isqrt` characterization

The recursive helper `isqrt_bin n lo hi` performs binary search for
`floor(sqrt n)` within `[lo, hi]`. Wrapped by `isqrt`, which short-circuits
non-positive inputs to `0` and otherwise calls `isqrt_bin n 0 3037000500`.

The upper bound `3037000500 > floor(sqrt(i64::MAX)) = 3037000499` is large
enough that for every `n : i64` with `0 ≤ n`, the invariant `n < hi*hi`
holds, so the binary search returns the true integer square root. Also,
the largest `mid` ever computed is `≤ 3037000499`, so `mid * mid ≤
(3037000499)^2 < 2^63` and the inner multiplication never overflows. -/

/-- Boundary clause: `isqrt n = 0` for any `n ≤ 0`.

    Pins the early-return arm `if n <=? 0 then pure 0` in `isqrt`. -/
theorem isqrt_nonpos (n : i64) (hn : n.toInt ≤ 0) :
    clever_070_triangle_area.isqrt n = RustM.ok (0 : i64) := by
  sorry

/-- Full postcondition for `isqrt`: returns the integer square root.

    For any `n : i64` with `0 ≤ n.toInt`, `isqrt n` returns some `r`
    satisfying `0 ≤ r`, `r * r ≤ n`, and `n < (r + 1) * (r + 1)` (the
    last bound stated at `Int` level so the `(r+1)^2` upper bound carries
    no overflow caveat). This characterises `r = floor(sqrt n)` and
    captures the contract that the binary-search helper actually meets. -/
theorem isqrt_postcondition (n : i64) (hn : 0 ≤ n.toInt) :
    ∃ r : i64, clever_070_triangle_area.isqrt n = RustM.ok r ∧
      0 ≤ r.toInt ∧
      r.toInt * r.toInt ≤ n.toInt ∧
      n.toInt < (r.toInt + 1) * (r.toInt + 1) := by
  sorry

/-! ## `triangle_area` contract

The three property tests in the Rust source decompose as follows:

  * `invalid_iff_minus_one` ⇒ two directions:
       - invalid → returns `-1` (`triangle_area_invalid_returns_minus_one`)
       - valid   → returns `r ≥ 0` (`triangle_area_valid_returns_nonneg`)
  * `matches_oracle`        ⇒ valid → closed-form match
       (`triangle_area_valid_formula`)
  * `known_cases`           ⇒ four concrete pinned values.

All non-boundary theorems carry the three "no-overflow on the
validity-check sums" preconditions for `a +? b`, `a +? c`, `b +? c`,
because the Hax extraction evaluates all three additions before any
boolean is consumed. The valid-branch theorems also carry positivity and
a Heron-product bound that suffices for every intermediate `+?`, `-?`,
`*?` in the chain to stay in i64 range. -/

/-- Invalid-triangle case: when the validity-check sums do not overflow
    and at least one of the triangle inequalities flips (one side is at
    least the sum of the other two), the function returns the sentinel
    `-1`.

    Corresponds to the `else` branch of `invalid_iff_minus_one`:
    `prop_assert_eq!(triangle_area(a,b,c), -1)`. -/
theorem triangle_area_invalid_returns_minus_one (a b c : i64)
    (h_ab : ¬ Int64.addOverflow a b)
    (h_ac : ¬ Int64.addOverflow a c)
    (h_bc : ¬ Int64.addOverflow b c)
    (h_invalid :
      (a + b).toInt ≤ c.toInt ∨
      (a + c).toInt ≤ b.toInt ∨
      (b + c).toInt ≤ a.toInt) :
    clever_070_triangle_area.triangle_area a b c = RustM.ok (-1 : i64) := by
  sorry

/-- Valid-triangle case (existence + non-negativity): when the sides are
    non-negative, the validity-check sums do not overflow, the triangle
    inequality holds strictly, and the full Heron product times `10000`
    fits in `i64`, the function returns some `r ≥ 0` (not the `-1`
    sentinel).

    Corresponds to the `then` branch of `invalid_iff_minus_one`:
    `if valid { prop_assert!(r >= 0); }`. -/
theorem triangle_area_valid_returns_nonneg (a b c : i64)
    (h_ab : ¬ Int64.addOverflow a b)
    (h_ac : ¬ Int64.addOverflow a c)
    (h_bc : ¬ Int64.addOverflow b c)
    (ha_pos : 0 ≤ a.toInt) (hb_pos : 0 ≤ b.toInt) (hc_pos : 0 ≤ c.toInt)
    (h_valid_ab : c.toInt < a.toInt + b.toInt)
    (h_valid_ac : b.toInt < a.toInt + c.toInt)
    (h_valid_bc : a.toInt < b.toInt + c.toInt)
    (h_heron_bound :
      (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
        (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt) * 10000
      < 2 ^ 63) :
    ∃ r : i64, clever_070_triangle_area.triangle_area a b c = RustM.ok r ∧
      0 ≤ r.toInt := by
  sorry

/-- Closed-form postcondition (valid branch).

    Let `s2 = (a+b+c)(b+c-a)(a-b+c)(a+b-c)`. In the valid branch the
    function returns `r = floor(sqrt(s2 * 10000)) / 4`, which equals
    `floor(sqrt(s2 * 625))` because `10000 = 16 * 625` and the integer
    square root commutes with division by a perfect square at the
    Int-floor level. This is captured here as the pair of bounds
    `r * r ≤ s2 * 625` and `s2 * 625 < (r + 1) * (r + 1)`, plus `0 ≤ r`.

    Corresponds to `matches_oracle`. The `±1` slack in the proptest is
    f64 rounding error on the *oracle*; the Rust function computes the
    exact integer floor. -/
theorem triangle_area_valid_formula (a b c : i64)
    (h_ab : ¬ Int64.addOverflow a b)
    (h_ac : ¬ Int64.addOverflow a c)
    (h_bc : ¬ Int64.addOverflow b c)
    (ha_pos : 0 ≤ a.toInt) (hb_pos : 0 ≤ b.toInt) (hc_pos : 0 ≤ c.toInt)
    (h_valid_ab : c.toInt < a.toInt + b.toInt)
    (h_valid_ac : b.toInt < a.toInt + c.toInt)
    (h_valid_bc : a.toInt < b.toInt + c.toInt)
    (h_heron_bound :
      (a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
        (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt) * 10000
      < 2 ^ 63) :
    ∃ r : i64, clever_070_triangle_area.triangle_area a b c = RustM.ok r ∧
      0 ≤ r.toInt ∧
      r.toInt * r.toInt ≤
        ((a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
          (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt)) * 625 ∧
      ((a.toInt + b.toInt + c.toInt) * (b.toInt + c.toInt - a.toInt) *
        (a.toInt - b.toInt + c.toInt) * (a.toInt + b.toInt - c.toInt)) * 625
        < (r.toInt + 1) * (r.toInt + 1) := by
  sorry

/-! ## Known cases (from `known_cases` test)

Four concrete value checks that pin specific input/output pairs. They
are corollaries of the general theorems above but exercise the explicit
code paths the proptests sample at. -/

/-- `triangle_area 3 4 5 = 600`. The 3-4-5 right triangle has true area
    `6.00`, encoded as `600`. -/
theorem triangle_area_3_4_5 :
    clever_070_triangle_area.triangle_area 3 4 5 = RustM.ok (600 : i64) := by
  sorry

/-- `triangle_area 6 8 10 = 2400`. The 6-8-10 right triangle (scaled
    3-4-5) has true area `24.00`, encoded as `2400`. -/
theorem triangle_area_6_8_10 :
    clever_070_triangle_area.triangle_area 6 8 10 = RustM.ok (2400 : i64) := by
  sorry

/-- `triangle_area 1 2 10 = -1`. Invalid triangle (1 + 2 < 10): far from
    the boundary. -/
theorem triangle_area_1_2_10 :
    clever_070_triangle_area.triangle_area 1 2 10 = RustM.ok (-1 : i64) := by
  sorry

/-- `triangle_area 1 2 3 = -1`. Degenerate triangle (1 + 2 = 3): the
    triangle inequality is non-strict, so the function correctly rejects
    it as invalid. Exercises the `a + b ≤ c` boundary of the validity
    check. -/
theorem triangle_area_1_2_3 :
    clever_070_triangle_area.triangle_area 1 2 3 = RustM.ok (-1 : i64) := by
  sorry

end Clever_070_triangle_areaObligations
