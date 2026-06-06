
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace clever_070_triangle_area

--  HumanEval/71 / CLEVER 070 — `triangle_area(a, b, c)`.  Return the area
--  of the triangle with sides `a`, `b`, `c`, rounded to two decimal
--  places, IF the sides form a valid triangle.  Otherwise return `-1`.
-- 
--  "Valid triangle" iff the sum of any two sides is strictly greater
--  than the third.
-- 
--  Integer adaptation: the canonical signature returns `i64`, so we
--  encode the "rounded to 2 decimal places" area as `floor(100 * area)`.
--  Heron's formula gives `16 * area² = (a+b+c)(b+c-a)(a-b+c)(a+b-c)`,
--  so `100 * area = floor(sqrt(s2 * 10000) / 4)` where
--  `s2 = (a+b+c)(b+c-a)(a-b+c)(a+b-c)`.
-- 
--  `isqrt` uses binary search on the recursion structure, so the
--  recursion depth is O(log n) — well inside any test-thread stack
--  limit even at the upper end of the test input range.
@[spec]
def isqrt_bin (n : i64) (lo : i64) (hi : i64) : RustM i64 := do
  if (← ((← (hi -? lo)) <=? (1 : i64))) then do
    (pure lo)
  else do
    let mid : i64 ← ((← (lo +? hi)) /? (2 : i64));
    if (← ((← (mid *? mid)) <=? n)) then do
      (isqrt_bin n mid hi)
    else do
      (isqrt_bin n lo mid)
partial_fixpoint

@[spec]
def isqrt (n : i64) : RustM i64 := do
  if (← (n <=? (0 : i64))) then do
    (pure (0 : i64))
  else do
    (isqrt_bin n (0 : i64) (3037000500 : i64))

@[spec]
def triangle_area (a : i64) (b : i64) (c : i64) : RustM i64 := do
  if
  (← ((← ((← ((← (a +? b)) <=? c)) ||? (← ((← (a +? c)) <=? b))))
    ||? (← ((← (b +? c)) <=? a)))) then do
    (pure (-1 : i64))
  else do
    let s2 : i64 ←
      ((← ((← ((← ((← (a +? b)) +? c)) *? (← ((← (b +? c)) -? a))))
          *? (← ((← (a -? b)) +? c))))
        *? (← ((← (a +? b)) -? c)));
    ((← (isqrt (← (s2 *? (10000 : i64))))) /? (4 : i64))

end clever_070_triangle_area

