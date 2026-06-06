-- Companion obligations file for the `clever_091_any_int` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_091_any_int

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_091_any_intObligations

open clever_091_any_int

/-- Definitional unfolding for `+?` on `i64`. -/
private theorem hax_add_def_i64 (x y : i64) :
    x +? y = if Int64.addOverflow x y
             then RustM.fail Error.integerOverflow
             else pure (x + y) := rfl

/-- Definitional unfolding for `==?` on `i64`. -/
private theorem hax_eq_def_i64 (x y : i64) :
    x ==? y = pure (x == y) := rfl

/-- Definitional unfolding for `||?` on `Bool`. -/
private theorem hax_or_def (x y : Bool) :
    (x ||? y) = pure (x || y) := rfl

/-- Postcondition (no overflow): when none of the three signed `i64` additions
    `b + c`, `a + c`, `a + b` overflow, `any_int a b c` returns the boolean
    disjunction `(a == b + c) || (b == a + c) || (c == a + b)` successfully.

    Corresponds to the `defining` proptest in the Rust source:
    `prop_assert_eq!(any_int(a, b, c), a == b + c || b == a + c || c == a + b)`
    under `a, b, c ∈ [-50, 50]`. The proptest's bound is a hint that the natural
    universal statement requires no-overflow preconditions; in the Lean model
    we state the precondition explicitly (each `+?` overflow source) rather
    than mimic the test domain. The `known` test cases (e.g. `any_int(5,2,3)`,
    `any_int(-1,1,0)`) are subsumed by this functional postcondition. -/
theorem any_int_ok (a b c : i64)
    (h1 : ¬ Int64.addOverflow b c)
    (h2 : ¬ Int64.addOverflow a c)
    (h3 : ¬ Int64.addOverflow a b) :
    any_int a b c =
      RustM.ok ((a == b + c) || (b == a + c) || (c == a + b)) := by
  simp only [any_int, hax_add_def_i64, hax_eq_def_i64, hax_or_def,
             if_neg h1, if_neg h2, if_neg h3, bind_pure_comp, map_pure]
  rfl

/-- Failure (first addition `b + c` overflows): the function panics with
    `Error.integerOverflow`. This is the first `+?` evaluated in the
    monadic chain (`(← (b +? c))` appears innermost-leftmost), so an
    overflow here short-circuits before the other two additions are
    attempted. Encodes the Rust panic semantics on `i64` overflow that the
    proptest's bounded range silently avoids. -/
theorem any_int_overflow_bc (a b c : i64)
    (h : Int64.addOverflow b c) :
    any_int a b c = RustM.fail Error.integerOverflow := by
  simp only [any_int, hax_add_def_i64, if_pos h]
  rfl

/-- Failure (second addition `a + c` overflows): when `b + c` does not
    overflow but `a + c` does, the function panics with
    `Error.integerOverflow`. The `b + c` no-overflow hypothesis is needed
    so that the monadic chain reaches the second `+?`. -/
theorem any_int_overflow_ac (a b c : i64)
    (h1 : ¬ Int64.addOverflow b c)
    (h2 : Int64.addOverflow a c) :
    any_int a b c = RustM.fail Error.integerOverflow := by
  simp only [any_int, hax_add_def_i64, hax_eq_def_i64,
             if_neg h1, if_pos h2, pure_bind]
  rfl

/-- Failure (third addition `a + b` overflows): when neither `b + c` nor
    `a + c` overflows but `a + b` does, the function panics with
    `Error.integerOverflow`. The earlier no-overflow hypotheses are needed
    so that the monadic chain reaches the third `+?`. -/
theorem any_int_overflow_ab (a b c : i64)
    (h1 : ¬ Int64.addOverflow b c)
    (h2 : ¬ Int64.addOverflow a c)
    (h3 : Int64.addOverflow a b) :
    any_int a b c = RustM.fail Error.integerOverflow := by
  simp only [any_int, hax_add_def_i64, hax_eq_def_i64, hax_or_def,
             if_neg h1, if_neg h2, if_pos h3, pure_bind]
  rfl

end Clever_091_any_intObligations
