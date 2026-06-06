-- Companion obligations file for the `clever_105_f` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import clever_105_f

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Clever_105_fObligations

/-! ## Specification helpers

Standard mathematical factorial used as the oracle for even positions. -/
private def factorial_nat : Nat → Nat
  | 0     => 1
  | k + 1 => (k + 1) * factorial_nat k

/-! ## Boundary clause -/

/-- `f 0` returns the empty `Vec`. Captures the `f(0) == vec![]` half of the
    `known` test in the Rust source. -/
theorem f_zero_empty :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_105_f.f (0 : u64) = RustM.ok v ∧ v.val.size = 0 := by
  sorry

/-! ## Totality in the proptest-bounded range -/

/-- For all `n ≤ 20`, `f n` terminates successfully. The bound matches the
    `0u64..=20` range used by every property test in the Rust source, which
    is itself bounded so that the largest factorial (`20!`) still fits in
    `u64` (`20! < 2^64 < 21!`). Outside this range the function panics on
    integer overflow when computing `i!` for the largest even index. -/
theorem f_total (n : u64) (h : n.toNat ≤ 20) :
    ∃ v : alloc.vec.Vec u64 alloc.alloc.Global,
      clever_105_f.f n = RustM.ok v := by
  sorry

/-! ## Length postcondition -/

/-- The returned vector has exactly `n` elements. Captures the property test
    `length_matches_n`. Stated as a consequence of `f n = ok v`: when `f n`
    fails (e.g. because of factorial overflow for `n ≥ 22`), the hypothesis
    is unsatisfiable and the conclusion is vacuous. -/
theorem f_length
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_105_f.f n = RustM.ok v) :
    v.val.size = n.toNat := by
  sorry

/-! ## Per-position postconditions -/

/-- Odd-index positions hold the triangular number `i * (i + 1) / 2`.
    Captures the property test `odd_positions_are_triangular`. The
    1-indexed Rust position `i` corresponds to the 0-indexed Lean position
    `i - 1`. Stated as a consequence of `f n = ok v` so that the failure
    range is handled vacuously. -/
theorem f_odd_position_triangular
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_105_f.f n = RustM.ok v)
    (i : Nat) (h_pos : 1 ≤ i) (h_le : i ≤ n.toNat) (h_odd : i % 2 = 1)
    (hi : i - 1 < v.val.size) :
    (v.val[i - 1]'hi).toNat = i * (i + 1) / 2 := by
  sorry

/-- Even-index positions hold the factorial `i!`. Captures the property
    test `even_positions_are_factorial`. The 1-indexed Rust position `i`
    corresponds to the 0-indexed Lean position `i - 1`. Stated as a
    consequence of `f n = ok v` so that the failure range is handled
    vacuously. -/
theorem f_even_position_factorial
    (n : u64) (v : alloc.vec.Vec u64 alloc.alloc.Global)
    (hres : clever_105_f.f n = RustM.ok v)
    (i : Nat) (h_pos : 1 ≤ i) (h_le : i ≤ n.toNat) (h_even : i % 2 = 0)
    (hi : i - 1 < v.val.size) :
    (v.val[i - 1]'hi).toNat = factorial_nat i := by
  sorry

end Clever_105_fObligations
