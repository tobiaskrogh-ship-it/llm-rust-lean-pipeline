-- Companion obligations file for the `sqrt_u64` extraction.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import sqrt_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Sqrt_u64Obligations

theorem sqrt_small_no_failure (x : u64) (h : x < 4) :
    ∃ v : u64, sqrt_u64.sqrt x = RustM.ok v := by
  unfold sqrt_u64.sqrt
  simp only [rust_primitives.cmp.lt, rust_primitives.cmp.gt, decide_eq_true_eq, pure_bind]
  trace_state
  sorry

end Sqrt_u64Obligations
