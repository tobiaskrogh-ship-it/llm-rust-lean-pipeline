-- Companion obligations file for the `gcd_u64` extraction.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import gcd_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Gcd_u64Obligations

theorem gcd_zero_left (y : u64) :
    gcd_u64.gcd 0 y = RustM.ok y := by
  simp only [gcd_u64.gcd, rust_primitives.cmp.eq, rust_primitives.hax.logical_op.or,
             pure_bind, beq_self_eq_true, Bool.true_or, ↓reduceIte]
  show RustM.ok ((0 : u64) ||| y) = RustM.ok y
  congr 1
  bv_decide

theorem gcd_zero_right (x : u64) :
    gcd_u64.gcd x 0 = RustM.ok x := by
  simp only [gcd_u64.gcd, rust_primitives.cmp.eq, rust_primitives.hax.logical_op.or,
             pure_bind, beq_self_eq_true, Bool.or_true, ↓reduceIte]
  show RustM.ok (x ||| (0 : u64)) = RustM.ok x
  congr 1
  bv_decide

/-- Try totality via Hoare triple. -/
theorem gcd_triple_True (x y : u64) :
    ⦃ ⌜ True ⌝ ⦄ gcd_u64.gcd x y ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  hax_mvcgen [gcd_u64.gcd]

end Gcd_u64Obligations
