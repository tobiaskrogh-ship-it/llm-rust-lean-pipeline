-- Companion obligations file for the `little_endian_from_slice_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import little_endian_from_slice_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace Little_endian_from_slice_u64Obligations

/-! ## Specification oracle: `u64::to_le` on the little-endian extraction host.

The Rust contract is "each element is mapped through `u64::to_le`". On a
little-endian platform `u64::to_le` performs no byte swap — it is exactly
the identity — which is precisely why `byteorder` documents
`from_slice_u64` as "a no-op if the host platform is already little
endian". We keep `toLe` as a named oracle (rather than inlining `id`) so
the elementwise postcondition reads as a genuine specification, parallel
to the `byteRev64` oracle of the big-endian twin. -/
private def toLe (n : Nat) : Nat := n

/-- `from_slice_u64` collapses to the identity on the LE extraction host.
    `cfg!(target_endian = "big")` extracted to `if false`, so the
    `build_swapped` / `copy_from_slice` branch is dead code and the whole
    `do` block is `pure numbers`. This is the structural fact every
    obligation below reduces to. -/
private theorem from_slice_u64_eq_noop (numbers : RustSlice u64) :
    little_endian_from_slice_u64.from_slice_u64 numbers = RustM.ok numbers := by
  unfold little_endian_from_slice_u64.from_slice_u64
  simp only [Bool.false_eq_true, ↓reduceIte, bind_pure]
  rfl

/-! ## Obligations. -/

/-- Core functional postcondition, no-op form. On the little-endian
    extraction host `cfg!(target_endian = "big")` is `false`, so the
    `build_swapped` / `copy_from_slice` branch is dead code and
    `from_slice_u64` reduces to the identity. This is the concrete claim
    behind the `doctest_little_endian` doc-test (`numbers` is unchanged,
    since `to_le` is the identity on a LE host) and the mechanism the two
    `prop_postcondition_*` tests rely on. -/
theorem from_slice_u64_is_noop (numbers : RustSlice u64) :
    little_endian_from_slice_u64.from_slice_u64 numbers = RustM.ok numbers :=
  from_slice_u64_eq_noop numbers

/-- Totality / no-panic. `from_slice_u64` has no precondition and no
    panic/overflow path on the LE host. Captures the "must not panic"
    requirement exercised across all input lengths (including the
    explicitly enumerated empty-slice edge case) by
    `prop_postcondition_each_element_mapped_through_to_le`. -/
theorem from_slice_u64_total (numbers : RustSlice u64) :
    ∃ v : RustSlice u64,
      little_endian_from_slice_u64.from_slice_u64 numbers = RustM.ok v :=
  ⟨numbers, from_slice_u64_eq_noop numbers⟩

/-- Length-preservation postcondition. Captures the
    `assert_eq!(numbers.len(), original.len())` clause of
    `prop_postcondition_each_element_mapped_through_to_le`: the slice is
    returned with the same number of elements. -/
theorem from_slice_u64_preserves_length
    (numbers : RustSlice u64)
    (v : RustSlice u64)
    (hres : little_endian_from_slice_u64.from_slice_u64 numbers = RustM.ok v) :
    v.val.size = numbers.val.size := by
  rw [from_slice_u64_eq_noop numbers] at hres
  injection hres with h1
  injection h1 with h2
  rw [h2]

/-- Core elementwise postcondition. Captures the
    `assert_eq!(numbers[i], original[i].to_le())` clause of
    `prop_postcondition_each_element_mapped_through_to_le`,
    `prop_postcondition_boundary_values`, and `doctest_little_endian`:
    each output element equals the corresponding input element mapped
    through `to_le` (the identity on the LE host), taken at its own index
    (so no reordering and, with the length clause, no drops). -/
theorem from_slice_u64_elementwise_le
    (numbers : RustSlice u64)
    (v : RustSlice u64)
    (hres : little_endian_from_slice_u64.from_slice_u64 numbers = RustM.ok v)
    (j : Nat) (hj : j < v.val.size) (hj' : j < numbers.val.size) :
    (v.val[j]'hj).toNat = toLe (numbers.val[j]'hj').toNat := by
  have hv : v = numbers := by
    rw [from_slice_u64_eq_noop numbers] at hres
    injection hres with h1
    injection h1 with h2
    exact h2.symm
  subst hv
  simp only [toLe]

/-- Empty-slice edge case. Captures the `len = 0` case explicitly listed
    in `prop_postcondition_each_element_mapped_through_to_le`: on an empty
    input the function completes successfully and yields an empty slice. -/
theorem from_slice_u64_empty_noop
    (numbers : RustSlice u64)
    (hempty : numbers.val.size = 0) :
    ∃ v : RustSlice u64,
      little_endian_from_slice_u64.from_slice_u64 numbers = RustM.ok v ∧
      v.val.size = 0 :=
  ⟨numbers, from_slice_u64_eq_noop numbers, hempty⟩

end Little_endian_from_slice_u64Obligations
