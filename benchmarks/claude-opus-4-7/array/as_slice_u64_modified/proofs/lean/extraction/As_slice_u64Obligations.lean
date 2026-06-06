-- Companion obligations file for the `as_slice_u64` extraction.
-- Each property the Rust function should satisfy belongs here as a separate `theorem`.
-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.

import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import as_slice_u64

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace As_slice_u64Obligations

open as_slice_u64

/-- The array-backed slice produced by `rust_primitives.unsize` has a
    size that fits in a `usize`. `a.toVec.toArray.size = N.toNat`
    (`Vector.size_toArray`) and `N : usize` is bounded by `USize64.size`,
    so the `Seq.size_lt_usizeSize` field is dischargeable for the slice
    that `as_slice` returns. Internal scaffolding shared by both
    obligations below. -/
private theorem toArray_size_lt {N : usize} (a : RustArray u64 N) :
    a.toVec.toArray.size < USize64.size := by
  rw [Vector.size_toArray]
  exact USize64.toNat_lt_size N

/-- Failure condition (none) / totality / no-panic.

    `as_slice` is the array→slice reborrow `(&[u64; N]) -> &[u64]` (Rust
    `&a[..]`). It is a `const fn` whose body is just `a`: a pure
    coercion that performs no fallible operation, so for every length `N`
    and every array `a` the call succeeds — it never panics, never
    overflows, never diverges.

    Every contract-style property test in the Rust source
    (`it_works`, `prop_returns_entire_array`, `prop_holds_for_each_size`)
    calls `as_slice(&a)` and then inspects the returned slice; each
    implicitly depends on this call returning a value rather than
    panicking. Unlike the degenerate `as_mut_slice` twin (whose
    extraction was `RustM sorry`), this extraction returns a concrete
    `RustM (RustSlice u64)`, so the no-panic clause is genuinely
    stateable here. -/
theorem as_slice_total (N : usize) (a : RustArray u64 N) :
    ∃ s : RustSlice u64, as_slice N a = RustM.ok s :=
  ⟨⟨a.toVec.toArray, toArray_size_lt a⟩, rfl⟩

/-- Postcondition (functional correctness): `as_slice` returns the
    *entire* array viewed as a slice. The underlying array of the
    returned slice is exactly the source array's elements, in order:
    `s.val = a.toVec.toArray`. This single equation simultaneously pins
    down the length (`s.val.size = N.toNat`), every element, and their
    order — `&a[..]` is the reference semantics for "the whole array as
    a slice".

    Captures the property tests `prop_returns_entire_array`
    (1000 random `[u64; 16]` arrays, `as_slice(&a) == &a[..]`) and
    `prop_holds_for_each_size` (the same contract across the distinct
    const-generic instantiations `N ∈ {0, 1, 2, 32}`, including the
    empty-array boundary `N = 0`). Because this theorem is universally
    quantified over `N` and `a`, the per-size test — and the concrete
    `it_works` sanity check (`[1,2,3]` and `[]`) — are instances of it.

    A buggy implementation that dropped, reordered, duplicated, or
    mutated any element, or returned a strict sub-range, would falsify
    this. -/
theorem as_slice_returns_entire_array (N : usize) (a : RustArray u64 N) :
    ∃ s : RustSlice u64, as_slice N a = RustM.ok s ∧ s.val = a.toVec.toArray :=
  ⟨⟨a.toVec.toArray, toArray_size_lt a⟩, rfl, rfl⟩

end As_slice_u64Obligations
