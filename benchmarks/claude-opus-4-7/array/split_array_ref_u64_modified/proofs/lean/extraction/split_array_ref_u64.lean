
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


namespace split_array_ref_u64

--  Returns an array reference to the first `M` items in the slice and the
--  remaining slice.
-- 
--  Panics if the slice is shorter than `M`.
@[spec]
def split_first_chunk (M : usize) (s : (RustSlice u64)) :
    RustM (rust_primitives.hax.Tuple2 (RustArray u64 M) (RustSlice u64)) := do
  let ⟨first, tail⟩ ← (core_models.slice.Impl.split_at u64 s M);
  (pure (rust_primitives.hax.Tuple2.mk
    (← (core_models.result.Impl.unwrap
      (RustArray u64 M)
      core_models.array.TryFromSliceError
      (← (core_models.convert.TryInto.try_into
        (RustSlice u64)
        (RustArray u64 M) first))))
    tail))

--  Divides one array reference into two at an index.
-- 
--  The first will contain all indices from `[0, M)` and the second will
--  contain all indices from `[M, N)`.
-- 
--  # Panics
-- 
--  Panics if `M > N`.
@[spec]
def split_array_ref (M : usize) (N : usize) (a : (RustArray u64 N)) :
    RustM (rust_primitives.hax.Tuple2 (RustArray u64 M) (RustSlice u64)) := do
  (split_first_chunk (M) (← (rust_primitives.unsize a)))

end split_array_ref_u64

